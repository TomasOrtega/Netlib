import Netlib.Check.CampusTCPTwoProgressPhaseBase

/-!
# Selected drops on the same indexed phase state

The resolved custody item defines the loss source.
Cause refinements retain that same drop and move.
-/

namespace Netlib.Check.CampusTCPTwoProgressPhaseDrop

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressPhaseBase
open CampusTCPTwoProgressSetup (config)

namespace M
export CampusTCPTwoProgressMonitor (Monitor DropTarget Allowed observe dropTarget observeDrop)
end M
namespace D
export CampusTCPRecoveryRoundDrop (Append Facts append)
end D
namespace L
export CampusTCPTwoProgressLossHistory (Loss Book Supports transitSource)
end L
namespace S
export CampusTCPTwoProgressSender (Stage)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {sent : S.Stage initial} {received : R.Stage} {actual : Step input}
variable {item : Theory.PacketCustody.Item (Transit input)} {target : M.DropTarget}

structure Selected (core : Core initial native quantum allowance current monitor sent received)
    (item : Theory.PacketCustody.Item (Transit input)) (target : M.DropTarget) (actual : Step input) where
  appended : D.Append current item.id actual
  selected : M.dropTarget (config initial native quantum allowance) current.report.final monitor item.id = some target
  allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event
  resolved : appended.facts.resolved.item = item

variable {core : Core initial native quantum allowance current monitor sent received}

def Selected.loss (selected : Selected core item target actual) : L.Loss initial (config initial native quantum allowance) :=
  core.losses.selectedLoss selected.appended.move selected.appended.facts selected.selected selected.allowed

theorem Selected.source_eq (selected : Selected core item target actual) :
    selected.loss.source = L.transitSource item.value.payload := by
  change L.transitSource selected.appended.facts.resolved.item.value.payload = _
  rw [selected.resolved]

theorem Selected.source_ingress (selected : Selected core item target actual)
    (payload : item.value.payload = .ingress index produced) : selected.loss.source = produced := by
  rw [selected.source_eq, payload]
  rfl

theorem Selected.source_link (selected : Selected core item target actual)
    (served : Served input) (emission : WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission)
    (payload : item.value.payload = .link index served emission emitted) :
    selected.loss.source = served.ticket.value.produced := by
  rw [selected.source_eq, payload]
  rfl

theorem Selected.observed (selected : Selected core item target actual) :
    M.observe (config initial native quantum allowance) monitor actual =
      M.observeDrop (config initial native quantum allowance) monitor actual item.id :=
  CampusTCPTwoProgressMonitorFacts.observe_drop _ _ _ selected.appended.move.supported selected.appended.move.passed
    (by simpa only [selected.appended.move.beforeEq] using selected.allowed) selected.appended.facts.event

theorem Selected.counters (selected : Selected core item target actual) :
    (M.observe (config initial native quantum allowance) monitor actual).retries = monitor.retries ∧
      (M.observe (config initial native quantum allowance) monitor actual).drops = monitor.drops ++ [item.id] := by
  rw [selected.observed]
  exact Prod.mk.inj (CampusTCPTwoProgressMonitorFacts.drop_counters _ _ _ item.id
    (by simpa only [selected.appended.move.beforeEq] using selected.selected))

theorem Selected.budget (selected : Selected core item target actual) : monitor.drops.length < allowance := by
  have chosen := selected.selected
  unfold M.dropTarget at chosen
  split at chosen
  · split at chosen
    · assumption
    · cases chosen
  · cases chosen

private def nextCore (selected : Selected core item target actual)
    (losses : CampusTCPTwoProgressLossHistory.History initial (config initial native quantum allowance)
      selected.appended.move.after (M.observe (config initial native quantum allowance) monitor actual)) :
    Core initial native quantum allowance selected.appended.move.after
      (M.observe (config initial native quantum allowance) monitor actual) sent received := by
  let flight : CampusTCPTwoProgressSender.Flight initial (endpoint selected.appended.move.after.endpoints sender) sent
      (M.observe (config initial native quantum allowance) monitor actual).retries := by
    rw [selected.appended.endpoints, selected.counters.1]
    exact core.live.senderFlight
  let receiver : CampusTCPTwoProgressReceiver.Facts initial
      (endpoint selected.appended.move.after.endpoints sender.other) received := by
    rw [selected.appended.endpoints]
    exact core.live.receiverFacts
  have environment : CampusTCPRoundEnvironment.environment current.report.final =
      CampusTCPRoundEnvironment.environment selected.appended.move.after.report.final := by
    rw [selected.appended.move.final, selected.appended.facts.environment]
  have gatewayFrame : beforeService input selected.appended.move.after.report.final gateway =
      beforeService input current.report.final gateway := by
    rw [selected.appended.move.final]
    exact selected.appended.facts.beforeService gateway
  let live : CampusTCPTwoProgressState.Live initial selected.appended.move.after sent
      (M.observe (config initial native quantum allowance) monitor actual).retries received := {
    anchor := ⟨CampusTCPTwoProgressState.endpoint_guards flight receiver,
      core.live.anchor.retained.trans selected.appended.move.retained, core.live.anchor.environment.trans environment⟩
    senderFlight := flight, receiverFacts := receiver
    gatewayState := core.live.gatewayState.reframe gatewayFrame
    gatewayWindow := core.live.gatewayWindow
    history := core.live.history.same (by rw [selected.appended.endpoints]) }
  have recovery : live.senderFlight.recovery = core.live.senderFlight.recovery := by
    apply Option.some.inj
    exact live.senderFlight.runtime.symm.trans (by rw [selected.appended.endpoints]; exact core.live.senderFlight.runtime)
  exact {
    live
    senderWindow := by rw [selected.appended.endpoints]; exact core.senderWindow
    originals := core.originals.retain_steps selected.appended.move.retained
    originalTimes := core.originalTimes
    writer := core.writer.same (by rw [selected.appended.endpoints])
    losses
    lossBound := by
      rw [selected.counters.2, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
      have budget := selected.budget
      omega
    retired := core.retired
    gatewayAck := core.gatewayAck
    covered := core.covered
    duplicates := recovery.symm ▸ core.duplicates
    deadline := recovery.symm ▸ core.deadline
    estimatorBeforeRetire := recovery.symm ▸ core.estimatorBeforeRetire
    rtoBeforeRetire := by rw [recovery, selected.counters.1]; exact core.rtoBeforeRetire
    rtoPending := by rw [recovery, selected.counters.1]; exact core.rtoPending
    emptyDuplicate := fun empty => recovery.symm ▸ core.emptyDuplicate empty }

structure Result (selected : Selected core item target actual)
    (book : L.Book initial (config initial native quantum allowance)) where
  next : Core initial native quantum allowance selected.appended.move.after
    (M.observe (config initial native quantum allowance) monitor actual) sent received
  bookEq : next.losses.book = book

def lowerBook (selected : Selected core item target actual) : L.Book initial (config initial native quantum allowance) :=
  { core.losses.book.appendLoss selected.loss with lower := some core.losses.book.losses.length }

def upperBook (selected : Selected core item target actual) : L.Book initial (config initial native quantum allowance) :=
  { core.losses.book.appendLoss selected.loss with upper := some core.losses.book.losses.length }

def Selected.unassigned (selected : Selected core item target actual) :
    Result selected (core.losses.book.appendLoss selected.loss) :=
  ⟨nextCore selected (core.losses.drop selected.appended.move selected.appended.facts selected.selected selected.allowed), rfl⟩

def Selected.credit_lower (selected : Selected core item target actual) (support : L.Supports selected.loss .lower) :
    Result selected (lowerBook selected) :=
  ⟨nextCore selected (core.losses.drop_lower selected.appended.move selected.appended.facts selected.selected selected.allowed support), rfl⟩

def Selected.credit_upper (selected : Selected core item target actual) (support : L.Supports selected.loss .upper) :
    Result selected (upperBook selected) :=
  ⟨nextCore selected (core.losses.drop_upper selected.appended.move selected.appended.facts selected.selected selected.allowed support), rfl⟩

theorem drop_at (core : Core initial native quantum allowance current monitor sent received)
    (item : Theory.PacketCustody.Item (Transit input)) (member : item ∈ current.report.final.custody.pending)
    (chosen : M.dropTarget (config initial native quantum allowance) current.report.final monitor item.id = some target)
    (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor (.dropPacket item.id)) :
    ∃ actual : Step input, ∃ selected : Selected core item target actual,
      Nonempty (Result selected (core.losses.book.appendLoss selected.loss)) := by
  obtain ⟨actual, ⟨appended⟩⟩ := D.append current item member
  let selected : Selected core item target actual := {
    appended, selected := chosen, allowed := by rw [appended.facts.event]; exact allowed
    resolved := appended.facts.resolved.item_eq (CampusTCPCustodyFacts.Report.valid current.report) item member rfl }
  exact ⟨actual, selected, ⟨selected.unassigned⟩⟩

theorem Step.selected_drop (actual : Step input) (core : Core initial native quantum allowance current monitor sent received)
    (item : Theory.PacketCustody.Item (Transit input)) (member : item ∈ current.report.final.custody.pending)
    (chosen : M.dropTarget (config initial native quantum allowance) current.report.final monitor item.id = some target)
    (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor (.dropPacket item.id))
    (before : actual.before = current.report.final) (event : actual.event = .dropPacket item.id) :
    ∃ selected : Selected core item target actual, Nonempty (Result selected (core.losses.book.appendLoss selected.loss)) := by
  obtain ⟨enabled, selected, result⟩ := drop_at core item member chosen allowed
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (selected.appended.move.beforeEq.trans before.symm) (selected.appended.facts.event.trans event.symm)
  subst actual
  exact ⟨selected, result⟩

end Netlib.Check.CampusTCPTwoProgressPhaseDrop
