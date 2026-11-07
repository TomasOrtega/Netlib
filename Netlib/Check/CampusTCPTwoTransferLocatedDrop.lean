import Netlib.Check.CampusTCPTwoTransferDropObserve
import Netlib.Check.CampusTCPTwoTransferLocatedCore
import Netlib.Check.CampusTCPTwoProgressPathsFrames
import Netlib.Check.CampusTCPTwoTransferPreparationState

namespace Netlib.Check.CampusTCPTwoTransferLocatedDrop

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)

namespace W
export CampusTCPTwoTransferMonitor (Allowed observe)
end W
namespace M
export CampusTCPTwoProgressMonitor (DropTarget dropTarget observeDrop exposedPacket)
end M
namespace D
export CampusTCPRecoveryRoundDrop (Append Facts append)
end D
namespace L
export CampusTCPTwoTransferLoss (Loss Book Supports transitSource)
end L
namespace Q
export CampusTCPTwoTransferQueue (Closed TicketAt)
end Q
namespace P
export CampusTCPTwoProgressPaths (Ingress Link DataIngress DataLink AckIngress AckLink)
end P

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender actor : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : CampusTCPTwoTransferMonitor.Monitor}
variable {sent : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
variable {actual : Step input} {item : Theory.PacketCustody.Item (Transit input)} {target : M.DropTarget}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

structure Selected (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (item : Theory.PacketCustody.Item (Transit input)) (target : M.DropTarget) (actual : Step input) where
  appended : D.Append current item.id actual
  phase : monitor.exchange.mode = .forward
  selected : M.dropTarget ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward item.id = some target
  allowed : W.Allowed cfg current.report.final monitor actual.event
  resolved : appended.facts.resolved.item = item

variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}

def Selected.loss (selected : Selected core item target actual) : L.Loss initial cfg :=
  core.losses.selectedLoss selected.appended.move selected.appended.facts selected.phase selected.selected selected.allowed

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
    (payload : item.value.payload = .link index served emission emitted) : selected.loss.source = served.ticket.value.produced := by
  rw [selected.source_eq, payload]
  rfl

theorem sender_runtime (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received) :
    CampusTCPGapProgressMonitor.senderRecovery ((cfg).at current.report.final).forward.toConfig current.report.final =
      some core.live.senderFlight.recovery := by
  simp only [CampusTCPGapProgressMonitor.senderRecovery, current.connection, config,
    CampusTCPTwoTransferNative.Checks.monitorConfig, CampusTCPTwoTransferMonitor.Config.at,
    CampusTCPTwoExchangeSetup.config, CampusTCPTwoProgressSetup.config, core.live.senderFlight.runtime]

theorem Selected.observed (selected : Selected core item target actual) :
    W.observe cfg monitor actual = CampusTCPTwoTransferDropObserve.afterDrop cfg monitor actual item.id :=
  CampusTCPTwoTransferDropObserve.observe_drop selected.appended.facts selected.phase
    (by rw [← selected.appended.facts.event]; exact selected.allowed) selected.selected (sender_runtime core)

theorem Selected.frame (selected : Selected core item target actual) :
    CampusTCPTwoTransferLossHistory.DropFrame cfg monitor actual item.id :=
  CampusTCPTwoTransferDropObserve.counters selected.appended.facts selected.phase
    (by rw [← selected.appended.facts.event]; exact selected.allowed) selected.selected (sender_runtime core)

theorem Selected.healthy (selected : Selected core item target actual) : (W.observe cfg monitor actual).mode ≠ .invalid :=
  CampusTCPTwoTransferDropObserve.healthy selected.appended.facts selected.phase
    (by rw [← selected.appended.facts.event]; exact selected.allowed) selected.selected (sender_runtime core)

theorem Selected.budget (selected : Selected core item target actual) : monitor.exchange.forward.drops.length < allowance := by
  have chosen := selected.selected
  unfold M.dropTarget at chosen
  split at chosen
  · split at chosen
    · assumption
    · cases chosen
  · cases chosen

def rawDrop (value : CampusTCPTwoProgressMonitor.Monitor) (id : Nat) : M.DropTarget → CampusTCPTwoProgressMonitor.Monitor
  | .lower => { value with drops := value.drops ++ [id], lower := { value.lower with phase := .done } }
  | .upper => { value with drops := value.drops ++ [id], upper := { value.upper with phase := .done } }
  | .retry => { value with drops := value.drops ++ [id], retry := { value.retry with phase := .done } }
  | .ack => { value with drops := value.drops ++ [id], ack := none }

theorem Selected.local_observed (selected : Selected core item target actual) :
    (W.observe cfg monitor actual).exchange.forward = CampusTCPTwoProgressMonitor.normalize
      ((cfg).at current.report.final).forward selected.appended.move.after.report.final
      (rawDrop monitor.exchange.forward item.id target) := by
  rw [selected.observed]
  change M.observeDrop ((cfg).at actual.before).forward monitor.exchange.forward actual item.id = _
  rw [M.observeDrop, selected.appended.move.beforeEq, selected.selected, selected.appended.move.final]
  cases target <;> rfl

private theorem exposed_ticket (config : CampusTCPTwoProgressMonitor.Config) (state : State input)
    (lane : CampusTCPTwoProgressMonitor.Lane) (phase : lane.phase = .dataTicket) :
    M.exposedPacket config state lane = none := by
  unfold M.exposedPacket
  cases action : CampusTCPGapProgressMonitor.nextAction config.toConfig state lane.toGap <;>
    simp only [bind, Option.bind, CampusTCPGapProgressMonitor.packetAt,
      CampusTCPTwoProgressMonitor.Lane.toGap, phase]

private theorem lower_not_ticket {packetConfig : CampusTCPTwoProgressMonitor.Config}
    {state : State input} {value : CampusTCPTwoProgressMonitor.Monitor} {id : Nat}
    (chosen : M.dropTarget packetConfig state value id = some .lower) : value.lower.phase ≠ .dataTicket := by
  intro phase
  have none := exposed_ticket packetConfig state value.lower phase
  unfold M.dropTarget at chosen
  simp only [none] at chosen
  repeat' split at chosen
  all_goals cases chosen
  all_goals simp_all only [beq_iff_eq, reduceCtorEq]

private theorem upper_not_ticket {packetConfig : CampusTCPTwoProgressMonitor.Config}
    {state : State input} {value : CampusTCPTwoProgressMonitor.Monitor} {id : Nat}
    (chosen : M.dropTarget packetConfig state value id = some .upper) : value.upper.phase ≠ .dataTicket := by
  intro phase
  have none := exposed_ticket packetConfig state value.upper phase
  unfold M.dropTarget at chosen
  simp only [none] at chosen
  repeat' split at chosen
  all_goals cases chosen
  all_goals simp_all only [beq_iff_eq, reduceCtorEq]

private theorem queue_normalize {packetConfig : CampusTCPTwoProgressMonitor.Config}
    {state : State input} {value : CampusTCPTwoProgressMonitor.Monitor} (closed : Q.Closed state value) :
    Q.Closed state (CampusTCPTwoProgressMonitor.normalize packetConfig state value) := by
  have lanes := CampusTCPTwoProgressMonitorFacts.normalize_lanes packetConfig state value
  intro item member primary
  simpa only [Q.TicketAt, lanes.1, lanes.2.1] using closed item member primary

private theorem queue_drop (selected : Selected core item target actual) :
    Q.Closed selected.appended.move.after.report.final (W.observe cfg monitor actual).exchange.forward := by
  have old : Q.Closed selected.appended.move.after.report.final monitor.exchange.forward :=
    core.primaryQueue.work_same (by rw [selected.appended.move.final]; exact selected.appended.facts.work)
  rw [selected.observed]
  change Q.Closed _ (M.observeDrop ((cfg).at actual.before).forward monitor.exchange.forward actual item.id)
  rw [M.observeDrop, selected.appended.move.beforeEq, selected.selected, ← selected.appended.move.final]
  cases target <;> dsimp (config := { zetaHave := true }) only
  all_goals
    apply queue_normalize
    intro pending member primary
    rcases old pending member primary with lower | upper
    all_goals first
      | exact False.elim (lower_not_ticket selected.selected lower.1)
      | exact False.elim (upper_not_ticket selected.selected upper.1)
      | exact Or.inl lower
      | exact Or.inr upper

private def nextCore (selected : Selected core item target actual)
    (losses : CampusTCPTwoTransferLossHistory.History initial cfg selected.appended.move.after (W.observe cfg monitor actual)) :
    Core initial checks routing quantum allowance reverseLower reverseUpper selected.appended.move.after
      (W.observe cfg monitor actual) location sent received := by
  have gatewayFrame (location) : beforeService input selected.appended.move.after.report.final location =
      beforeService input current.report.final location := by
    rw [selected.appended.move.final]
    exact selected.appended.facts.beforeService location
  let previous := core.live.reindex selected.appended.move.retained
    (fun location => (congrArg CampusTCPService.Before.environment (gatewayFrame location)).symm)
    (fun actor => congrArg (fun endpoints => endpoint endpoints actor) selected.appended.endpoints)
    (congrArg (fun endpoints => applicationSteps endpoints sender.other) selected.appended.endpoints)
    (target := location) (by
      rw [selected.appended.move.final, selected.appended.facts.final]
      cases location <;> rfl)
  let live : CampusTCPTwoTransferState.LiveAt initial selected.appended.move.after location sent
      (W.observe cfg monitor actual).exchange.forward.retries received := {
    anchor := previous.anchor
    senderFlight := by rw [selected.frame.retries]; exact previous.senderFlight
    receiverFacts := previous.receiverFacts
    gatewayState := previous.gatewayState
    gatewayWindow := previous.gatewayWindow
    history := previous.history }
  have recovery : live.senderFlight.recovery = core.live.senderFlight.recovery := by
    exact Option.some.inj (live.senderFlight.runtime.symm.trans
      (by rw [selected.appended.endpoints]; exact core.live.senderFlight.runtime))
  exact {
    live
    senderWindow := by rw [selected.appended.endpoints]; exact core.senderWindow
    originals := core.originals.retain_steps selected.appended.move.retained
    originalTimes := core.originalTimes
    writer := core.writer.same (by rw [selected.appended.endpoints])
    losses
    lossBound := by
      rw [selected.frame.dropIDs, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
      exact selected.budget
    primaryQueue := queue_drop selected
    retired := core.retired
    gatewayAck := core.gatewayAck
    peerSettled := core.peerSettled
    peerWindow := core.peerWindow
    covered := core.covered
    duplicates := recovery.symm ▸ core.duplicates
    emptyDuplicate := recovery.symm ▸ core.emptyDuplicate
    deadline := recovery.symm ▸ core.deadline
    estimatorBeforeRetire := recovery.symm ▸ core.estimatorBeforeRetire
    rtoBeforeRetire := by rw [recovery, selected.frame.retries]; exact core.rtoBeforeRetire
    rtoPending := by rw [recovery, selected.frame.retries]; exact core.rtoPending }

structure Result (selected : Selected core item target actual) (book : L.Book initial cfg) where
  next : Core initial checks routing quantum allowance reverseLower reverseUpper selected.appended.move.after
    (W.observe cfg monitor actual) location sent received
  bookEq : next.losses.book = book

variable {selected : Selected core item target actual}

theorem Result.sender_recovery {nextBook : L.Book initial cfg} (value : Result selected nextBook) :
    value.next.live.senderFlight.recovery = core.live.senderFlight.recovery := by
  exact Option.some.inj (value.next.live.senderFlight.runtime.symm.trans
    (by rw [selected.appended.endpoints]; exact core.live.senderFlight.runtime))

theorem Result.receiver_reaction {nextBook : L.Book initial cfg} (value : Result selected nextBook) :
    value.next.live.receiverFacts.reaction = core.live.receiverFacts.reaction := by
  exact Option.some.inj (value.next.live.receiverFacts.ackRuntime.symm.trans
    (by rw [selected.appended.endpoints]; exact core.live.receiverFacts.ackRuntime))

theorem Result.session {nextBook : L.Book initial cfg} (value : Result selected nextBook) :
    value.next.live.gatewayState.gateway.session = core.live.gatewayState.gateway.session := by
  have phase := value.next.live.gatewayState.gateway.phase
  rw [selected.appended.move.final, selected.appended.facts.beforeService location,
    core.live.gatewayState.gateway.phase] at phase
  exact (Admission.Phase.data.inj phase).symm

theorem Result.range {nextBook : L.Book initial cfg} (value : Result selected nextBook) (part : CampusTCPTwoProgressSender.Part) :
    CampusTCPTwoTransferAdmission.rangeAt value.next.live.gatewayState part =
      CampusTCPTwoTransferAdmission.rangeAt core.live.gatewayState part := by
  have ranges := value.next.live.gatewayState.ranges.unique core.live.gatewayState.ranges initial.lowerNonempty
    (by rw [value.session])
  cases part
  · exact ranges.1
  · exact ranges.2

theorem Result.suffix {nextBook : L.Book initial cfg} (value : Result selected nextBook) : value.next.losses.suffix = core.losses.suffix ++ [actual] := by
  have history := value.next.losses.steps
  rw [selected.appended.move.history, core.losses.steps, List.append_assoc] at history
  exact (List.append_cancel_left history).symm

def lowerBook (selected : Selected core item target actual) : L.Book initial cfg :=
  { core.losses.book.appendLoss selected.loss with lower := some core.losses.book.losses.length }

def upperBook (selected : Selected core item target actual) : L.Book initial cfg :=
  { core.losses.book.appendLoss selected.loss with upper := some core.losses.book.losses.length }

def Selected.unassigned (selected : Selected core item target actual) :
    Result selected (core.losses.book.appendLoss selected.loss) :=
  ⟨nextCore selected (core.losses.drop selected.appended.move selected.appended.facts selected.phase selected.selected selected.allowed selected.frame), rfl⟩

def Selected.credit_lower (selected : Selected core item target actual) (support : L.Supports selected.loss .lower) :
    Result selected (lowerBook selected) :=
  ⟨nextCore selected (core.losses.drop_lower selected.appended.move selected.appended.facts selected.phase selected.selected
    selected.allowed selected.frame support), rfl⟩

def Selected.credit_upper (selected : Selected core item target actual) (support : L.Supports selected.loss .upper) :
    Result selected (upperBook selected) :=
  ⟨nextCore selected (core.losses.drop_upper selected.appended.move selected.appended.facts selected.phase selected.selected
    selected.allowed selected.frame support), rfl⟩

theorem drop_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (phase : monitor.exchange.mode = .forward)
    (item : Theory.PacketCustody.Item (Transit input)) (member : item ∈ current.report.final.custody.pending)
    (chosen : M.dropTarget ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward item.id = some target)
    (allowed : W.Allowed cfg current.report.final monitor (.dropPacket item.id)) :
    ∃ actual, ∃ selected : Selected core item target actual, Nonempty (Result selected (core.losses.book.appendLoss selected.loss)) := by
  obtain ⟨actual, ⟨appended⟩⟩ := D.append current item member
  let selected : Selected core item target actual := {
    appended, phase, selected := chosen, allowed := by rw [appended.facts.event]; exact allowed
    resolved := appended.facts.resolved.item_eq (CampusTCPCustodyFacts.Report.valid current.report) item member rfl }
  exact ⟨actual, selected, ⟨selected.unassigned⟩⟩

theorem Step.selected_drop (actual : Step input)
    (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (phase : monitor.exchange.mode = .forward)
    (item : Theory.PacketCustody.Item (Transit input)) (member : item ∈ current.report.final.custody.pending)
    (chosen : M.dropTarget ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward item.id = some target)
    (allowed : W.Allowed cfg current.report.final monitor (.dropPacket item.id))
    (before : actual.before = current.report.final) (event : actual.event = .dropPacket item.id) :
    ∃ selected : Selected core item target actual, Nonempty (Result selected (core.losses.book.appendLoss selected.loss)) := by
  obtain ⟨enabled, selected, result⟩ := drop_at core phase item member chosen allowed
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (selected.appended.move.beforeEq.trans before.symm) (selected.appended.facts.event.trans event.symm)
  subst actual
  exact ⟨selected, result⟩

variable {fields : Produced input.active input.passive → Prop} {header : Header}
variable {part : CampusTCPTwoProgressSender.Part} {lane : CampusTCPTwoProgressMonitor.Lane} {count packetID : Nat}
variable {produced : Produced input.active input.passive}

structure Dropped (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (produced : Produced input.active input.passive) (packetID : Nat) (target : M.DropTarget) (actual : Step input) where
  item : Theory.PacketCustody.Item (Transit input)
  identity : item.id = packetID
  selected : Selected core item target actual
  sourceEq : selected.loss.source = produced
  unassigned : Result selected (core.losses.book.appendLoss selected.loss)

theorem Dropped.event (drop : Dropped core produced packetID target actual) : actual.event = .dropPacket packetID :=
  drop.selected.appended.facts.event.trans (congrArg Event.dropPacket drop.identity)

def originalTarget : CampusTCPTwoProgressSender.Part → M.DropTarget
  | .lower => .lower
  | .upper => .upper

def creditBook (selected : Selected core item target actual) : CampusTCPTwoProgressSender.Part → L.Book initial cfg
  | .lower => lowerBook selected
  | .upper => upperBook selected

structure Credited (drop : Dropped core produced packetID target actual) (part : CampusTCPTwoProgressSender.Part) where
  support : L.Supports drop.selected.loss part
  result : Result drop.selected (creditBook drop.selected part)

private def credited (drop : Dropped core produced packetID target actual) (support : L.Supports drop.selected.loss part) :
    Credited drop part := by
  refine ⟨support, ?_⟩
  cases part
  · exact drop.selected.credit_lower support
  · exact drop.selected.credit_upper support

theorem ingress_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (phase : monitor.exchange.mode = .forward) (path : P.Ingress current actor fields)
    (chosen : M.dropTarget ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward path.packetID = some target)
    (allowed : W.Allowed cfg current.report.final monitor (.dropPacket path.packetID)) :
    ∃ actual, Nonempty (Dropped core path.output.produced path.packetID target actual) := by
  obtain ⟨item, member, id, payload⟩ := path.custody_item
  have selected : M.dropTarget ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward item.id = some target := by
    rw [id]
    exact chosen
  obtain ⟨actual, selected, ⟨result⟩⟩ := drop_at core phase item member selected (by rw [id]; exact allowed)
  exact ⟨actual, ⟨⟨item, id, selected, selected.source_ingress payload, result⟩⟩⟩

theorem link_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (phase : monitor.exchange.mode = .forward) (path : P.Link current actor fields header)
    (chosen : M.dropTarget ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward path.packetID = some target)
    (allowed : W.Allowed cfg current.report.final monitor (.dropPacket path.packetID)) :
    ∃ actual, Nonempty (Dropped core path.served.ticket.value.produced path.packetID target actual) := by
  obtain ⟨item, member, id, payload⟩ := path.custody_item
  have selected : M.dropTarget ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward item.id = some target := by
    rw [id]
    exact chosen
  obtain ⟨actual, selected, ⟨result⟩⟩ := drop_at core phase item member selected (by rw [id]; exact allowed)
  exact ⟨actual, ⟨⟨item, id, selected, selected.source_link path.served path.emission path.emitted payload, result⟩⟩⟩

theorem Step.ingress_drop (actual : Step input)
    (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (phase : monitor.exchange.mode = .forward) (path : P.Ingress current actor fields)
    (chosen : M.dropTarget ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward path.packetID = some target)
    (allowed : W.Allowed cfg current.report.final monitor (.dropPacket path.packetID))
    (before : actual.before = current.report.final) (event : actual.event = .dropPacket path.packetID) :
    Nonempty (Dropped core path.output.produced path.packetID target actual) := by
  obtain ⟨item, member, id, payload⟩ := path.custody_item
  obtain ⟨selected, ⟨result⟩⟩ := Step.selected_drop actual core phase item member
    (by rw [id]; exact chosen) (by rw [id]; exact allowed) before (by rw [id]; exact event)
  exact ⟨⟨item, id, selected, selected.source_ingress payload, result⟩⟩

theorem Step.link_drop (actual : Step input)
    (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (phase : monitor.exchange.mode = .forward) (path : P.Link current actor fields header)
    (chosen : M.dropTarget ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward path.packetID = some target)
    (allowed : W.Allowed cfg current.report.final monitor (.dropPacket path.packetID))
    (before : actual.before = current.report.final) (event : actual.event = .dropPacket path.packetID) :
    Nonempty (Dropped core path.served.ticket.value.produced path.packetID target actual) := by
  obtain ⟨item, member, id, payload⟩ := path.custody_item
  obtain ⟨selected, ⟨result⟩⟩ := Step.selected_drop actual core phase item member
    (by rw [id]; exact chosen) (by rw [id]; exact allowed) before (by rw [id]; exact event)
  exact ⟨⟨item, id, selected, selected.source_link path.served path.emission path.emitted payload, result⟩⟩

def Dropped.credit_original (drop : Dropped core produced packetID (originalTarget part) actual)
    (actor : produced.actor = sender)
    (fields : CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper) produced) :
    Credited drop part := by
  apply credited drop
  cases part
  · apply CampusTCPTwoTransferLoss.Supports.lower rfl
    · rw [drop.sourceEq]; exact actor
    · rw [drop.sourceEq]; exact fields
  · apply CampusTCPTwoTransferLoss.Supports.upper rfl
    · rw [drop.sourceEq]; exact actor
    · rw [drop.sourceEq]; exact fields

def Dropped.credit_retry (drop : Dropped core produced packetID .retry actual)
    (head : CampusTCPTwoProgressLossHistory.Head initial current part) (actor : produced.actor = sender)
    (fields : CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper) produced) :
    Credited drop part := by
  apply credited drop
  apply CampusTCPTwoTransferLoss.Supports.retry part rfl head
  · rw [drop.sourceEq]; exact actor
  · rw [drop.sourceEq]; exact fields

def Dropped.credit_ack (drop : Dropped core produced packetID .ack actual)
    (head : CampusTCPTwoProgressLossHistory.Head initial current part) (actor : produced.actor = sender.other)
    (fields : CampusTCPTwoProgressWire.AckFields initial count produced) (within : count ≤ lower.length + upper.length)
    (covered : part.offset lower + (part.bytes lower upper).length ≤ count) : Credited drop part := by
  apply credited drop
  apply CampusTCPTwoTransferLoss.Supports.ack part rfl head count
  · rw [drop.sourceEq]; exact actor
  · rw [drop.sourceEq]; exact fields
  · exact within
  · exact covered

theorem Dropped.gap_ack (drop : Dropped core produced packetID .ack actual)
    (fields : CampusTCPTwoProgressWire.AckFields initial 0 produced) (part : CampusTCPTwoProgressSender.Part) :
    ¬L.Supports drop.selected.loss part :=
  CampusTCPTwoTransferLoss.Supports.no_gap_ack rfl (by rw [drop.sourceEq]; exact fields)

theorem original_ingress_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (phase : monitor.exchange.mode = .forward) (path : P.DataIngress initial current part lane)
    (chosen : M.dropTarget ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward path.packetID = some (originalTarget part))
    (allowed : W.Allowed cfg current.report.final monitor (.dropPacket path.packetID)) :
    ∃ actual, ∃ drop : Dropped core path.output.produced path.packetID (originalTarget part) actual, Nonempty (Credited drop part) := by
  obtain ⟨actual, ⟨drop⟩⟩ := ingress_at core phase path.toIngress chosen allowed
  exact ⟨actual, drop, ⟨drop.credit_original path.output.actor path.output.fields⟩⟩

theorem original_link_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (phase : monitor.exchange.mode = .forward) (path : P.DataLink initial current part lane)
    (chosen : M.dropTarget ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward path.packetID = some (originalTarget part))
    (allowed : W.Allowed cfg current.report.final monitor (.dropPacket path.packetID)) :
    ∃ actual, ∃ drop : Dropped core path.served.ticket.value.produced path.packetID (originalTarget part) actual, Nonempty (Credited drop part) := by
  obtain ⟨actual, ⟨drop⟩⟩ := link_at core phase path.toLink chosen allowed
  exact ⟨actual, drop, ⟨drop.credit_original path.actor path.fields⟩⟩

theorem retry_ingress_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (phase : monitor.exchange.mode = .forward) (path : P.DataIngress initial current part lane)
    (head : CampusTCPTwoProgressLossHistory.Head initial current part)
    (chosen : M.dropTarget ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward path.packetID = some .retry)
    (allowed : W.Allowed cfg current.report.final monitor (.dropPacket path.packetID)) :
    ∃ actual, ∃ drop : Dropped core path.output.produced path.packetID .retry actual, Nonempty (Credited drop part) := by
  obtain ⟨actual, ⟨drop⟩⟩ := ingress_at core phase path.toIngress chosen allowed
  exact ⟨actual, drop, ⟨drop.credit_retry head path.output.actor path.output.fields⟩⟩

theorem retry_link_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (phase : monitor.exchange.mode = .forward) (path : P.DataLink initial current part lane)
    (head : CampusTCPTwoProgressLossHistory.Head initial current part)
    (chosen : M.dropTarget ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward path.packetID = some .retry)
    (allowed : W.Allowed cfg current.report.final monitor (.dropPacket path.packetID)) :
    ∃ actual, ∃ drop : Dropped core path.served.ticket.value.produced path.packetID .retry actual, Nonempty (Credited drop part) := by
  obtain ⟨actual, ⟨drop⟩⟩ := link_at core phase path.toLink chosen allowed
  exact ⟨actual, drop, ⟨drop.credit_retry head path.actor path.fields⟩⟩

theorem ack_ingress_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (phase : monitor.exchange.mode = .forward) (path : P.AckIngress initial current count lane)
    (head : CampusTCPTwoProgressLossHistory.Head initial current part) (within : count ≤ lower.length + upper.length)
    (covered : part.offset lower + (part.bytes lower upper).length ≤ count)
    (chosen : M.dropTarget ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward path.packetID = some .ack)
    (allowed : W.Allowed cfg current.report.final monitor (.dropPacket path.packetID)) :
    ∃ actual, ∃ drop : Dropped core path.output.produced path.packetID .ack actual, Nonempty (Credited drop part) := by
  obtain ⟨actual, ⟨drop⟩⟩ := ingress_at core phase path.toIngress chosen allowed
  exact ⟨actual, drop, ⟨drop.credit_ack head path.output.actor path.output.fields within covered⟩⟩

theorem ack_link_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (phase : monitor.exchange.mode = .forward) (path : P.AckLink initial current count lane)
    (head : CampusTCPTwoProgressLossHistory.Head initial current part) (within : count ≤ lower.length + upper.length)
    (covered : part.offset lower + (part.bytes lower upper).length ≤ count)
    (chosen : M.dropTarget ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward path.packetID = some .ack)
    (allowed : W.Allowed cfg current.report.final monitor (.dropPacket path.packetID)) :
    ∃ actual, ∃ drop : Dropped core path.served.ticket.value.produced path.packetID .ack actual, Nonempty (Credited drop part) := by
  obtain ⟨actual, ⟨drop⟩⟩ := link_at core phase path.toLink chosen allowed
  exact ⟨actual, drop, ⟨drop.credit_ack head path.actor path.fields within covered⟩⟩

theorem gap_ack_ingress_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (phase : monitor.exchange.mode = .forward) (path : P.AckIngress initial current 0 lane)
    (chosen : M.dropTarget ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward path.packetID = some .ack)
    (allowed : W.Allowed cfg current.report.final monitor (.dropPacket path.packetID)) :
    ∃ actual, ∃ drop : Dropped core path.output.produced path.packetID .ack actual, ∀ part, ¬L.Supports drop.selected.loss part := by
  obtain ⟨actual, ⟨drop⟩⟩ := ingress_at core phase path.toIngress chosen allowed
  exact ⟨actual, drop, drop.gap_ack path.output.fields⟩

theorem gap_ack_link_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (phase : monitor.exchange.mode = .forward) (path : P.AckLink initial current 0 lane)
    (chosen : M.dropTarget ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward path.packetID = some .ack)
    (allowed : W.Allowed cfg current.report.final monitor (.dropPacket path.packetID)) :
    ∃ actual, ∃ drop : Dropped core path.served.ticket.value.produced path.packetID .ack actual, ∀ part, ¬L.Supports drop.selected.loss part := by
  obtain ⟨actual, ⟨drop⟩⟩ := link_at core phase path.toLink chosen allowed
  exact ⟨actual, drop, drop.gap_ack path.fields⟩

end Netlib.Check.CampusTCPTwoTransferLocatedDrop

namespace Netlib.Check.CampusTCPTwoTransferPreparationState

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)

namespace D
export CampusTCPTwoTransferLocatedDrop (Selected Dropped lowerBook)
end D
namespace M
export CampusTCPTwoProgressMonitor (dropTarget exposedPacket observeDrop normalize)
end M
namespace W
export CampusTCPTwoTransferMonitor (Allowed observe)
end W

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : CampusTCPTwoTransferMonitor.Monitor} {actual : Step input} {id : Nat}
variable {first : CampusTCPTwoProgressSender.Original initial .lower}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

def lowerAfter (monitor : CampusTCPTwoTransferMonitor.Monitor) (id : Nat) : CampusTCPTwoTransferMonitor.Monitor :=
  { monitor with exchange := { monitor.exchange with
    forward := { monitor.exchange.forward with
      drops := monitor.exchange.forward.drops ++ [id]
      lower := { monitor.exchange.forward.lower with phase := .done } }
    drops := monitor.exchange.drops ++ [id]
    slots := monitor.exchange.slots + 1 } }

structure LowerDropped
    (state : PendingUpper initial checks routing quantum allowance reverseLower reverseUpper current monitor location first)
    (actual : Step input) where
  item : Theory.PacketCustody.Item (Transit input)
  selected : D.Selected state.core item .lower actual
  produced : selected.loss.source = CampusTCPTwoProgressOriginalPath.source first
  observed : W.observe cfg monitor actual = lowerAfter monitor item.id
  next : PendingUpper initial checks routing quantum allowance reverseLower reverseUpper selected.appended.move.after
    (W.observe cfg monitor actual) location first
  book : next.core.losses.book = D.lowerBook selected

private theorem lower_exposed {packetConfig : CampusTCPTwoProgressMonitor.Config}
    {state : State input} {value : CampusTCPTwoProgressMonitor.Monitor} {id : Nat}
    (chosen : M.dropTarget packetConfig state value id = some .lower) :
    M.exposedPacket packetConfig state value.lower = some id := by
  unfold M.dropTarget at chosen
  repeat' split at chosen
  all_goals cases chosen
  all_goals simp_all only [beq_iff_eq]

theorem LowerDropped.packet_eq
    {state : PendingUpper initial checks routing quantum allowance reverseLower reverseUpper current monitor location first}
    (value : LowerDropped state actual)
    (chosen : M.dropTarget ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward id = some .lower) :
    value.item.id = id :=
  Option.some.inj ((lower_exposed value.selected.selected).symm.trans (lower_exposed chosen))

theorem LowerDropped.event
    {state : PendingUpper initial checks routing quantum allowance reverseLower reverseUpper current monitor location first}
    (value : LowerDropped state actual)
    (chosen : M.dropTarget ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward id = some .lower) :
    actual.event = .dropPacket id :=
  value.selected.appended.facts.event.trans (congrArg Event.dropPacket (value.packet_eq chosen))

private theorem lower_observed
    (state : PendingUpper initial checks routing quantum allowance reverseLower reverseUpper current monitor location first)
    (item : Theory.PacketCustody.Item (Transit input)) (selected : D.Selected state.core item .lower actual) :
    W.observe cfg monitor actual = lowerAfter monitor item.id := by
  rw [selected.observed]
  simp (config := { zetaHave := true }) only [CampusTCPTwoTransferDropObserve.afterDrop,
    M.observeDrop, selected.appended.move.beforeEq, selected.selected, M.normalize, state.mode, state.ack,
    state.upperPending, Option.isNone_none, CampusTCPTwoProgressMonitorFacts.phase_beq_self,
    show (CampusTCPRoundMonitor.Phase.needSend == .done) = false from rfl,
    Bool.and_false, Bool.false_eq_true, ite_false, lowerAfter]

private theorem lower_drop_path_at
    (state : PendingUpper initial checks routing quantum allowance reverseLower reverseUpper current monitor location first)
    (path : CampusTCPTwoProgressPaths.DataIngress initial current .lower monitor.exchange.forward.lower)
    (source : path.output.produced = CampusTCPTwoProgressOriginalPath.source first)
    (chosen : M.dropTarget ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward path.packetID = some .lower)
    (allowed : W.Allowed cfg current.report.final monitor (.dropPacket path.packetID)) :
    ∃ actual, Nonempty (LowerDropped state actual) := by
  obtain ⟨actual, drop, ⟨credited⟩⟩ := CampusTCPTwoTransferLocatedDrop.original_ingress_at state.core state.exchange path chosen allowed
  have observed := lower_observed state drop.item drop.selected
  let nextCore := credited.result.next
  have book : nextCore.losses.book = D.lowerBook drop.selected := credited.result.bookEq
  have produced : drop.selected.loss.source = CampusTCPTwoProgressOriginalPath.source first := drop.sourceEq.trans source
  let next : PendingUpper initial checks routing quantum allowance reverseLower reverseUpper drop.selected.appended.move.after
      (W.observe cfg monitor actual) location first := {
    core := nextCore
    exchange := by rw [observed]; exact state.exchange
    mode := by rw [observed]; exact state.mode
    lowerPath := .lost (by rw [observed]; rfl) state.core.losses.book.losses.length drop.selected.loss
      (by rw [book]; exact List.getElem?_concat_length) produced (by rw [book]; rfl)
    upperPending := by rw [observed]; exact state.upperPending
    ack := by rw [observed]; exact state.ack
    waiting := by rw [observed]; exact state.waiting
    retry := by rw [observed]; exact state.retry
    retries := by rw [observed]; exact state.retries
    sources := state.sources.no_receipt drop.selected.appended.move drop.selected.appended.facts.receipt }
  exact ⟨actual, ⟨⟨drop.item, drop.selected, produced, observed, next, book⟩⟩⟩

theorem PendingUpper.lower_drop_at
    (state : PendingUpper initial checks routing quantum allowance reverseLower reverseUpper current monitor location first)
    (pending : monitor.exchange.forward.lower.phase = .dataIngress)
    (chosen : M.dropTarget ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward id = some .lower)
    (allowed : W.Allowed cfg current.report.final monitor (.dropPacket id)) :
    ∃ actual, Nonempty (LowerDropped state actual) := by
  cases state.lowerPath with
  | ingress path source =>
    have packet : path.packetID = id := Option.some.inj
      ((path.exposed_packet ((cfg).at current.report.final).forward).symm.trans (lower_exposed chosen))
    exact lower_drop_path_at state path source (by rw [packet]; exact chosen) (by rw [packet]; exact allowed)
  | lost phase _ _ _ _ _ => rw [pending] at phase; cases phase

theorem PendingUpper.lower_drop_step
    (state : PendingUpper initial checks routing quantum allowance reverseLower reverseUpper current monitor location first)
    (pending : monitor.exchange.forward.lower.phase = .dataIngress)
    (chosen : M.dropTarget ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward id = some .lower)
    (allowed : W.Allowed cfg current.report.final monitor (.dropPacket id))
    (actual : Step input) (before : actual.before = current.report.final) (event : actual.event = .dropPacket id) :
    Nonempty (LowerDropped state actual) := by
  obtain ⟨enabled, ⟨value⟩⟩ := state.lower_drop_at pending chosen allowed
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (value.selected.appended.move.beforeEq.trans before.symm) ((value.event chosen).trans event.symm)
  exact ⟨same ▸ value⟩

end Netlib.Check.CampusTCPTwoTransferPreparationState
