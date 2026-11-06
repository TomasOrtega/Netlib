import Netlib.Check.CampusTCPTwoProgressEvidence
import Netlib.Check.CampusTCPTwoProgressPhaseAckReceive
import Netlib.Check.CampusTCPTwoProgressPathRetain
import Netlib.Check.CampusTCPTwoProgressGatewayRanges

/-!
# Joint state after actual ACK receipt

Partial retirement retains the actual upper work or loss cause.
Full retirement enters the read phase on the same suffix.
-/

namespace Netlib.Check.CampusTCPTwoProgressPhaseAckRetire

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (Core Arrived)
open CampusTCPTwoProgressPhaseState
open CampusTCPTwoProgressPaths
open CampusTCPTwoProgressPathsReady (rangeAt)
open CampusTCPTwoProgressSetup (config)

namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane observe normalize)
end M
namespace S
export CampusTCPTwoProgressSender (Stage Part Original Retires)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
namespace A
export CampusTCPTwoProgressPhaseAckReceive (Advanced Zero retirementBook)
end A
namespace D
export CampusTCPTwoProgressPhaseDebt (Debt Work)
end D
namespace P
export CampusTCPTwoProgressPathRetain (consumedPacket)
end P

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor nextMonitor : M.Monitor} {sent nextSent : S.Stage initial} {received : R.Stage}
variable {core : Core initial native quantum allowance current monitor sent received}
variable {lane dataLane : M.Lane} {count : Nat} {part : S.Part}

private theorem pending_eq (first second : Theory.PacketCustody.Item (Transit input))
    (firstMember : first ∈ current.report.final.custody.pending)
    (secondMember : second ∈ current.report.final.custody.pending) (same : first.id = second.id) : first = second := by
  obtain ⟨resolved, _⟩ := Theory.PacketCustody.resolve_completes current.report.final.custody first firstMember .dropped
  have valid := CampusTCPCustodyFacts.Report.valid current.report
  exact (resolved.item_eq valid first firstMember rfl).symm.trans (resolved.item_eq valid second secondMember same.symm)

private theorem ingress_ack_ne (data : DataIngress initial current part dataLane) (ack : AckLink initial current count lane) :
    data.packetID ≠ ack.packetID := by
  intro same
  obtain ⟨left, leftMember, leftID, leftPayload⟩ := data.toIngress.custody_item
  obtain ⟨right, rightMember, rightID, rightPayload⟩ := ack.toLink.custody_item
  have items := pending_eq left right leftMember rightMember (leftID.trans (same.trans rightID.symm))
  have payload := congrArg (fun item => item.value.payload) items
  rw [leftPayload, rightPayload] at payload
  cases payload

private theorem link_ack_ne (data : DataLink initial current part dataLane) (ack : AckLink initial current count lane) :
    data.packetID ≠ ack.packetID := by
  intro same
  obtain ⟨left, leftMember, leftID, leftPayload⟩ := data.toLink.custody_item
  obtain ⟨right, rightMember, rightID, rightPayload⟩ := ack.toLink.custody_item
  have items := pending_eq left right leftMember rightMember (leftID.trans (same.trans rightID.symm))
  have payload := congrArg (fun item => item.value.payload) items
  rw [leftPayload, rightPayload] at payload
  have actor := congrArg (fun transit => (CampusTCPTwoProgressLossHistory.transitSource transit).actor) payload
  change data.served.ticket.value.produced.actor = ack.served.ticket.value.produced.actor at actor
  rw [data.actor, ack.actor] at actor
  cases sender <;> cases actor

private theorem ingress_other (data : DataIngress initial current part dataLane) (ack : AckLink initial current count lane)
    (delivery : CampusTCPRoundDelivery.Delivery current.report complete current.endpoints ack.index ack.served ack.emission ack.emitted) :
    P.consumedPacket current.report.final delivery.step.event ≠ some data.packetID := by
  rw [delivery.event]
  change current.report.final.custody.pendingID (Transit.linkAt ack.index) ≠ some data.packetID
  rw [ack.custody]
  intro same
  exact ingress_ack_ne data ack (Option.some.inj same).symm

private theorem link_other (data : DataLink initial current part dataLane) (ack : AckLink initial current count lane)
    (delivery : CampusTCPRoundDelivery.Delivery current.report complete current.endpoints ack.index ack.served ack.emission ack.emitted) :
    P.consumedPacket current.report.final delivery.step.event ≠ some data.packetID := by
  rw [delivery.event]
  change current.report.final.custody.pendingID (Transit.linkAt ack.index) ≠ some data.packetID
  rw [ack.custody]
  intro same
  exact link_ack_ne data ack (Option.some.inj same).symm

private theorem gateway_frame (ack : AckLink initial current count lane)
    (delivery : CampusTCPRoundDelivery.Delivery current.report complete current.endpoints ack.index ack.served ack.emission ack.emitted)
    (move : Move current delivery.step) :
    beforeService input move.after.report.final gateway = beforeService input current.report.final gateway := by
  rw [move.final, CampusTCPRoundLocal.step_service_nonservice delivery.step (by rw [delivery.event]; trivial), delivery.beforeEq]

private def data_after (ack : AckLink initial current count lane)
    (delivery : CampusTCPRoundDelivery.Delivery current.report complete current.endpoints ack.index ack.served ack.emission ack.emitted)
    (move : Move current delivery.step) (next : Core initial native quantum allowance move.after nextMonitor nextSent received)
    (work : DataWork initial native current core.live.gatewayState part dataLane) :
    DataWork initial native move.after next.live.gatewayState part dataLane := by
  cases work with
  | ingress path source =>
    exact .ingress (path.after_move move (ingress_other path ack delivery)) (source.retain_steps move.retained)
  | ticket path source =>
    exact .ticket (path.after_quiet move (by rw [delivery.event]; trivial)) (source.retain_steps move.retained)
  | link path source covered =>
    have ranges := core.live.gatewayState.ranges_same next.live.gatewayState (gateway_frame ack delivery move)
    have kept : (rangeAt next.live.gatewayState part).isSome = true := by
      cases part
      · change next.live.gatewayState.ranges.lowerRun.isSome = true
        rw [ranges.1]
        exact covered
      · change next.live.gatewayState.ranges.upperRun.isSome = true
        rw [ranges.2]
        exact covered
    exact .link (path.after_move move (link_other path ack delivery)) (source.retain_steps move.retained) kept

private def original_after (ack : AckLink initial current count lane)
    (delivery : CampusTCPRoundDelivery.Delivery current.report complete current.endpoints ack.index ack.served ack.emission ack.emitted)
    (move : Move current delivery.step) (next : Core initial native quantum allowance move.after nextMonitor nextSent received)
    (work : OriginalLane initial native current core.live.gatewayState received part dataLane) :
    OriginalLane initial native move.after next.live.gatewayState received part dataLane := by
  cases work with
  | active work missing => exact .active (data_after ack delivery move next work) missing
  | done phase => exact .done phase

private def ackCleared (monitor : M.Monitor) (index : Nat) : M.Monitor :=
  { monitor with ack := none, ackReceipts := monitor.ackReceipts ++ [index] }

private structure Layout (before after : M.Monitor) : Prop where
  mode : after.mode = .originals ∨ after.mode = .recovery
  lower : after.lower = before.lower
  upper : after.upper = before.upper
  retry : after.retry = before.retry
  ack : after.ack = none
  originals : after.mode = .originals → after.retry.phase = .done ∧ after.waiting = false ∧ after.retries = 0
  recovery : after.mode = .recovery → after.lower.phase = .done ∧ after.upper.phase = .done
  recoveryWaiting : after.mode = .recovery → after.waiting = true
  waiting : after.waiting = true → after.ack = none ∧ after.retry.phase = .done
  runnable : after.mode = .recovery → after.waiting = false → after.ack = none → after.retry.phase ≠ .done
  originalOpen : after.mode = .originals → after.ack = none → ¬(after.lower.phase = .done ∧ after.upper.phase = .done)

private theorem after_layout {after : Cut input complete} {index : Nat} (active : Active core)
    (selected : monitor.ack = some lane)
    (next : Core initial native quantum allowance after nextMonitor nextSent received)
    (nonempty : nextSent.ledger ≠ [])
    (observed : nextMonitor = M.normalize (config initial native quantum allowance) after.report.final (ackCleared monitor index)) :
    Layout monitor nextMonitor := by
  have serial := active.serial (by rw [selected]; rfl)
  have quiet : monitor.waiting = false := by
    cases waiting : monitor.waiting
    · rfl
    · have absent := (active.waiting waiting).1
      rw [selected] at absent
      cases absent
  rcases CampusTCPTwoProgressPhaseNormalize.normalize_cases (raw := ackCleared monitor index) next nonempty with
    ⟨unresolved, same⟩ | ⟨resolved, same⟩
  · have afterEq := observed.trans same
    have mode : monitor.mode = .originals := by
      rcases active.mode with mode | mode
      · exact mode
      · exact False.elim (unresolved ⟨rfl, .inr ⟨mode, serial⟩⟩)
    have unclosed : ¬(monitor.lower.phase = .done ∧ monitor.upper.phase = .done) := by
      intro closed
      exact unresolved ⟨rfl, .inl ⟨mode, closed⟩⟩
    exact {
      mode := by rw [afterEq]; exact Or.inl mode
      lower := by rw [afterEq]; rfl
      upper := by rw [afterEq]; rfl
      retry := by rw [afterEq]; rfl
      ack := by rw [afterEq]; rfl
      originals := fun _ => by simpa only [afterEq, ackCleared] using active.originals mode
      recovery := by intro impossible; rw [afterEq] at impossible; change monitor.mode = .recovery at impossible; rw [mode] at impossible; cases impossible
      recoveryWaiting := by intro impossible; rw [afterEq] at impossible; change monitor.mode = .recovery at impossible; rw [mode] at impossible; cases impossible
      waiting := by intro impossible; rw [afterEq] at impossible; change monitor.waiting = true at impossible; rw [quiet] at impossible; cases impossible
      runnable := by intro impossible; rw [afterEq] at impossible; change monitor.mode = .recovery at impossible; rw [mode] at impossible; cases impossible
      originalOpen := fun _ _ => by simpa only [afterEq, ackCleared] using unclosed }
  · have afterEq := observed.trans same
    have closed : monitor.lower.phase = .done ∧ monitor.upper.phase = .done := by
      obtain ⟨_, original | recovery⟩ := resolved
      · exact original.2
      · exact active.recovery recovery.1
    exact {
      mode := by rw [afterEq]; exact Or.inr rfl
      lower := by rw [afterEq]; rfl
      upper := by rw [afterEq]; rfl
      retry := by rw [afterEq]; rfl
      ack := by rw [afterEq]; rfl
      originals := by intro impossible; rw [afterEq] at impossible; cases impossible
      recovery := fun _ => by simpa only [afterEq, ackCleared] using closed
      recoveryWaiting := by intro _; rw [afterEq]
      waiting := by
        intro _
        constructor
        · rw [afterEq]; rfl
        · rw [afterEq]; exact serial
      runnable := by intro _ impossible; rw [afterEq] at impossible; cases impossible
      originalOpen := by intro impossible; rw [afterEq] at impossible; cases impossible }

private def active_after (active : Active core) (ack : AckLink initial current count lane)
    (delivery : CampusTCPRoundDelivery.Delivery current.report complete current.endpoints ack.index ack.served ack.emission ack.emitted)
    (move : Move current delivery.step) (next : Core initial native quantum allowance move.after nextMonitor nextSent received)
    (selected : monitor.ack = some lane) (layout : Layout monitor nextMonitor)
    (preparing : nextSent.preparing = false) (nonempty : nextSent.ledger ≠ [])
    (debt : ∀ part head rest, CampusTCPTwoProgressRetry.HeadRange nextSent part head rest → Nonempty (D.Debt next part))
    (upperMissing : nextSent.retiredBytes = 0 → ¬Arrived received .upper → nextMonitor.upper.phase = .done →
      ∃ position, next.losses.book.cause .upper = some position) : Active next := by
  have serial := active.serial (by rw [selected]; rfl)
  exact {
    mode := layout.mode, preparing, nonempty
    lowerLane := by simpa only [layout.lower] using original_after ack delivery move next active.lowerLane
    upperLane := by simpa only [layout.upper] using original_after ack delivery move next active.upperLane
    retry := .done (by rw [layout.retry]; exact serial)
    ack := by unfold AckState; rw [layout.ack]; exact PUnit.unit
    originals := layout.originals, recovery := layout.recovery
    recoveryHead := by
      intro mode nonwaiting
      rw [layout.recoveryWaiting mode] at nonwaiting
      cases nonwaiting
    serial := by intro impossible; rw [layout.ack] at impossible; cases impossible
    ackNonempty := by intro impossible; rw [layout.ack] at impossible; cases impossible
    waiting := layout.waiting, runnable := layout.runnable, originalOpen := layout.originalOpen
    debt, upperMissing
    zeroAck := by intro _ impossible; rw [layout.ack] at impossible; cases impossible
    sources := active.sources.ack ack delivery move }

private theorem original_sent {part : S.Part} {before : M.Lane}
    (value : OriginalLane initial native current core.live.gatewayState received part before) : before.phase ≠ .needSend := by
  cases value with
  | active work missing =>
    cases work with
    | ingress path _ => rw [path.phase]; decide
    | ticket path _ => rw [path.phase]; decide
    | link path _ _ => rw [path.phase]; decide
  | done phase => rw [phase]; decide

private def work_after (ack : AckLink initial current count lane)
    (delivery : CampusTCPRoundDelivery.Delivery current.report complete current.endpoints ack.index ack.served ack.emission ack.emitted)
    (move : Move current delivery.step) (work : D.Work initial native current part dataLane) :
    D.Work initial native move.after part dataLane := by
  cases work with
  | ingress path => exact .ingress (path.after_move move (ingress_other path ack delivery))
  | ticket path => exact .ticket (path.after_quiet move (by rw [delivery.event]; trivial))
  | link path => exact .link (path.after_move move (link_other path ack delivery))

private theorem head_remaining (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest) :
    sent.retiredBytes < part.offset lower + (part.bytes lower upper).length := by
  have first := List.length_pos_iff.mpr initial.lowerNonempty
  have second := List.length_pos_iff.mpr initial.upperNonempty
  cases selected <;> simp only [CampusTCPTwoProgressSender.Stage.retiredBytes,
    CampusTCPTwoProgressSender.Part.offset, CampusTCPTwoProgressSender.Part.bytes, Nat.zero_add] <;> omega

private def zero_debt (active : Active core) (path : AckLink initial current (received.bytes lower upper).length lane)
    (value : A.Zero core path) (selected : monitor.ack = some lane) (layout : Layout monitor
      (M.observe (config initial native quantum allowance) monitor value.value.delivery.step))
    (equal : sent.retiredBytes = (received.bytes lower upper).length)
    (head : CampusTCPTwoProgressRetry.HeadRange sent part entry rest) (debt : D.Debt core part) : D.Debt value.nextCore part := by
  cases debt with
  | cause position chosen => exact .cause position (by rw [value.losses]; exact chosen)
  | lower same work => exact .lower same (by simpa only [layout.lower] using work_after path value.value.delivery.toDelivery value.value.delivery.move work)
  | upper same work => exact .upper same (by simpa only [layout.upper] using work_after path value.value.delivery.toDelivery value.value.delivery.move work)
  | retry work => exact False.elim (work.not_done (active.serial (by rw [selected]; rfl)))
  | ack lane pending covered =>
    have outstanding := head_remaining head
    rw [equal] at outstanding
    exact False.elim (Nat.not_le_of_lt outstanding covered)

structure ZeroState (active : Active core) (path : AckLink initial current (received.bytes lower upper).length lane) where
  value : A.Zero core path
  next : Active value.nextCore

theorem zero_at (active : Active core) (path : AckLink initial current (received.bytes lower upper).length lane)
    (selected : monitor.ack = some lane) (equal : sent.retiredBytes = (received.bytes lower upper).length)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor
      (.deliver path.index path.emission.bytes true)) : Nonempty (ZeroState active path) := by
  obtain ⟨value⟩ := CampusTCPTwoProgressPhaseAckReceive.zero_at core path active.preparing equal
    (active.zeroAck lane selected equal) (active.ackNonempty (by rw [selected]; rfl)) active.mode
    (original_sent active.lowerLane) (original_sent active.upperLane) selected allowed
  have observed := value.observed
  rw [← value.value.delivery.move.final] at observed
  have layout := after_layout active selected value.nextCore active.nonempty observed
  apply Nonempty.intro
  refine ⟨value, active_after active path value.value.delivery.toDelivery value.value.delivery.move value.nextCore selected layout
    active.preparing active.nonempty ?_ ?_⟩
  · intro part head rest selectedHead
    obtain ⟨debt⟩ := active.debt part head rest selectedHead
    exact ⟨zero_debt active path value selected layout equal selectedHead debt⟩
  · intro zero missing done
    obtain ⟨position, chosen⟩ := active.upperMissing zero missing (by rw [← layout.upper]; exact done)
    exact ⟨position, by rw [value.losses]; exact chosen⟩

private def partial_after {first : S.Original initial .lower} {second : S.Original initial .upper} {head : Recovery.Outstanding}
    {core : Core initial native quantum allowance current monitor (.both first second head) received}
    (active : Active core) (path : AckLink initial current (received.bytes lower upper).length lane)
    (delivery : CampusTCPRoundDelivery.Delivery current.report complete current.endpoints path.index path.served path.emission path.emitted)
    (move : Move current delivery.step)
    (next : Core initial native quantum allowance move.after nextMonitor (.tail first second second.entry) received)
    (selected : monitor.ack = some lane)
    (coordinate : lower.length = (received.bytes lower upper).length)
    (observed : nextMonitor = M.normalize (config initial native quantum allowance) move.after.report.final
      (ackCleared monitor current.report.final.receipts.length))
    (book : next.losses.book = core.losses.book.clearLower) : Active next := by
  have firstPositive := List.length_pos_iff.mpr initial.lowerNonempty
  have secondPositive := List.length_pos_iff.mpr initial.upperNonempty
  have receiverStage : received = .lowerReleased := by
    cases received with
    | empty | upperHeld => change lower.length = 0 at coordinate; omega
    | lowerReleased => rfl
    | allReleased => change lower.length = (lower ++ upper).length at coordinate; rw [List.length_append] at coordinate; omega
  have nonempty : (CampusTCPTwoProgressSender.Stage.tail first second second.entry).ledger ≠ [] := by intro impossible; cases impossible
  have layout := after_layout active selected next nonempty observed
  apply active_after active path delivery move next selected layout rfl nonempty
  · intro part head rest selectedHead
    have role : part = .upper := by cases selectedHead; rfl
    cases role
    cases active.upperLane with
    | active work missing =>
      exact ⟨.upper rfl (by simpa only [layout.upper] using (data_after path delivery move next work).work)⟩
    | done phase =>
      have missing : ¬Arrived received .upper := by rw [receiverStage]; intro impossible; cases impossible
      obtain ⟨position, chosen⟩ := active.upperMissing rfl missing phase
      exact ⟨.cause position (by rw [book]; exact chosen)⟩
  · intro zero _ _
    change lower.length = 0 at zero
    omega

private def ready_after {first : S.Original initial .lower} {second : S.Original initial .upper}
    (active : Active core) (path : AckLink initial current (received.bytes lower upper).length lane)
    (delivery : CampusTCPRoundDelivery.Delivery current.report complete current.endpoints path.index path.served path.emission path.emitted)
    (move : Move current delivery.step)
    (next : Core initial native quantum allowance move.after nextMonitor (.retired first second) received)
    (selected : monitor.ack = some lane)
    (observed : nextMonitor = M.normalize (config initial native quantum allowance) move.after.report.final
      (ackCleared monitor current.report.final.receipts.length)) : CampusTCPTwoProgressEvidence.Ready next := by
  have all := CampusTCPTwoProgressPhaseNormalize.retired_allReleased next
  have lowerDone : monitor.lower.phase = .done := by
    cases active.lowerLane with
    | active work missing => exact False.elim (missing (by rw [all]; trivial))
    | done phase => exact phase
  have upperDone : monitor.upper.phase = .done := by
    cases active.upperLane with
    | active work missing => exact False.elim (missing (by rw [all]; trivial))
    | done phase => exact phase
  have shape : CampusTCPTwoProgressPhaseNormalize.Resolved (ackCleared monitor current.report.final.receipts.length) := by
    refine ⟨rfl, ?_⟩
    rcases active.mode with mode | mode
    · exact .inl ⟨mode, lowerDone, upperDone⟩
    · exact .inr ⟨mode, active.serial (by rw [selected]; rfl)⟩
  have normalized := CampusTCPTwoProgressPhaseNormalize.normalize_empty next shape rfl
  exact {
    mode := congrArg (fun state => state.mode) (observed.trans normalized)
    retired := rfl, preparing := rfl
    sources := active.sources.ack path delivery move }

inductive Outcome (next : Core initial native quantum allowance current monitor sent received) where
  | active (value : Active next)
  | ready (value : CampusTCPTwoProgressEvidence.Ready next)

private theorem advancing_outcome (active : Active core) (path : AckLink initial current (received.bytes lower upper).length lane)
    (delivery : CampusTCPRoundDelivery.Delivery current.report complete current.endpoints path.index path.served path.emission path.emitted)
    (move : Move current delivery.step) (next : Core initial native quantum allowance move.after nextMonitor nextSent received)
    (selected : monitor.ack = some lane) (retiring : S.Retires sent amount nextSent)
    (coordinate : nextSent.retiredBytes = (received.bytes lower upper).length)
    (observed : nextMonitor = M.normalize (config initial native quantum allowance) move.after.report.final
      (ackCleared monitor current.report.final.receipts.length))
    (book : next.losses.book = A.retirementBook core.losses.book nextSent) : Nonempty (Outcome next) := by
  cases retiring with
  | lower first second head => exact ⟨.active (partial_after (sent := .both first second head) (core := core) active path delivery move next selected coordinate observed book)⟩
  | both first second head => exact ⟨.ready (ready_after active path delivery move next selected observed)⟩
  | tail first second head => exact ⟨.ready (ready_after active path delivery move next selected observed)⟩

structure AdvancedState (active : Active core) (path : AckLink initial current (received.bytes lower upper).length lane) where
  value : A.Advanced core path
  next : Outcome value.nextCore

theorem advancing_at (active : Active core) (path : AckLink initial current (received.bytes lower upper).length lane)
    (selected : monitor.ack = some lane) (different : sent.retiredBytes ≠ (received.bytes lower upper).length)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor
      (.deliver path.index path.emission.bytes true)) : Nonempty (AdvancedState active path) := by
  obtain ⟨value⟩ := CampusTCPTwoProgressPhaseAckReceive.advancing_at core path active.preparing different active.mode
    (original_sent active.lowerLane) (original_sent active.upperLane) selected allowed
  have observed := value.observed
  rw [← value.value.delivery.move.final] at observed
  obtain ⟨outcome⟩ := advancing_outcome active path value.value.delivery.toDelivery value.value.delivery.move value.nextCore
    selected value.value.retiring value.coordinate observed value.losses
  exact ⟨⟨value, outcome⟩⟩

inductive Received (active : Active core) (path : AckLink initial current (received.bytes lower upper).length lane) where
  | zero (value : ZeroState active path)
  | advanced (value : AdvancedState active path)

theorem receive_at (active : Active core) (path : AckLink initial current (received.bytes lower upper).length lane)
    (selected : monitor.ack = some lane)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor
      (.deliver path.index path.emission.bytes true)) : Nonempty (Received active path) := by
  by_cases equal : sent.retiredBytes = (received.bytes lower upper).length
  · obtain ⟨value⟩ := zero_at active path selected equal allowed
    exact ⟨.zero value⟩
  · obtain ⟨value⟩ := advancing_at active path selected equal allowed
    exact ⟨.advanced value⟩

variable {active : Active core} {path : AckLink initial current (received.bytes lower upper).length lane}

def Received.actual (record : Received active path) : Step input :=
  match record with
  | .zero value => value.value.value.delivery.step
  | .advanced value => value.value.value.delivery.step

def Received.move (record : Received active path) : Move current record.actual :=
  match record with
  | .zero value => value.value.value.delivery.move
  | .advanced value => value.value.value.delivery.move

theorem Received.event (record : Received active path) : record.actual.event = .deliver path.index path.emission.bytes true := by
  cases record with
  | zero value => exact value.value.value.delivery.event
  | advanced value => exact value.value.value.delivery.event

def Received.evidence (record : Received active path) :
    CampusTCPTwoProgressEvidence.Evidence initial native quantum allowance record.move.after
      (M.observe (config initial native quantum allowance) monitor record.actual) :=
  match record with
  | .zero value => .active value.value.nextCore value.next
  | .advanced value => match value.next with
    | .active next => .active value.value.nextCore next
    | .ready next => .ready value.value.nextCore next

end Netlib.Check.CampusTCPTwoProgressPhaseAckRetire
