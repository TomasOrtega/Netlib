import Netlib.Check.CampusTCPTwoTransferEvidence
import Netlib.Check.CampusTCPTwoTransferAckReceiveCore
import Netlib.Check.CampusTCPTwoTransferGatewayComplete
import Netlib.Check.CampusTCPTwoProgressPhaseNormalize

/-!
# Joint state after actual ACK receipt

Partial retirement retains the actual upper work or loss cause.
Full retirement enters the read phase on the same suffix.
-/

namespace Netlib.Check.CampusTCPTwoTransferAckRetire

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (Arrived)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferPhaseState (Active)
open CampusTCPTwoTransferWork (DataWork OriginalLane RetryLane AckState)
open CampusTCPTwoTransferPaths
open CampusTCPTwoTransferAdmission (rangeAt)
open CampusTCPTwoProgressPhaseNormalize (Resolved normalize_unresolved)

namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane observe normalize)
end M
namespace W
export CampusTCPTwoTransferMonitor (Monitor observe)
end W
namespace E
export CampusTCPTwoTransferEvidence (Forward)
end E
namespace S
export CampusTCPTwoProgressSender (Stage Part Original Retires)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
namespace A
export CampusTCPTwoTransferAckReceiveCore (Advanced Zero retirementBook)
end A
namespace D
export CampusTCPTwoTransferPhaseState (Debt)
export CampusTCPTwoTransferWork (Work)
end D
namespace P
export CampusTCPTwoProgressPathRetain (consumedPacket)
end P

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor nextMonitor : W.Monitor} {sent nextSent : S.Stage initial} {received : R.Stage}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}
variable {lane dataLane : M.Lane} {count : Nat} {part : S.Part}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper
local notation "localCfg" => CampusTCPTwoExchangeMonitor.Config.forward
  (CampusTCPTwoTransferMonitor.Config.at
    (config initial checks routing quantum allowance reverseLower reverseUpper) current.report.final)

private theorem sender_runtime {after : Cut input complete} {nextMonitor : W.Monitor} {nextSent : S.Stage initial}
    (next : Core initial checks routing quantum allowance reverseLower reverseUpper after nextMonitor location nextSent received)
    (config : CampusTCPTwoProgressMonitor.Config) (source : config.sender = sender) :
    CampusTCPGapProgressMonitor.senderRecovery config.toConfig after.report.final = some next.live.senderFlight.recovery := by
  simp only [CampusTCPGapProgressMonitor.senderRecovery, after.connection, source, next.live.senderFlight.runtime]

private theorem normalize_cases {after : Cut input complete} {raw : M.Monitor}
    (next : Core initial checks routing quantum allowance reverseLower reverseUpper after nextMonitor location nextSent received)
    (nonempty : nextSent.ledger ≠ []) (config : CampusTCPTwoProgressMonitor.Config) (source : config.sender = sender) :
    (¬Resolved raw ∧ M.normalize config after.report.final raw = raw) ∨
      (Resolved raw ∧ M.normalize config after.report.final raw = { raw with mode := .recovery, waiting := true }) := by
  by_cases resolved : Resolved raw
  · apply Or.inr
    refine ⟨resolved, ?_⟩
    have present : next.live.senderFlight.recovery.outstanding.isEmpty = false := by
      rw [next.live.senderFlight.ledger]
      cases ledger : nextSent.ledger with
      | nil => exact False.elim (nonempty ledger)
      | cons head rest => rfl
    simp (config := { zetaHave := true }) only [M.normalize, sender_runtime next config source, present, Bool.false_eq_true, ite_false]
    obtain ⟨ack, original | recovery⟩ := resolved
    · obtain ⟨mode, lower, upper⟩ := original; rw [ack, mode, lower, upper]; rfl
    · obtain ⟨mode, retry⟩ := recovery; rw [ack, mode, retry]; rfl
  · exact .inl ⟨resolved, normalize_unresolved _ _ _ resolved⟩

private theorem normalize_empty {after : Cut input complete} {raw : M.Monitor}
    (next : Core initial checks routing quantum allowance reverseLower reverseUpper after nextMonitor location nextSent received)
    (shape : Resolved raw) (empty : nextSent.ledger = []) (config : CampusTCPTwoProgressMonitor.Config) (source : config.sender = sender) :
    M.normalize config after.report.final raw = { raw with mode := .needRead, waiting := false } := by
  simp (config := { zetaHave := true }) only [M.normalize, ite_true, sender_runtime next config source,
    next.live.senderFlight.ledger, empty, List.isEmpty_nil]
  obtain ⟨ack, original | recovery⟩ := shape
  · obtain ⟨mode, lower, upper⟩ := original; rw [ack, mode, lower, upper]; rfl
  · obtain ⟨mode, retry⟩ := recovery; rw [ack, mode, retry]; rfl

private theorem retired_allReleased {after : Cut input complete} {first : S.Original initial .lower} {second : S.Original initial .upper}
    (next : Core initial checks routing quantum allowance reverseLower reverseUpper after nextMonitor location (.retired first second) received) :
    received = .allReleased := by
  have retired := next.retired
  have lowerPositive := List.length_pos_iff.mpr initial.lowerNonempty
  have upperPositive := List.length_pos_iff.mpr initial.upperNonempty
  change lower.length + upper.length ≤ _ at retired
  cases received with
  | empty | upperHeld => change lower.length + upper.length ≤ 0 at retired; omega
  | lowerReleased => change lower.length + upper.length ≤ lower.length at retired; omega
  | allReleased => rfl

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
    beforeService input move.after.report.final location = beforeService input current.report.final location := by
  rw [move.final, CampusTCPRoundLocal.step_service_nonservice delivery.step (by rw [delivery.event]; trivial), delivery.beforeEq]

private def data_after (ack : AckLink initial current count lane)
    (delivery : CampusTCPRoundDelivery.Delivery current.report complete current.endpoints ack.index ack.served ack.emission ack.emitted)
    (move : Move current delivery.step) (next : Core initial checks routing quantum allowance reverseLower reverseUpper move.after nextMonitor location nextSent received)
    (work : DataWork initial checks current core.live.gatewayState part dataLane) :
    DataWork initial checks move.after next.live.gatewayState part dataLane := by
  cases work with
  | ingress path source =>
    exact .ingress (path.after_move move (ingress_other path ack delivery)) (source.retain_steps move.retained)
  | ticket path selected source =>
    exact .ticket (path.after_quiet move (by rw [delivery.event]; trivial)) selected (source.retain_steps move.retained)
  | link path source covered =>
    have ranges := CampusTCPTwoTransferGatewayComplete.ranges_same core.live.gatewayState next.live.gatewayState (gateway_frame ack delivery move)
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
    (move : Move current delivery.step) (next : Core initial checks routing quantum allowance reverseLower reverseUpper move.after nextMonitor location nextSent received)
    (work : OriginalLane initial checks current core.live.gatewayState received part dataLane) :
    OriginalLane initial checks move.after next.live.gatewayState received part dataLane := by
  cases work with
  | active work missing => exact .active (data_after ack delivery move next work) missing
  | done phase => exact .done phase

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
    (selected : monitor.exchange.forward.ack = some lane)
    (next : Core initial checks routing quantum allowance reverseLower reverseUpper after nextMonitor location nextSent received)
    (nonempty : nextSent.ledger ≠ [])
    (observed : nextMonitor.exchange.forward = M.normalize localCfg after.report.final (CampusTCPTwoTransferAckReceiveObserve.ackCleared monitor.exchange.forward index)) :
    Layout monitor.exchange.forward nextMonitor.exchange.forward := by
  have serial := active.serial (by rw [selected]; rfl)
  have quiet : monitor.exchange.forward.waiting = false := by
    cases waiting : monitor.exchange.forward.waiting
    · rfl
    · have absent := (active.waiting waiting).1
      rw [selected] at absent
      cases absent
  rcases normalize_cases (raw := CampusTCPTwoTransferAckReceiveObserve.ackCleared monitor.exchange.forward index) next nonempty localCfg rfl with
    ⟨unresolved, same⟩ | ⟨resolved, same⟩
  · have afterEq := observed.trans same
    have mode : monitor.exchange.forward.mode = .originals := by
      rcases active.mode with mode | mode
      · exact mode
      · exact False.elim (unresolved ⟨rfl, .inr ⟨mode, serial⟩⟩)
    have unclosed : ¬(monitor.exchange.forward.lower.phase = .done ∧ monitor.exchange.forward.upper.phase = .done) := by
      intro closed
      exact unresolved ⟨rfl, .inl ⟨mode, closed⟩⟩
    exact {
      mode := by rw [afterEq]; exact Or.inl mode
      lower := by rw [afterEq]; rfl
      upper := by rw [afterEq]; rfl
      retry := by rw [afterEq]; rfl
      ack := by rw [afterEq]; rfl
      originals := fun _ => by simpa only [afterEq, CampusTCPTwoTransferAckReceiveObserve.ackCleared] using active.originals mode
      recovery := by intro impossible; rw [afterEq] at impossible; change monitor.exchange.forward.mode = .recovery at impossible; rw [mode] at impossible; cases impossible
      recoveryWaiting := by intro impossible; rw [afterEq] at impossible; change monitor.exchange.forward.mode = .recovery at impossible; rw [mode] at impossible; cases impossible
      waiting := by intro impossible; rw [afterEq] at impossible; change monitor.exchange.forward.waiting = true at impossible; rw [quiet] at impossible; cases impossible
      runnable := by intro impossible; rw [afterEq] at impossible; change monitor.exchange.forward.mode = .recovery at impossible; rw [mode] at impossible; cases impossible
      originalOpen := fun _ _ => by simpa only [afterEq, CampusTCPTwoTransferAckReceiveObserve.ackCleared] using unclosed }
  · have afterEq := observed.trans same
    have closed : monitor.exchange.forward.lower.phase = .done ∧ monitor.exchange.forward.upper.phase = .done := by
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
      recovery := fun _ => by simpa only [afterEq, CampusTCPTwoTransferAckReceiveObserve.ackCleared] using closed
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
    (move : Move current delivery.step) (next : Core initial checks routing quantum allowance reverseLower reverseUpper move.after nextMonitor location nextSent received)
    (selected : monitor.exchange.forward.ack = some lane) (layout : Layout monitor.exchange.forward nextMonitor.exchange.forward)
    (exchange : nextMonitor.exchange.mode = .forward)
    (preparing : nextSent.preparing = false) (nonempty : nextSent.ledger ≠ [])
    (debt : ∀ part head rest, CampusTCPTwoProgressRetry.HeadRange nextSent part head rest → Nonempty (D.Debt next part))
    (upperMissing : nextSent.retiredBytes = 0 → ¬Arrived received .upper → nextMonitor.exchange.forward.upper.phase = .done →
      ∃ position, next.losses.book.cause .upper = some position) : Active next := by
  have serial := active.serial (by rw [selected]; rfl)
  exact {
    exchange
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
    ackGateway := by intro _ impossible; rw [layout.ack] at impossible; cases impossible
    waiting := layout.waiting, runnable := layout.runnable, originalOpen := layout.originalOpen
    debt, upperMissing
    zeroAck := by intro _ impossible; rw [layout.ack] at impossible; cases impossible
    sources := active.sources.ack ack delivery move }

private def work_after (ack : AckLink initial current count lane)
    (delivery : CampusTCPRoundDelivery.Delivery current.report complete current.endpoints ack.index ack.served ack.emission ack.emitted)
    (move : Move current delivery.step) (work : D.Work initial checks current location part dataLane) :
    D.Work initial checks move.after location part dataLane := by
  cases work with
  | ingress path => exact .ingress (path.after_move move (ingress_other path ack delivery))
  | ticket path selected => exact .ticket (path.after_quiet move (by rw [delivery.event]; trivial)) selected
  | link path => exact .link (path.after_move move (link_other path ack delivery))

private theorem head_remaining (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest) :
    sent.retiredBytes < part.offset lower + (part.bytes lower upper).length := by
  have first := List.length_pos_iff.mpr initial.lowerNonempty
  have second := List.length_pos_iff.mpr initial.upperNonempty
  cases selected <;> simp only [CampusTCPTwoProgressSender.Stage.retiredBytes,
    CampusTCPTwoProgressSender.Part.offset, CampusTCPTwoProgressSender.Part.bytes, Nat.zero_add] <;> omega

private def zero_debt (active : Active core) (path : AckLink initial current (received.bytes lower upper).length lane)
    (value : A.Zero core path) (selected : monitor.exchange.forward.ack = some lane) (layout : Layout monitor.exchange.forward
      (W.observe cfg monitor value.value.delivery.step).exchange.forward)
    (equal : sent.retiredBytes = (received.bytes lower upper).length)
    (head : CampusTCPTwoProgressRetry.HeadRange sent part entry rest) (debt : D.Debt core part) : D.Debt value.nextCore part := by
  cases debt with
  | cause position chosen => exact .cause position (by rw [value.losses]; exact chosen)
  | lower same work => exact .lower same (by simpa only [layout.lower] using work_after path value.value.delivery.toDelivery value.value.delivery.move work)
  | upper same work => exact .upper same (by simpa only [layout.upper] using work_after path value.value.delivery.toDelivery value.value.delivery.move work)
  | retry work => exact False.elim (work.not_done (active.serial (by rw [selected]; rfl)))
  | ack lane pending _ covered =>
    have outstanding := head_remaining head
    rw [equal] at outstanding
    exact False.elim (Nat.not_le_of_lt outstanding covered)

structure ZeroState (active : Active core) (path : AckLink initial current (received.bytes lower upper).length lane) where
  value : A.Zero core path
  next : Active value.nextCore

theorem zero_at (active : Active core)
    (controls : CampusTCPTwoTransferControlState.Phase current.report.final monitor.mode location) (path : AckLink initial current (received.bytes lower upper).length lane)
    (selected : monitor.exchange.forward.ack = some lane) (equal : sent.retiredBytes = (received.bytes lower upper).length)
    (allowed : CampusTCPTwoTransferMonitor.Allowed cfg current.report.final monitor
      (.deliver path.index path.emission.bytes true)) : Nonempty (ZeroState active path) := by
  obtain ⟨value⟩ := CampusTCPTwoTransferAckReceiveCore.zero_at core path active.preparing equal
    (active.zeroAck lane selected equal) (active.ackNonempty (by rw [selected]; rfl)) active controls selected allowed
  have observed := value.observed
  rw [← value.value.delivery.move.final] at observed
  have layout := after_layout active selected value.nextCore active.nonempty observed
  apply Nonempty.intro
  refine ⟨value, active_after active path value.value.delivery.toDelivery value.value.delivery.move value.nextCore selected layout (by rw [value.observation.observed]; exact active.exchange)
    active.preparing active.nonempty ?_ ?_⟩
  · intro part head rest selectedHead
    obtain ⟨debt⟩ := active.debt part head rest selectedHead
    exact ⟨zero_debt active path value selected layout equal selectedHead debt⟩
  · intro zero missing done
    obtain ⟨position, chosen⟩ := active.upperMissing zero missing (by rw [← layout.upper]; exact done)
    exact ⟨position, by rw [value.losses]; exact chosen⟩

private def partial_after {first : S.Original initial .lower} {second : S.Original initial .upper} {head : Recovery.Outstanding}
    {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location (.both first second head) received}
    (active : Active core) (path : AckLink initial current (received.bytes lower upper).length lane)
    (delivery : CampusTCPRoundDelivery.Delivery current.report complete current.endpoints path.index path.served path.emission path.emitted)
    (move : Move current delivery.step)
    (next : Core initial checks routing quantum allowance reverseLower reverseUpper move.after nextMonitor location (.tail first second second.entry) received)
    (selected : monitor.exchange.forward.ack = some lane)
    (coordinate : lower.length = (received.bytes lower upper).length)
    (observed : nextMonitor.exchange.forward = M.normalize localCfg move.after.report.final
      (CampusTCPTwoTransferAckReceiveObserve.ackCleared monitor.exchange.forward current.report.final.receipts.length))
    (book : next.losses.book = core.losses.book.clearLower)
    (exchange : nextMonitor.exchange.mode = .forward) : Active next := by
  have firstPositive := List.length_pos_iff.mpr initial.lowerNonempty
  have secondPositive := List.length_pos_iff.mpr initial.upperNonempty
  have receiverStage : received = .lowerReleased := by
    cases received with
    | empty | upperHeld => change lower.length = 0 at coordinate; omega
    | lowerReleased => rfl
    | allReleased => change lower.length = (lower ++ upper).length at coordinate; rw [List.length_append] at coordinate; omega
  have nonempty : (CampusTCPTwoProgressSender.Stage.tail first second second.entry).ledger ≠ [] := by intro impossible; cases impossible
  have layout := after_layout active selected next nonempty observed
  apply active_after active path delivery move next selected layout exchange rfl nonempty
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
    (next : Core initial checks routing quantum allowance reverseLower reverseUpper move.after nextMonitor location (.retired first second) received)
    (selected : monitor.exchange.forward.ack = some lane)
    (observed : nextMonitor.exchange.forward = M.normalize localCfg move.after.report.final
      (CampusTCPTwoTransferAckReceiveObserve.ackCleared monitor.exchange.forward current.report.final.receipts.length))
    (duplicate : next.live.senderFlight.recovery.duplicateAcks = 0)
    (exchange : nextMonitor.exchange.mode = .forward) : E.Forward initial checks routing quantum allowance reverseLower reverseUpper move.after nextMonitor location next := by
  have all := retired_allReleased next
  have lowerDone : monitor.exchange.forward.lower.phase = .done := by
    cases active.lowerLane with
    | active work missing => exact False.elim (missing (by rw [all]; trivial))
    | done phase => exact phase
  have upperDone : monitor.exchange.forward.upper.phase = .done := by
    cases active.upperLane with
    | active work missing => exact False.elim (missing (by rw [all]; trivial))
    | done phase => exact phase
  have shape : CampusTCPTwoProgressPhaseNormalize.Resolved (CampusTCPTwoTransferAckReceiveObserve.ackCleared monitor.exchange.forward current.report.final.receipts.length) := by
    refine ⟨rfl, ?_⟩
    rcases active.mode with mode | mode
    · exact .inl ⟨mode, lowerDone, upperDone⟩
    · exact .inr ⟨mode, active.serial (by rw [selected]; rfl)⟩
  have normalized := normalize_empty next shape rfl localCfg rfl
  have mode : nextMonitor.exchange.forward.mode = .needRead := congrArg (fun state => state.mode) (observed.trans normalized)
  have mainAck : (next.live.gatewayState.gateway.session.lane sender.direction).acknowledged =
      initial.geometry.«prefix» + (lower ++ upper).length := by
    rw [CampusTCPTwoTransferGatewayComplete.session_same core.live.gatewayState next.live.gatewayState
      (gateway_frame path delivery move)]
    have acknowledged := active.ackGateway lane selected path.phase
    have full : (received.bytes lower upper).length = (lower ++ upper).length := by rw [all]; rfl
    exact acknowledged.trans (congrArg (Nat.add initial.geometry.«prefix») full)
  cases all
  exact .readable next exchange mode (active.sources.ack path delivery move) duplicate mainAck

inductive Outcome (next : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received) where
  | active (value : Active next)
  | ready (value : E.Forward initial checks routing quantum allowance reverseLower reverseUpper current monitor location next)

private theorem advancing_outcome (active : Active core) (path : AckLink initial current (received.bytes lower upper).length lane)
    (delivery : CampusTCPRoundDelivery.Delivery current.report complete current.endpoints path.index path.served path.emission path.emitted)
    (move : Move current delivery.step) (next : Core initial checks routing quantum allowance reverseLower reverseUpper move.after nextMonitor location nextSent received)
    (selected : monitor.exchange.forward.ack = some lane) (retiring : S.Retires sent amount nextSent)
    (coordinate : nextSent.retiredBytes = (received.bytes lower upper).length)
    (observed : nextMonitor.exchange.forward = M.normalize localCfg move.after.report.final
      (CampusTCPTwoTransferAckReceiveObserve.ackCleared monitor.exchange.forward current.report.final.receipts.length))
    (book : next.losses.book = A.retirementBook core.losses.book nextSent)
    (duplicate : next.live.senderFlight.recovery.duplicateAcks = 0)
    (exchange : nextMonitor.exchange.mode = .forward) : Nonempty (Outcome next) := by
  cases retiring with
  | lower first second head => exact ⟨.active (partial_after (sent := .both first second head) (core := core) active path delivery move next selected coordinate observed book exchange)⟩
  | both first second head => exact ⟨.ready (ready_after active path delivery move next selected observed duplicate exchange)⟩
  | tail first second head => exact ⟨.ready (ready_after active path delivery move next selected observed duplicate exchange)⟩

structure AdvancedState (active : Active core) (path : AckLink initial current (received.bytes lower upper).length lane) where
  value : A.Advanced core path
  next : Outcome value.nextCore

theorem advancing_at (active : Active core)
    (controls : CampusTCPTwoTransferControlState.Phase current.report.final monitor.mode location) (path : AckLink initial current (received.bytes lower upper).length lane)
    (selected : monitor.exchange.forward.ack = some lane) (different : sent.retiredBytes ≠ (received.bytes lower upper).length)
    (allowed : CampusTCPTwoTransferMonitor.Allowed cfg current.report.final monitor
      (.deliver path.index path.emission.bytes true)) : Nonempty (AdvancedState active path) := by
  obtain ⟨value⟩ := CampusTCPTwoTransferAckReceiveCore.advancing_at core path active.preparing different active controls selected allowed
  have observed := value.observed
  rw [← value.value.delivery.move.final] at observed
  obtain ⟨outcome⟩ := advancing_outcome active path value.value.delivery.toDelivery value.value.delivery.move value.nextCore
    selected value.value.retiring value.coordinate observed value.losses value.duplicates
    (by rw [value.observation.observed]; exact active.exchange)
  exact ⟨⟨value, outcome⟩⟩

inductive Received (active : Active core) (path : AckLink initial current (received.bytes lower upper).length lane) where
  | zero (value : ZeroState active path)
  | advanced (value : AdvancedState active path)

theorem receive_at (active : Active core)
    (controls : CampusTCPTwoTransferControlState.Phase current.report.final monitor.mode location) (path : AckLink initial current (received.bytes lower upper).length lane)
    (selected : monitor.exchange.forward.ack = some lane)
    (allowed : CampusTCPTwoTransferMonitor.Allowed cfg current.report.final monitor
      (.deliver path.index path.emission.bytes true)) : Nonempty (Received active path) := by
  by_cases equal : sent.retiredBytes = (received.bytes lower upper).length
  · obtain ⟨value⟩ := zero_at active controls path selected equal allowed
    exact ⟨.zero value⟩
  · obtain ⟨value⟩ := advancing_at active controls path selected equal allowed
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

def Received.nextStage (record : Received active path) : S.Stage initial :=
  match record with
  | .zero _ => sent
  | .advanced value => value.value.nextStage


def Received.nextCore (record : Received active path) :
    Core initial checks routing quantum allowance reverseLower reverseUpper record.move.after
      (W.observe cfg monitor record.actual) location record.nextStage received :=
  match record with
  | .zero value => value.value.nextCore
  | .advanced value => value.value.nextCore


def Received.forward (record : Received active path) :
    E.Forward initial checks routing quantum allowance reverseLower reverseUpper record.move.after
      (W.observe cfg monitor record.actual) location record.nextCore :=
  match record with
  | .zero value => .active value.next
  | .advanced value => match value.next with
    | .active state => .active state
    | .ready state => state


theorem Received.phase (record : Received active path)
    (controls : CampusTCPTwoTransferControlState.Phase current.report.final monitor.mode location)
    (allowed : CampusTCPTwoTransferMonitor.Allowed cfg current.report.final monitor (.deliver path.index path.emission.bytes true)) :
    CampusTCPTwoTransferControlState.Phase record.move.after.report.final (W.observe cfg monitor record.actual).mode location := by
  have control := (CampusTCPTwoTransferAckReceiveObserve.ordinary_delivery allowed).2
  cases record with
  | zero value =>
    have mode := congrArg (fun whole : W.Monitor => whole.mode) value.value.observation.observed
    change CampusTCPTwoTransferControlState.Phase value.value.value.delivery.move.after.report.final
      (W.observe cfg monitor value.value.value.delivery.step).mode location
    rw [mode]
    exact controls.nonservice control value.value.value.delivery.move (by rw [value.value.value.delivery.event]; trivial)
  | advanced value =>
    have mode := congrArg (fun whole : W.Monitor => whole.mode) value.value.observation.observed
    change CampusTCPTwoTransferControlState.Phase value.value.value.delivery.move.after.report.final
      (W.observe cfg monitor value.value.value.delivery.step).mode location
    rw [mode]
    exact controls.nonservice control value.value.value.delivery.move (by rw [value.value.value.delivery.event]; trivial)


theorem Received.outer_mode (record : Received active path) : (W.observe cfg monitor record.actual).mode = monitor.mode := by
  cases record with
  | zero value =>
    change (W.observe cfg monitor value.value.value.delivery.step).mode = monitor.mode
    have same := congrArg (fun whole : W.Monitor => whole.mode) value.value.observation.observed
    exact same
  | advanced value =>
    change (W.observe cfg monitor value.value.value.delivery.step).mode = monitor.mode
    have same := congrArg (fun whole : W.Monitor => whole.mode) value.value.observation.observed
    exact same


theorem Step.receive_ack (active : Active core)
    (controls : CampusTCPTwoTransferControlState.Phase current.report.final monitor.mode location)
    (path : AckLink initial current (received.bytes lower upper).length lane)
    (selected : monitor.exchange.forward.ack = some lane)
    (allowed : CampusTCPTwoTransferMonitor.Allowed cfg current.report.final monitor (.deliver path.index path.emission.bytes true))
    (actual : Step input) (before : actual.before = current.report.final)
    (event : actual.event = .deliver path.index path.emission.bytes true) :
    ∃ record : Received active path, record.actual = actual := by
  obtain ⟨record⟩ := receive_at active controls path selected allowed
  exact ⟨record, CampusTCPRoundPhaseBase.Step.eq_of_before_event record.actual actual
    (record.move.beforeEq.trans before.symm) (record.event.trans event.symm)⟩

end Netlib.Check.CampusTCPTwoTransferAckRetire
