import Netlib.Check.CampusTCPTwoTransferAckReceiveObserve

/-!
# ACK receipt on the same indexed phase state

Current packet and stage relations select retirement.
Zero-count receipt needs the current duplicate count to be zero.
-/

namespace Netlib.Check.CampusTCPTwoTransferAckReceiveCore

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (emitted OriginalTimes stage_prefix)
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferPhaseState (Active)

namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane observe normalize)
end M
namespace W
export CampusTCPTwoTransferMonitor (Monitor observe Allowed)
end W
namespace O
export CampusTCPTwoTransferAckReceiveObserve (Observed ackCleared)
end O
namespace F
export CampusTCPTwoProgressMonitorFacts
  (observe_action observe_ack phase_beq_self normalize_counters)
end F
namespace S
export CampusTCPTwoProgressSender (Stage Retires)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
namespace P
export CampusTCPTwoProgressPaths (AckLink)
end P
namespace A
export CampusTCPTwoTransferLocatedAckReceive (Advanced Zero)
end A

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {sent next : S.Stage initial} {received : R.Stage} {amount : Nat} {lane : M.Lane}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper
local notation "localCfg" => CampusTCPTwoExchangeMonitor.Config.forward
  (CampusTCPTwoTransferMonitor.Config.at
    (config initial checks routing quantum allowance reverseLower reverseUpper) current.report.final)

private theorem emitted_retire (retiring : S.Retires sent amount next) : emitted initial sent = emitted initial next := by
  cases retiring <;> rfl

private theorem times_retire (retiring : S.Retires sent amount next) : OriginalTimes initial sent = OriginalTimes initial next := by
  cases retiring <;> rfl

private theorem retirement (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (recovering : sent.preparing = false) (different : sent.retiredBytes ≠ (received.bytes lower upper).length) :
    ∃ amount next, S.Retires sent amount next ∧ next.retiredBytes = (received.bytes lower upper).length := by
  have positive : sent.retiredBytes < (received.bytes lower upper).length := by
    have bounded := core.retired
    omega
  have bounded := (stage_prefix (lower := lower) (upper := upper) received).length_le
  simp only [List.length_append] at bounded
  cases sent with
  | written => cases recovering
  | lower first => cases recovering
  | both first second head =>
    cases received with
    | empty | upperHeld => cases positive
    | lowerReleased => exact ⟨lower.length, .tail first second second.entry, .lower first second head, rfl⟩
    | allReleased => exact ⟨lower.length + upper.length, .retired first second, .both first second head, List.length_append.symm⟩
  | tail first second head =>
    cases received with
    | empty | upperHeld => simp only [CampusTCPTwoProgressReceiver.Stage.bytes, List.length_nil] at positive; omega
    | lowerReleased => exact False.elim (Nat.lt_irrefl _ positive)
    | allReleased => exact ⟨upper.length, .retired first second, .tail first second head, List.length_append.symm⟩
  | retired first second =>
    change lower.length + upper.length < _ at positive
    omega

private def clearRetired (history : CampusTCPTwoTransferLossHistory.History initial cfg after observed)
    (next : S.Stage initial) : CampusTCPTwoTransferLossHistory.History initial cfg after observed :=
  match next with
  | .tail .. => { history with book := history.book.clearLower, valid := history.valid.clearLower }
  | .retired .. => { history with book := history.book.clearAll, valid := history.valid.clearAll }
  | _ => history

def retirementBook (book : CampusTCPTwoTransferLoss.Book initial cfg) (next : S.Stage initial) :
    CampusTCPTwoTransferLoss.Book initial cfg :=
  match next with
  | .tail .. => book.clearLower
  | .retired .. => book.clearAll
  | _ => book

private theorem clearRetired_book (history : CampusTCPTwoTransferLossHistory.History initial cfg after observed)
    (next : S.Stage initial) : (clearRetired history next).book = retirementBook history.book next := by
  cases next <;> rfl

private theorem received_nonempty (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (different : sent.retiredBytes ≠ (received.bytes lower upper).length) : received ≠ .empty := by
  intro empty
  have bound := core.retired
  rw [empty] at bound different
  change sent.retiredBytes ≤ 0 at bound
  change sent.retiredBytes ≠ 0 at different
  omega

private def literalJoint {index : Nat} {served : Served input}
    {emission : WireForwarding.Emission served.ticket.value.source.packet} {emittedProof : served.evidence.output = some emission}
    (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (delivery : CampusTCPRoundDelivery.Delivery current.report complete current.endpoints index served emission emittedProof)
    (move : CampusTCPRoundPhaseBase.Move current delivery.step) (updated : move.after.endpoints = delivery.updated)
    (actor : served.ticket.value.produced.actor.other = sender)
    (flight : CampusTCPTwoProgressSender.Flight initial (endpoint move.after.endpoints sender) next retries) :
    CampusTCPTwoTransferState.LiveAt initial move.after location next retries received := by
  have peer : endpoint move.after.endpoints sender.other = endpoint current.endpoints sender.other := by
    rw [updated]
    simpa only [actor] using delivery.peer
  let receiver : CampusTCPTwoProgressReceiver.Facts initial (endpoint move.after.endpoints sender.other) received :=
    peer.symm ▸ core.live.receiverFacts
  have gatewayFrame (selected) : beforeService input move.after.report.final selected = beforeService input current.report.final selected := by
    rw [move.final, CampusTCPRoundLocal.step_service_nonservice delivery.step (by rw [delivery.event]; trivial), delivery.beforeEq]
  have operations : applicationSteps move.after.endpoints sender.other = applicationSteps current.endpoints sender.other := by
    rw [updated]
    simpa only [actor] using delivery.peerSteps
  exact ⟨⟨⟨core.live.anchor.retained.trans move.retained,
    fun selected => (core.live.anchor.policy selected).trans
      (congrArg CampusTCPService.Before.environment (gatewayFrame selected)).symm⟩,
    CampusTCPTwoProgressState.endpoint_guards flight receiver⟩,
    flight, receiver, core.live.gatewayState.reframe (gatewayFrame location), core.live.gatewayWindow, core.live.history.same operations⟩

private theorem delivery_queue (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received) (path : P.AckLink initial current count lane)
    (delivery : CampusTCPRoundDelivery.Delivery current.report complete current.endpoints path.index path.served path.emission path.emitted)
    (move : CampusTCPRoundPhaseBase.Move current delivery.step) (observation : O.Observed core path delivery) :
    CampusTCPTwoTransferQueue.Closed move.after.report.final (W.observe cfg monitor delivery.step).exchange.forward := by
  have queue : CampusTCPTwoTransferQueue.Closed move.after.report.final monitor.exchange.forward := by
    apply core.primaryQueue.work_same
    rw [move.final, CampusTCPTwoProgressPathRetain.Step.work_quiet delivery.step (by rw [delivery.event]; trivial), delivery.beforeEq]
  rw [observation.observed]
  have lanes := CampusTCPTwoProgressMonitorFacts.normalize_lanes localCfg delivery.step.result.state
    (O.ackCleared monitor.exchange.forward current.report.final.receipts.length)
  exact queue.reframe (congrArg (fun lane : M.Lane => lane.phase) lanes.1) (congrArg (fun lane : M.Lane => lane.refs.dataTicket) lanes.1)
    (congrArg (fun lane : M.Lane => lane.phase) lanes.2.1) (congrArg (fun lane : M.Lane => lane.refs.dataTicket) lanes.2.1)

structure Advanced (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (path : P.AckLink initial current (received.bytes lower upper).length lane) where
  nextStage : S.Stage initial
  amount : Nat
  value : A.Advanced core.live nextStage amount path.index path.served path.emission path.emitted
  coordinate : nextStage.retiredBytes = (received.bytes lower upper).length
  observation : O.Observed core path value.delivery.toDelivery
  nextCore : Core initial checks routing quantum allowance reverseLower reverseUpper value.delivery.move.after
    (W.observe cfg monitor value.delivery.step) location nextStage received
  duplicates : nextCore.live.senderFlight.recovery.duplicateAcks = 0
  losses : nextCore.losses.book = retirementBook core.losses.book nextStage

structure Zero (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (path : P.AckLink initial current (received.bytes lower upper).length lane) where
  value : A.Zero core.live path.index path.served path.emission path.emitted
  observation : O.Observed core path value.delivery.toDelivery
  nextCore : Core initial checks routing quantum allowance reverseLower reverseUpper value.delivery.move.after
    (W.observe cfg monitor value.delivery.step) location sent received
  duplicates : nextCore.live.senderFlight.recovery.duplicateAcks =
    if Endpoint.qualifyingDuplicate (endpoint current.endpoints sender) path.emission.asInput.packet.segment 0 then 1 else 0
  losses : nextCore.losses.book = core.losses.book

private theorem retirement_envelope (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (retiring : S.Retires sent amount next) {packet : Endpoint.Input} {after : Endpoint.State}
    (protocol : Endpoint.AdvancingAck (endpoint current.endpoints sender) packet core.live.senderFlight.recovery after)
    (counted : Endpoint.inOrderCount (endpoint current.endpoints sender) packet = amount)
    (pending : next.ledger ≠ []) :
    RTOEnvelope.Bound initial.senderState.idle.recovery.rto initial.senderState.idle.recovery.estimator
      (endpoint cut.endpoints sender).now monitor.exchange.forward.retries
      (Endpoint.advancingAckRecovery (endpoint current.endpoints sender) packet core.live.senderFlight.recovery) := by
  cases retiring with
  | lower first second head =>
    have size := congrArg Recovery.Outstanding.count core.live.senderFlight.headFixed
    have countedHead : Endpoint.inOrderCount (endpoint current.endpoints sender) packet = head.count := counted.trans size.symm
    have now := (protocol.head_fields head [second.entry] core.live.senderFlight.ledger countedHead).2.1
    cases retried : head.retried with
    | true =>
      have fields := protocol.head_retried head [second.entry] core.live.senderFlight.ledger countedHead retried
      exact RTOEnvelope.transport (core.rtoPending (by intro impossible; cases impossible)) fields.2.2 now
    | false =>
      have fields := protocol.head_fresh head [second.entry] core.live.senderFlight.ledger countedHead retried
      have estimator := core.estimatorBeforeRetire rfl
      rw [estimator] at fields
      have sentAt := congrArg Recovery.Outstanding.sentAt core.live.senderFlight.headFixed
      change head.sentAt = first.operation.before.now at sentAt
      have past := core.originalTimes.1
      apply RTOEnvelope.observed (core.live.senderFlight.recovery.now - head.sentAt) fields.2.2
      rw [now]
      omega
  | both => exact False.elim (pending rfl)
  | tail => exact False.elim (pending rfl)

theorem advancing_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (path : P.AckLink initial current (received.bytes lower upper).length lane)
    (recovering : sent.preparing = false) (different : sent.retiredBytes ≠ (received.bytes lower upper).length)
    (active : Active core)
    (controls : CampusTCPTwoTransferControlState.Phase current.report.final monitor.mode location)
    (ack : monitor.exchange.forward.ack = some lane)
    (allowed : W.Allowed cfg current.report.final monitor
      (.deliver path.index path.emission.bytes true)) : Nonempty (Advanced core path) := by
  obtain ⟨amount, next, retiring, coordinate⟩ := retirement core recovering different
  have fields : CampusTCPTwoProgressWire.AckFields initial next.retiredBytes path.served.ticket.value.produced :=
    coordinate.symm ▸ path.fields
  obtain ⟨value⟩ := CampusTCPTwoTransferLocatedAckReceive.advancing_at (emitted := path.emitted) core.live core.senderWindow retiring
    path.stored path.actor path.application path.toLink.pending fields path.target
  have observation := CampusTCPTwoTransferAckReceiveObserve.advancing core active path value controls ack allowed
  have counters := And.intro observation.retries observation.drops
  let flight : CampusTCPTwoProgressSender.Flight initial (endpoint value.delivery.move.after.endpoints sender) next
      (W.observe cfg monitor value.delivery.step).exchange.forward.retries := by
    rw [counters.1]
    exact value.joint.senderFlight
  have other : path.served.ticket.value.produced.actor.other = sender := by rw [path.actor]; cases sender <;> rfl
  let joint := literalJoint core value.delivery.toDelivery value.delivery.move rfl other flight
  have selected : endpoint value.delivery.move.after.endpoints sender = value.delivery.after := by
    change endpoint value.delivery.updated sender = value.delivery.after
    simpa only [other] using value.delivery.selected
  have runtime : joint.senderFlight.recovery = Endpoint.advancingAckRecovery (endpoint current.endpoints sender)
      path.emission.asInput core.live.senderFlight.recovery := by
    apply Option.some.inj
    exact joint.senderFlight.runtime.symm.trans (by rw [selected]; exact value.protocol.runtime)
  have duplicate : joint.senderFlight.recovery.duplicateAcks = 0 := by
    rw [runtime]
    have positive := value.protocol.count_positive
    simp only [Endpoint.advancingAckRecovery, Recovery.acknowledgeState, Nat.ne_of_gt positive, ite_false]
  have operations : applicationSteps value.delivery.move.after.endpoints sender =
      applicationSteps current.endpoints sender ++ [value.delivery.localStep] := by
    change applicationSteps value.delivery.updated sender = _
    simpa only [other] using value.delivery.selectedSteps
  have quiet := CampusTCPTwoProgressWriteHistory.receive_quiet value.delivery.localStep value.delivery.localEvent
  let writer := core.writer.quiet value.delivery.localStep operations quiet.1 quiet.2
  let losses := core.losses.append value.delivery.move
    (by simp only [CampusTCPTwoProgressLossHistory.isDrop, value.delivery.event])
      (by simp only [CampusTCPTwoExchangeLoss.isTimeoutOutput, value.delivery.event]) counters.2 counters.1 observation.wholeDrops observation.timeouts
  have notEmpty := received_nonempty core different
  let after : Core initial checks routing quantum allowance reverseLower reverseUpper value.delivery.move.after
      (W.observe cfg monitor value.delivery.step) location next received := {
    live := joint
    senderWindow := value.space
    originals := (core.originals.retain_steps value.delivery.move.retained).retire retiring
    originalTimes := (times_retire retiring) ▸ core.originalTimes
    writer := (emitted_retire retiring) ▸ writer
    losses := clearRetired losses next
    lossBound := counters.2.symm ▸ core.lossBound
    primaryQueue := delivery_queue core path value.delivery.toDelivery value.delivery.move observation
    retired := Nat.le_of_eq coordinate
    gatewayAck := core.gatewayAck
    peerSettled := core.peerSettled, peerWindow := core.peerWindow
    covered := core.covered
    duplicates := by rw [duplicate]; decide
    emptyDuplicate := fun empty => False.elim (notEmpty empty)
    deadline := by
      rw [runtime]
      exact RecoveryDeadline.positive_ack _ _ value.protocol.count_positive
    estimatorBeforeRetire := by
      intro zero
      have bounded := core.retired
      rw [coordinate] at zero
      omega
    rtoBeforeRetire := by
      intro zero
      have bounded := core.retired
      rw [coordinate] at zero
      omega
    rtoPending := by
      intro pending
      rw [runtime, counters.1]
      exact retirement_envelope core retiring value.protocol value.counted pending }
  exact ⟨⟨next, amount, value, coordinate, observation, after, duplicate, clearRetired_book losses next⟩⟩

theorem zero_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (path : P.AckLink initial current (received.bytes lower upper).length lane)
    (recovering : sent.preparing = false) (equal : sent.retiredBytes = (received.bytes lower upper).length)
    (duplicate : core.live.senderFlight.recovery.duplicateAcks = 0) (notEmpty : received ≠ .empty)
    (active : Active core)
    (controls : CampusTCPTwoTransferControlState.Phase current.report.final monitor.mode location)
    (ack : monitor.exchange.forward.ack = some lane)
    (allowed : W.Allowed cfg current.report.final monitor
      (.deliver path.index path.emission.bytes true)) : Nonempty (Zero core path) := by
  have fields : CampusTCPTwoProgressWire.AckFields initial sent.retiredBytes path.served.ticket.value.produced := equal.symm ▸ path.fields
  obtain ⟨value⟩ := CampusTCPTwoTransferLocatedAckReceive.zero_at (emitted := path.emitted) core.live core.senderWindow recovering
    path.stored path.actor path.application path.toLink.pending fields path.target (by intro _; rw [duplicate]; decide)
  have observation := CampusTCPTwoTransferAckReceiveObserve.zero core active path value controls ack allowed
  have counters := And.intro observation.retries observation.drops
  let flight : CampusTCPTwoProgressSender.Flight initial (endpoint value.delivery.move.after.endpoints sender) sent
      (W.observe cfg monitor value.delivery.step).exchange.forward.retries := by
    rw [counters.1]
    exact value.joint.senderFlight
  have other : path.served.ticket.value.produced.actor.other = sender := by rw [path.actor]; cases sender <;> rfl
  let joint := literalJoint core value.delivery.toDelivery value.delivery.move rfl other flight
  have selected : endpoint value.delivery.move.after.endpoints sender = value.delivery.after := by
    change endpoint value.delivery.updated sender = value.delivery.after
    simpa only [other] using value.delivery.selected
  have runtime : joint.senderFlight.recovery = Endpoint.zeroAckRecovery (endpoint current.endpoints sender)
      path.emission.asInput core.live.senderFlight.recovery := by
    apply Option.some.inj
    exact joint.senderFlight.runtime.symm.trans (by rw [selected]; exact value.protocol.runtime)
  have actualDuplicate : joint.senderFlight.recovery.duplicateAcks =
      if Endpoint.qualifyingDuplicate (endpoint current.endpoints sender) path.emission.asInput.packet.segment 0 then 1 else 0 := by
    rw [runtime]
    unfold Endpoint.zeroAckRecovery
    split <;> simp only [duplicate] <;> rfl
  have bound : joint.senderFlight.recovery.duplicateAcks ≤ 1 := by
    rw [actualDuplicate]
    split <;> decide
  have operations : applicationSteps value.delivery.move.after.endpoints sender =
      applicationSteps current.endpoints sender ++ [value.delivery.localStep] := by
    change applicationSteps value.delivery.updated sender = _
    simpa only [other] using value.delivery.selectedSteps
  have quiet := CampusTCPTwoProgressWriteHistory.receive_quiet value.delivery.localStep value.delivery.localEvent
  let after : Core initial checks routing quantum allowance reverseLower reverseUpper value.delivery.move.after
      (W.observe cfg monitor value.delivery.step) location sent received := {
    live := joint
    senderWindow := value.space
    originals := core.originals.retain_steps value.delivery.move.retained
    originalTimes := core.originalTimes
    writer := core.writer.quiet value.delivery.localStep operations quiet.1 quiet.2
    losses := core.losses.append value.delivery.move
      (by simp only [CampusTCPTwoProgressLossHistory.isDrop, value.delivery.event])
      (by simp only [CampusTCPTwoExchangeLoss.isTimeoutOutput, value.delivery.event]) counters.2 counters.1 observation.wholeDrops observation.timeouts
    lossBound := counters.2.symm ▸ core.lossBound
    primaryQueue := delivery_queue core path value.delivery.toDelivery value.delivery.move observation
    retired := core.retired
    gatewayAck := core.gatewayAck
    peerSettled := core.peerSettled, peerWindow := core.peerWindow
    covered := core.covered
    duplicates := bound
    emptyDuplicate := fun empty => False.elim (notEmpty empty)
    deadline := by
      rw [runtime]
      unfold Endpoint.zeroAckRecovery
      split <;> exact core.deadline
    estimatorBeforeRetire := by
      intro zero
      rw [runtime]
      unfold Endpoint.zeroAckRecovery
      split <;> exact core.estimatorBeforeRetire zero
    rtoBeforeRetire := by
      intro zero
      rw [runtime, counters.1]
      unfold Endpoint.zeroAckRecovery
      split <;> exact core.rtoBeforeRetire zero
    rtoPending := by
      intro pending
      rw [runtime, counters.1]
      unfold Endpoint.zeroAckRecovery
      split <;> exact core.rtoPending pending }
  exact ⟨⟨value, observation, after, actualDuplicate, rfl⟩⟩

theorem Advanced.observed {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}
    {path : P.AckLink initial current (received.bytes lower upper).length lane} (value : Advanced core path) :
    (W.observe cfg monitor value.value.delivery.step).exchange.forward =
      M.normalize localCfg value.value.delivery.step.result.state
        (O.ackCleared monitor.exchange.forward current.report.final.receipts.length) :=
  congrArg (fun whole : W.Monitor => whole.exchange.forward) value.observation.observed

theorem Zero.observed {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}
    {path : P.AckLink initial current (received.bytes lower upper).length lane} (value : Zero core path) :
    (W.observe cfg monitor value.value.delivery.step).exchange.forward =
      M.normalize localCfg value.value.delivery.step.result.state
        (O.ackCleared monitor.exchange.forward current.report.final.receipts.length) :=
  congrArg (fun whole : W.Monitor => whole.exchange.forward) value.observation.observed

end Netlib.Check.CampusTCPTwoTransferAckReceiveCore
