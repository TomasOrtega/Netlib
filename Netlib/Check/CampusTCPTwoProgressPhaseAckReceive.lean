import Netlib.Check.CampusTCPTwoProgressPhaseBase
import Netlib.Check.CampusTCPTwoProgressAckReceive

/-!
# ACK receipt on the same indexed phase state

Current packet and stage relations select retirement.
Zero-count receipt needs the current duplicate count to be zero.
-/

namespace Netlib.Check.CampusTCPTwoProgressPhaseAckReceive

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressPhaseBase
open CampusTCPTwoProgressSetup (config)

namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane observe normalize)
end M
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
export CampusTCPTwoProgressAckReceive (Advanced Zero)
end A

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {sent next : S.Stage initial} {received : R.Stage} {amount : Nat} {lane : M.Lane}

private theorem emitted_retire (retiring : S.Retires sent amount next) : emitted initial sent = emitted initial next := by
  cases retiring <;> rfl

private theorem times_retire (retiring : S.Retires sent amount next) : OriginalTimes initial sent = OriginalTimes initial next := by
  cases retiring <;> rfl

private theorem retirement (core : Core initial native quantum allowance current monitor sent received)
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

private def clearRetired (history : CampusTCPTwoProgressLossHistory.History initial cfg after observed)
    (next : S.Stage initial) : CampusTCPTwoProgressLossHistory.History initial cfg after observed :=
  match next with
  | .tail .. => history.clearLower
  | .retired .. => history.clearAll
  | _ => history

def retirementBook (book : CampusTCPTwoProgressLossHistory.Book initial cfg) (next : S.Stage initial) :
    CampusTCPTwoProgressLossHistory.Book initial cfg :=
  match next with
  | .tail .. => book.clearLower
  | .retired .. => book.clearAll
  | _ => book

private theorem clearRetired_book (history : CampusTCPTwoProgressLossHistory.History initial cfg after observed)
    (next : S.Stage initial) : (clearRetired history next).book = retirementBook history.book next := by
  cases next <;> rfl

private theorem received_nonempty (core : Core initial native quantum allowance current monitor sent received)
    (different : sent.retiredBytes ≠ (received.bytes lower upper).length) : received ≠ .empty := by
  intro empty
  have bound := core.retired
  rw [empty] at bound different
  change sent.retiredBytes ≤ 0 at bound
  change sent.retiredBytes ≠ 0 at different
  omega

private theorem delivery_observed (core : Core initial native quantum allowance current monitor sent received)
    (path : P.AckLink initial current count lane)
    (delivery : CampusTCPRoundDelivery.Delivery current.report complete current.endpoints path.index path.served path.emission path.emitted)
    (active : monitor.mode = .originals ∨ monitor.mode = .recovery)
    (first : monitor.lower.phase ≠ .needSend) (second : monitor.upper.phase ≠ .needSend)
    (ack : monitor.ack = some lane)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor
      (.deliver path.index path.emission.bytes true)) :
    M.observe (config initial native quantum allowance) monitor delivery.step =
      M.normalize (config initial native quantum allowance) delivery.step.result.state
        { monitor with ack := none, ackReceipts := monitor.ackReceipts ++ [current.report.final.receipts.length] } := by
  have other : path.served.ticket.value.produced.actor.other = sender := by rw [path.actor]; cases sender <;> rfl
  have receiptActor : delivery.receipt.actor = sender := by
    rw [delivery.receipt.receiver, delivery.receiptService, other]
  have self : (sender == sender) = true := by cases sender <;> rfl
  have observed := F.observe_action (config initial native quantum allowance) monitor delivery.step
    delivery.supported delivery.passed
    (by simpa only [delivery.beforeEq, delivery.event] using allowed)
    (.deliver path.index path.emission.bytes true) delivery.event
  rw [observed, F.observe_ack _ _ _ _ active first second ack]
  simp only [CampusTCPTwoProgressMonitor.observeAck, CampusTCPTwoProgressMonitor.ackLane, path.phase,
    CampusTCPGapProgressMonitor.observeReceipt, delivery.receiptAt, delivery.recorded, other, receiptActor,
    config, CampusTCPTwoProgressMonitor.Lane.toGap, CampusTCPTwoProgressMonitor.Lane.ofGap,
    Bool.false_eq_true, ite_false, self, Bool.and_self, ite_true, F.phase_beq_self,
    delivery.beforeEq]
  rfl

private theorem delivery_counters (_core : Core initial native quantum allowance current monitor sent received)
    (path : P.AckLink initial current count lane)
    (delivery : CampusTCPRoundDelivery.Delivery current.report complete current.endpoints path.index path.served path.emission path.emitted)
    (observed : M.observe (config initial native quantum allowance) monitor delivery.step =
      M.normalize (config initial native quantum allowance) delivery.step.result.state
        { monitor with ack := none, ackReceipts := monitor.ackReceipts ++ [current.report.final.receipts.length] }) :
    (M.observe (config initial native quantum allowance) monitor delivery.step).retries = monitor.retries ∧
      (M.observe (config initial native quantum allowance) monitor delivery.step).drops = monitor.drops := by
  rw [observed]
  have frame := F.normalize_counters (config initial native quantum allowance) delivery.step.result.state
    { monitor with ack := none, ackReceipts := monitor.ackReceipts ++ [current.report.final.receipts.length] }
  exact Prod.mk.inj frame

private def literalJoint {index : Nat} {served : Served input}
    {emission : WireForwarding.Emission served.ticket.value.source.packet} {emittedProof : served.evidence.output = some emission}
    (core : Core initial native quantum allowance current monitor sent received)
    (delivery : CampusTCPRoundDelivery.Delivery current.report complete current.endpoints index served emission emittedProof)
    (move : CampusTCPRoundPhaseBase.Move current delivery.step) (updated : move.after.endpoints = delivery.updated)
    (actor : served.ticket.value.produced.actor.other = sender)
    (flight : CampusTCPTwoProgressSender.Flight initial (endpoint move.after.endpoints sender) next retries) :
    CampusTCPTwoProgressState.Live initial move.after next retries received := by
  have peer : endpoint move.after.endpoints sender.other = endpoint current.endpoints sender.other := by
    rw [updated]
    simpa only [actor] using delivery.peer
  let receiver : CampusTCPTwoProgressReceiver.Facts initial (endpoint move.after.endpoints sender.other) received :=
    peer.symm ▸ core.live.receiverFacts
  have environment : CampusTCPRoundEnvironment.environment current.report.final =
      CampusTCPRoundEnvironment.environment move.after.report.final := by
    rw [move.final]
    exact delivery.environment
  have gatewayFrame : beforeService input move.after.report.final gateway = beforeService input current.report.final gateway := by
    rw [move.final, CampusTCPRoundLocal.step_service_nonservice delivery.step (by rw [delivery.event]; trivial), delivery.beforeEq]
  have operations : applicationSteps move.after.endpoints sender.other = applicationSteps current.endpoints sender.other := by
    rw [updated]
    simpa only [actor] using delivery.peerSteps
  exact ⟨⟨CampusTCPTwoProgressState.endpoint_guards flight receiver, core.live.anchor.retained.trans move.retained,
    core.live.anchor.environment.trans environment⟩, flight, receiver, core.live.gatewayState.reframe gatewayFrame,
    core.live.gatewayWindow, core.live.history.same operations⟩

structure Advanced (core : Core initial native quantum allowance current monitor sent received)
    (path : P.AckLink initial current (received.bytes lower upper).length lane) where
  nextStage : S.Stage initial
  amount : Nat
  value : A.Advanced core.live nextStage amount path.index path.served path.emission path.emitted
  coordinate : nextStage.retiredBytes = (received.bytes lower upper).length
  observed : M.observe (config initial native quantum allowance) monitor value.delivery.step =
    M.normalize (config initial native quantum allowance) value.delivery.step.result.state
      { monitor with ack := none, ackReceipts := monitor.ackReceipts ++ [current.report.final.receipts.length] }
  nextCore : Core initial native quantum allowance value.delivery.move.after
    (M.observe (config initial native quantum allowance) monitor value.delivery.step) nextStage received
  duplicates : nextCore.live.senderFlight.recovery.duplicateAcks = 0
  losses : nextCore.losses.book = retirementBook core.losses.book nextStage

structure Zero (core : Core initial native quantum allowance current monitor sent received)
    (path : P.AckLink initial current (received.bytes lower upper).length lane) where
  value : A.Zero core.live path.index path.served path.emission path.emitted
  observed : M.observe (config initial native quantum allowance) monitor value.delivery.step =
    M.normalize (config initial native quantum allowance) value.delivery.step.result.state
      { monitor with ack := none, ackReceipts := monitor.ackReceipts ++ [current.report.final.receipts.length] }
  nextCore : Core initial native quantum allowance value.delivery.move.after
    (M.observe (config initial native quantum allowance) monitor value.delivery.step) sent received
  duplicates : nextCore.live.senderFlight.recovery.duplicateAcks =
    if Endpoint.qualifyingDuplicate (endpoint current.endpoints sender) path.emission.asInput.packet.segment 0 then 1 else 0
  losses : nextCore.losses.book = core.losses.book

private theorem retirement_envelope (core : Core initial native quantum allowance current monitor sent received)
    (retiring : S.Retires sent amount next) {packet : Endpoint.Input} {after : Endpoint.State}
    (protocol : Endpoint.AdvancingAck (endpoint current.endpoints sender) packet core.live.senderFlight.recovery after)
    (counted : Endpoint.inOrderCount (endpoint current.endpoints sender) packet = amount)
    (pending : next.ledger ≠ []) :
    RTOEnvelope.Bound initial.senderState.idle.recovery.rto initial.senderState.idle.recovery.estimator
      (endpoint cut.endpoints sender).now monitor.retries
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

theorem advancing_at (core : Core initial native quantum allowance current monitor sent received)
    (path : P.AckLink initial current (received.bytes lower upper).length lane)
    (recovering : sent.preparing = false) (different : sent.retiredBytes ≠ (received.bytes lower upper).length)
    (active : monitor.mode = .originals ∨ monitor.mode = .recovery)
    (first : monitor.lower.phase ≠ .needSend) (second : monitor.upper.phase ≠ .needSend)
    (ack : monitor.ack = some lane)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor
      (.deliver path.index path.emission.bytes true)) : Nonempty (Advanced core path) := by
  obtain ⟨amount, next, retiring, coordinate⟩ := retirement core recovering different
  have fields : CampusTCPTwoProgressWire.AckFields initial next.retiredBytes path.served.ticket.value.produced :=
    coordinate.symm ▸ path.fields
  obtain ⟨value⟩ := CampusTCPTwoProgressAckReceive.advancing_at (emitted := path.emitted) core.live core.senderWindow retiring
    path.stored path.actor path.application path.toLink.pending fields path.target
  have observed := delivery_observed core path value.delivery.toDelivery active first second ack allowed
  have counters := delivery_counters core path value.delivery.toDelivery observed
  let flight : CampusTCPTwoProgressSender.Flight initial (endpoint value.delivery.move.after.endpoints sender) next
      (M.observe (config initial native quantum allowance) monitor value.delivery.step).retries := by
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
      (by simp only [CampusTCPTwoProgressLossHistory.isTimeout, value.delivery.event]) counters.2 counters.1
  have notEmpty := received_nonempty core different
  let after : Core initial native quantum allowance value.delivery.move.after
      (M.observe (config initial native quantum allowance) monitor value.delivery.step) next received := {
    live := joint
    senderWindow := value.space
    originals := (core.originals.retain_steps value.delivery.move.retained).retire retiring
    originalTimes := (times_retire retiring) ▸ core.originalTimes
    writer := (emitted_retire retiring) ▸ writer
    losses := clearRetired losses next
    lossBound := counters.2.symm ▸ core.lossBound
    retired := Nat.le_of_eq coordinate
    gatewayAck := core.gatewayAck
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
  exact ⟨⟨next, amount, value, coordinate, observed, after, duplicate, clearRetired_book losses next⟩⟩

theorem zero_at (core : Core initial native quantum allowance current monitor sent received)
    (path : P.AckLink initial current (received.bytes lower upper).length lane)
    (recovering : sent.preparing = false) (equal : sent.retiredBytes = (received.bytes lower upper).length)
    (duplicate : core.live.senderFlight.recovery.duplicateAcks = 0) (notEmpty : received ≠ .empty)
    (active : monitor.mode = .originals ∨ monitor.mode = .recovery)
    (first : monitor.lower.phase ≠ .needSend) (second : monitor.upper.phase ≠ .needSend)
    (ack : monitor.ack = some lane)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor
      (.deliver path.index path.emission.bytes true)) : Nonempty (Zero core path) := by
  have fields : CampusTCPTwoProgressWire.AckFields initial sent.retiredBytes path.served.ticket.value.produced := equal.symm ▸ path.fields
  obtain ⟨value⟩ := CampusTCPTwoProgressAckReceive.zero_at (emitted := path.emitted) core.live core.senderWindow recovering
    path.stored path.actor path.application path.toLink.pending fields path.target (by intro _; rw [duplicate]; decide)
  have observed := delivery_observed core path value.delivery.toDelivery active first second ack allowed
  have counters := delivery_counters core path value.delivery.toDelivery observed
  let flight : CampusTCPTwoProgressSender.Flight initial (endpoint value.delivery.move.after.endpoints sender) sent
      (M.observe (config initial native quantum allowance) monitor value.delivery.step).retries := by
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
  let after : Core initial native quantum allowance value.delivery.move.after
      (M.observe (config initial native quantum allowance) monitor value.delivery.step) sent received := {
    live := joint
    senderWindow := value.space
    originals := core.originals.retain_steps value.delivery.move.retained
    originalTimes := core.originalTimes
    writer := core.writer.quiet value.delivery.localStep operations quiet.1 quiet.2
    losses := core.losses.append value.delivery.move
      (by simp only [CampusTCPTwoProgressLossHistory.isDrop, value.delivery.event])
      (by simp only [CampusTCPTwoProgressLossHistory.isTimeout, value.delivery.event]) counters.2 counters.1
    lossBound := counters.2.symm ▸ core.lossBound
    retired := core.retired
    gatewayAck := core.gatewayAck
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
  exact ⟨⟨value, observed, after, actualDuplicate, rfl⟩⟩

theorem Step.advancing (actual : Step input) (core : Core initial native quantum allowance current monitor sent received)
    (path : P.AckLink initial current (received.bytes lower upper).length lane)
    (recovering : sent.preparing = false) (different : sent.retiredBytes ≠ (received.bytes lower upper).length)
    (active : monitor.mode = .originals ∨ monitor.mode = .recovery)
    (first : monitor.lower.phase ≠ .needSend) (second : monitor.upper.phase ≠ .needSend) (ack : monitor.ack = some lane)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor
      (.deliver path.index path.emission.bytes true))
    (before : actual.before = current.report.final) (event : actual.event = .deliver path.index path.emission.bytes true) :
    ∃ result : Advanced core path, result.value.delivery.step = actual := by
  obtain ⟨result⟩ := advancing_at core path recovering different active first second ack allowed
  exact ⟨result, CampusTCPRoundPhaseBase.Step.eq_of_before_event result.value.delivery.step actual
    (result.value.delivery.beforeEq.trans before.symm) (result.value.delivery.event.trans event.symm)⟩

theorem Step.zero (actual : Step input) (core : Core initial native quantum allowance current monitor sent received)
    (path : P.AckLink initial current (received.bytes lower upper).length lane)
    (recovering : sent.preparing = false) (equal : sent.retiredBytes = (received.bytes lower upper).length)
    (duplicate : core.live.senderFlight.recovery.duplicateAcks = 0) (notEmpty : received ≠ .empty)
    (active : monitor.mode = .originals ∨ monitor.mode = .recovery)
    (first : monitor.lower.phase ≠ .needSend) (second : monitor.upper.phase ≠ .needSend) (ack : monitor.ack = some lane)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor
      (.deliver path.index path.emission.bytes true))
    (before : actual.before = current.report.final) (event : actual.event = .deliver path.index path.emission.bytes true) :
    ∃ result : Zero core path, result.value.delivery.step = actual := by
  obtain ⟨result⟩ := zero_at core path recovering equal duplicate notEmpty active first second ack allowed
  exact ⟨result, CampusTCPRoundPhaseBase.Step.eq_of_before_event result.value.delivery.step actual
    (result.value.delivery.beforeEq.trans before.symm) (result.value.delivery.event.trans event.symm)⟩

end Netlib.Check.CampusTCPTwoProgressPhaseAckReceive
