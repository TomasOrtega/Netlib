import Netlib.Protocol.TCP.EndpointAckReceiveEnabled
import Netlib.Protocol.TCP.RecoveryHeadAckEnabled

namespace Netlib.Protocol.TCP.Endpoint

structure AdvancingAckConditions (state : State) (input : Input)
    (recovery : Recovery.State) (reaction : AckReaction.State) : Prop where
  valid : state.Valid
  coherent : RecoveryCoherent state
  prepared : AckPrepared state
  storage : StorageCoherent state
  runtime : state.recovery = some recovery
  ackRuntime : state.ackReaction = some reaction
  tuple : input.packet.header = state.core.inbound
  controls : EstablishedReceive.control input.packet.segment = none
  ack : Flags.ack input.packet.segment.flags = true
  sequence : input.packet.segment.sequence = state.core.receiveNext
  empty : input.packet.segment.payload = []
  positive : 0 < inOrderCount state input
  bounded : inOrderCount state input ≤ state.core.sent.length

def advancingAckRecovery (state : State) (input : Input) (recovery : Recovery.State) : Recovery.State :=
  Recovery.acknowledgeState recovery (inOrderCount state input)

def advancingAckState (state : State) (input : Input) (recovery : Recovery.State) : State :=
  inOrderReceivedWith state input (advancingAckRecovery state input recovery)

structure AdvancingAck (state : State) (input : Input) (recovery : Recovery.State) (after : State) : Prop where
  conditions : ∃ reaction, AdvancingAckConditions state input recovery reaction
  afterEq : after = advancingAckState state input recovery
  acknowledged : Recovery.acknowledge recovery (inOrderCount state input) = .ok (advancingAckRecovery state input recovery)
  effect : receiveEffect state input = receivePlain
    ⟨after, .accepted (.receive (inOrderCount state input) 0), none, [], none⟩
  valid : after.Valid
  coherent : RecoveryCoherent after
  prepared : AckPrepared after
  storage : StorageCoherent after
  runtime : after.recovery = some (advancingAckRecovery state input recovery)

variable {state after : State} {input : Input} {recovery : Recovery.State} {reaction : AckReaction.State}

private theorem recovery_reset (value : Recovery.State) (zero : value.duplicateAcks = 0) :
    { value with duplicateAcks := 0 } = value := by
  cases value
  cases zero
  rfl

private theorem advancingAckRecovery_reset (positive : 0 < inOrderCount state input) :
    { advancingAckRecovery state input recovery with duplicateAcks := 0 } = advancingAckRecovery state input recovery := by
  apply recovery_reset
  simp only [advancingAckRecovery, Recovery.acknowledgeState, Nat.ne_of_gt positive, ite_false]

theorem receive_advancing_ack_enabled (conditions : AdvancingAckConditions state input recovery reaction) :
    ∃ after, AdvancingAck state input recovery after := by
  have old : recovery.Valid ∧ recovery.smss = state.effectiveMSS ∧
      Recovery.flight recovery = state.core.sent.length ∧ AckWindowKnown state := by
    simpa only [RecoveryCoherent, conditions.runtime] using conditions.coherent
  have bounded : inOrderCount state input ≤ Recovery.flight recovery := by
    rw [old.2.2.1]
    exact conditions.bounded
  have accepted : Recovery.acknowledge recovery (inOrderCount state input) = .ok (advancingAckRecovery state input recovery) :=
    Recovery.acknowledge_of_bounded recovery _ bounded
  have nextValid := Recovery.acknowledgeState_valid recovery (inOrderCount state input) old.1
  have nextMSS : (advancingAckRecovery state input recovery).smss = state.effectiveMSS :=
    (Recovery.acknowledgeState_smss recovery _).trans old.2.1
  have nextFlight : Recovery.flight (advancingAckRecovery state input recovery) =
      state.core.sent.length - inOrderCount state input := by
    rw [advancingAckRecovery, Recovery.acknowledgeState_flight, old.2.2.1]
  have parsed := prepare_empty_forward state input conditions.valid conditions.tuple conditions.controls conditions.ack
    conditions.sequence conditions.empty conditions.bounded
  have computed := receiveInOrder_empty_of_acknowledged state input recovery (advancingAckRecovery state input recovery)
    reaction conditions.valid conditions.coherent conditions.prepared.1 conditions.runtime conditions.ackRuntime
    conditions.tuple conditions.controls conditions.ack conditions.sequence conditions.empty conditions.bounded conditions.positive accepted
  have raw : receiveRaw state input = receivePlain
      ⟨advancingAckState state input recovery, .accepted (.receive (inOrderCount state input) 0), none, [], none⟩ := by
    simp only [receiveRaw, conditions.valid, conditions.coherent, conditions.prepared.1, conditions.storage,
      not_true_eq_false, ite_false, parsed, computed, advancingAckState]
  have valid : (advancingAckState state input recovery).Valid :=
    inOrderReceivedWith_valid state input _ conditions.valid (by rw [conditions.empty]; exact Nat.zero_le _) conditions.bounded
  have coherent : RecoveryCoherent (advancingAckState state input recovery) :=
    inOrderReceivedWith_recovery state input _ nextValid nextMSS nextFlight
  have prepared : AckPrepared (advancingAckState state input recovery) :=
    inOrderReceivedWith_prepared_empty state input recovery _ reaction conditions.prepared conditions.runtime
      conditions.ackRuntime conditions.empty (Recovery.acknowledgeState_now recovery _)
  have storage : StorageCoherent (advancingAckState state input recovery) :=
    inOrderReceivedWith_storage_empty state input _ conditions.empty conditions.storage
  have runtime : (advancingAckState state input recovery).recovery = some (advancingAckRecovery state input recovery) := by
    change (inOrderReceivedWith state input (advancingAckRecovery state input recovery)).recovery = _
    rw [inOrderReceivedWith, windowState_recovery, advancingAckRecovery_reset conditions.positive]
  generalize changed : advancingAckState state input recovery = after at raw valid coherent prepared storage runtime
  refine ⟨after, ⟨⟨reaction, conditions⟩, changed.symm, accepted, ?_, valid, coherent, prepared, storage, runtime⟩⟩
  simp only [receiveEffect, raw, receivePlain, valid, storage.1, and_self, ite_true]

theorem AdvancingAck.receive (received : AdvancingAck state input recovery after) :
    receive state input =
      ⟨after, .accepted (.receive (inOrderCount state input) 0), none, [], none⟩ :=
  congrArg ReceiveEffect.result received.effect

theorem AdvancingAck.runs (received : AdvancingAck state input recovery after) : receiveRuns state input = [] :=
  congrArg ReceiveEffect.runs received.effect

theorem AdvancingAck.bytes (received : AdvancingAck state input recovery after) : receivedBytes state input = [] := by
  change ReceiveStore.bytes (receiveEffect state input).runs = []
  rw [received.effect]
  rfl

theorem AdvancingAck.core (received : AdvancingAck state input recovery after) :
    after.core = EstablishedReceive.commit state.core [] (inOrderCount state input) := by
  obtain ⟨reaction, conditions⟩ := received.conditions
  rw [received.afterEq]
  unfold advancingAckState inOrderReceivedWith
  rw [windowState_core]
  simp only [inOrderCore, conditions.empty]

theorem AdvancingAck.store (received : AdvancingAck state input recovery after) :
    after.receiveStore = state.receiveStore := by
  rw [received.afterEq]
  exact windowState_receiveStore state _ input.packet.segment

theorem AdvancingAck.pending (received : AdvancingAck state input recovery after) :
    after.pending = state.pending := by
  rw [received.afterEq]
  unfold advancingAckState inOrderReceivedWith windowState
  split <;> rfl

theorem AdvancingAck.now (received : AdvancingAck state input recovery after) :
    after.now = state.now := by
  obtain ⟨reaction, conditions⟩ := received.conditions
  simp only [State.now, received.runtime, conditions.runtime, Option.map_some, Option.getD_some,
    advancingAckRecovery, Recovery.acknowledgeState_now]

theorem AdvancingAck.recovery_clocked (_received : AdvancingAck state input recovery after) (clocked : recovery.Clocked) :
    (advancingAckRecovery state input recovery).Clocked := Recovery.acknowledgeState_clocked recovery _ clocked

theorem AdvancingAck.recovery_positive (_received : AdvancingAck state input recovery after) (positive : recovery.Positive) :
    (advancingAckRecovery state input recovery).Positive := Recovery.acknowledgeState_positive recovery _ positive

theorem AdvancingAck.count_positive (received : AdvancingAck state input recovery after) : 0 < inOrderCount state input := by
  obtain ⟨reaction, conditions⟩ := received.conditions
  exact conditions.positive

theorem AdvancingAck.sender_fields (received : AdvancingAck state input recovery after) :
    after.core.sent = state.core.sent.drop (inOrderCount state input) ∧
      after.core.sendUna = state.core.sendUna.add (inOrderCount state input) ∧
      after.core.sendNext = state.core.sendNext ∧ after.core.receiveNext = state.core.receiveNext := by
  rw [received.core]
  simp only [EstablishedReceive.commit, List.length_nil, Seq.add_zero]
  trivial

theorem AdvancingAck.head_fields (received : AdvancingAck state input recovery after)
    (head : Recovery.Outstanding) (tail : List Recovery.Outstanding)
    (source : recovery.outstanding = head :: tail) (counted : inOrderCount state input = head.count) :
    let next := advancingAckRecovery state input recovery
    next.outstanding = tail ∧ next.now = recovery.now ∧
      next.nextId = recovery.nextId ∧ next.frontier = recovery.frontier ∧
      next.smss = recovery.smss ∧ next.cwnd = recovery.cwnd ∧ next.ssthresh = recovery.ssthresh ∧
      next.deadline = (if tail.isEmpty then none else some (recovery.now + next.rto)) ∧
      next.lastTimedOut = (if tail.isEmpty then none else recovery.lastTimedOut) ∧
      next.timeoutCount = (if tail.isEmpty then 0 else recovery.timeoutCount) ∧ next.duplicateAcks = 0 := by
  have positive : 0 < head.count := by rw [← counted]; exact received.count_positive
  simpa only [advancingAckRecovery, counted] using Recovery.acknowledgeState_head_fields recovery head tail source positive

theorem AdvancingAck.tail_fields (received : AdvancingAck state input recovery after)
    (head tail : Recovery.Outstanding) (rest : List Recovery.Outstanding)
    (source : recovery.outstanding = head :: tail :: rest) (counted : inOrderCount state input = head.count) :
    let next := advancingAckRecovery state input recovery
    next.outstanding = tail :: rest ∧ next.deadline = some (recovery.now + next.rto) ∧
      next.lastTimedOut = recovery.lastTimedOut ∧ next.timeoutCount = recovery.timeoutCount := by
  have positive : 0 < head.count := by rw [← counted]; exact received.count_positive
  simpa only [advancingAckRecovery, counted] using Recovery.acknowledgeState_tail_metadata recovery head tail rest source positive

theorem AdvancingAck.head_fresh (received : AdvancingAck state input recovery after)
    (head : Recovery.Outstanding) (tail : List Recovery.Outstanding)
    (source : recovery.outstanding = head :: tail) (counted : inOrderCount state input = head.count)
    (fresh : head.retried = false) :
    let next := advancingAckRecovery state input recovery
    let estimate := RTO.observe recovery.estimator (recovery.now - head.sentAt)
    next.estimator = some estimate ∧ next.lastSample = some ⟨head.id, head.sentAt, recovery.now⟩ ∧ next.rto = RTO.interval estimate := by
  have positive : 0 < head.count := by rw [← counted]; exact received.count_positive
  simpa only [advancingAckRecovery, counted] using Recovery.acknowledgeState_head_fresh recovery head tail source positive fresh

theorem AdvancingAck.head_retried (received : AdvancingAck state input recovery after)
    (head : Recovery.Outstanding) (tail : List Recovery.Outstanding)
    (source : recovery.outstanding = head :: tail) (counted : inOrderCount state input = head.count)
    (retried : head.retried = true) :
    let next := advancingAckRecovery state input recovery
    next.estimator = recovery.estimator ∧ next.lastSample = recovery.lastSample ∧ next.rto = recovery.rto := by
  have positive : 0 < head.count := by rw [← counted]; exact received.count_positive
  simpa only [advancingAckRecovery, counted] using Recovery.acknowledgeState_head_retried recovery head tail source positive retried

theorem AdvancingAck.tail_credit (received : AdvancingAck state input recovery after)
    (head tail : Recovery.Outstanding) (rest : List Recovery.Outstanding)
    (source : recovery.outstanding = head :: tail :: rest) (counted : inOrderCount state input = head.count)
    (previous : recovery.lastTimedOut = some head.id) (distinct : head.id ≠ tail.id) :
    (advancingAckRecovery state input recovery).lastTimedOut ≠ some tail.id := by
  have positive : 0 < head.count := by rw [← counted]; exact received.count_positive
  simpa only [advancingAckRecovery, counted] using
    Recovery.acknowledgeState_tail_credit recovery head tail rest source positive previous distinct

theorem AdvancingAck.two_record_tail (received : AdvancingAck state input recovery after)
    (head tail : Recovery.Outstanding) (source : recovery.outstanding = [head, tail])
    (counted : inOrderCount state input = head.count) (bytes : state.core.sent = lower ++ upper)
    (size : head.count = lower.length) :
    after.recovery = some (advancingAckRecovery state input recovery) ∧
      (advancingAckRecovery state input recovery).outstanding = [tail] ∧
      after.core.sent = upper ∧ after.core.sendUna = state.core.sendUna.add lower.length ∧
      (advancingAckRecovery state input recovery).deadline = some (recovery.now + (advancingAckRecovery state input recovery).rto) ∧
      (advancingAckRecovery state input recovery).lastTimedOut = recovery.lastTimedOut ∧
      (advancingAckRecovery state input recovery).timeoutCount = recovery.timeoutCount := by
  have fields := received.tail_fields head tail [] source counted
  have sender := received.sender_fields
  refine ⟨received.runtime, fields.1, ?_, ?_, fields.2.1, fields.2.2.1, fields.2.2.2⟩
  · rw [sender.1, bytes, counted, size, List.drop_left]
  · rw [sender.2.1, counted, size]

end Netlib.Protocol.TCP.Endpoint
