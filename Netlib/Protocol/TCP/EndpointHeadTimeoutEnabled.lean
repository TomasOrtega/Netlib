import Netlib.Protocol.TCP.EndpointTimeoutEnabled
import Netlib.Protocol.TCP.EndpointAckReceiveEnabled
import Netlib.Protocol.TCP.ApplicationTraceCore

/-!
# Head-record timeout from current endpoint facts

A retry emits only the current head range and retains its actual tail.
A full ACK of a retried head retains the old RTT history.
-/

namespace Netlib.Protocol.TCP.Endpoint

structure HeadTimeoutReady (state : State) (recovery : Recovery.State)
    (head : Recovery.Outstanding) (tail : List Recovery.Outstanding) (deadline : Nat) : Prop where
  runtime : state.recovery = some recovery
  coherent : RecoveryCoherent state
  prepared : AckPrepared state
  source : recovery.outstanding = head :: tail
  positive : recovery.Positive
  timer : recovery.deadline = some deadline
  due : deadline ≤ recovery.now
  elapsed : head.lastAt + recovery.rto ≤ recovery.now
  credit : recovery.lastTimedOut = some head.id → recovery.timeoutCount < 2
  clocked : recovery.Clocked
  window : head.count ≤ state.sendWindow

theorem HeadTimeoutReady.head_positive (ready : HeadTimeoutReady state recovery head tail deadline) : 0 < head.count :=
  ready.positive head (by simp only [ready.source, List.mem_cons_self])

theorem HeadTimeoutReady.flight_eq (ready : HeadTimeoutReady state recovery head tail deadline) :
    head.count + (tail.map (·.count)).sum = state.core.sent.length := by
  have fields : recovery.Valid ∧ recovery.smss = state.effectiveMSS ∧
      Recovery.flight recovery = state.core.sent.length ∧ AckWindowKnown state := by
    simpa only [RecoveryCoherent, ready.runtime] using ready.coherent
  simpa only [Recovery.flight, ready.source, List.map_cons, List.sum_cons] using fields.2.2.1

theorem HeadTimeoutReady.count_le (ready : HeadTimeoutReady state recovery head tail deadline) :
    head.count ≤ state.core.sent.length := by have count := ready.flight_eq; omega

theorem HeadTimeoutReady.bounds (ready : HeadTimeoutReady state recovery head tail deadline) (valid : state.Valid) :
    head.count ≤ state.effectiveMSS ∧ 40 + head.count ≤ state.ipSendLimit := by
  have fields : recovery.Valid ∧ recovery.smss = state.effectiveMSS ∧
      Recovery.flight recovery = state.core.sent.length ∧ AckWindowKnown state := by
    simpa only [RecoveryCoherent, ready.runtime] using ready.coherent
  have total : state.core.sent.length ≤ state.effectiveMSS := by
    rw [← fields.2.2.1, ← fields.2.1]
    exact fields.1.2.2.2
  have count := Nat.le_trans ready.count_le total
  exact ⟨count, Nat.le_trans (Nat.add_le_add_left count 40) valid.2.2.2.2.2.1⟩

def headRetryState (state : State) (recovery : Recovery.State)
    (head : Recovery.Outstanding) (tail : List Recovery.Outstanding) : State :=
  { outputState state with recovery := some (Recovery.timeoutState recovery head tail) }

theorem headRetryState_nil (state : State) (recovery : Recovery.State) (head : Recovery.Outstanding) :
    headRetryState state recovery head [] = retryState state recovery head := rfl

theorem head_timeout_success_enabled (state : State) (recovery : Recovery.State)
    (head : Recovery.Outstanding) (tail : List Recovery.Outstanding) (deadline : Nat)
    (valid : state.Valid) (ready : HeadTimeoutReady state recovery head tail deadline) :
    ∃ output, timeout state true =
        ⟨headRetryState state recovery head tail, .accepted (.retry head.count), some output, [], none⟩ ∧
      emitAt state state.core.sendUna (state.core.sent.take head.count) = .ok output := by
  have bounds := ready.bounds valid
  have bounded : 40 + (state.core.sent.take head.count).length ≤ 65535 := by
    have count := List.length_take_le head.count state.core.sent
    have ip := valid.2.2.2.2.2.2
    omega
  obtain ⟨output, encoded⟩ := emitAt_exists state state.core.sendUna _ valid ready.prepared.1 bounded
  have timed := Recovery.timeout_of_due recovery head tail deadline ready.source ready.timer ready.head_positive
    ready.due ready.elapsed ready.credit
  refine ⟨output, ?_, encoded⟩
  simp only [timeout, valid, not_true_eq_false, ite_false, ready.coherent, ready.runtime, timed,
    Bool.not_true, Bool.false_eq_true, Nat.not_lt.mpr ready.window, Nat.not_lt.mpr ready.count_le,
    Nat.not_lt.mpr bounds.1, Nat.not_lt.mpr bounds.2, false_or,
    ackReady_of_prepared state ready.prepared, encoded, headRetryState]

theorem headRetryState_valid (ready : HeadTimeoutReady state recovery head tail deadline) (valid : state.Valid) :
    (headRetryState state recovery head tail).Valid := by
  obtain ⟨_, result, _⟩ := head_timeout_success_enabled state recovery head tail deadline valid ready
  simpa only [result] using timeout_valid state true valid

theorem headRetryState_coherent (ready : HeadTimeoutReady state recovery head tail deadline) :
    RecoveryCoherent (headRetryState state recovery head tail) := by
  have fields : recovery.Valid ∧ recovery.smss = state.effectiveMSS ∧
      Recovery.flight recovery = state.core.sent.length ∧ AckWindowKnown state := by
    simpa only [RecoveryCoherent, ready.runtime] using ready.coherent
  have timed := Recovery.timeout_of_due recovery head tail deadline ready.source ready.timer ready.head_positive
    ready.due ready.elapsed ready.credit
  exact ⟨Recovery.timeout_valid _ _ _ fields.1 timed, fields.2.1,
    (Recovery.timeout_flight _ _ _ timed).trans fields.2.2.1, fields.2.2.2⟩

theorem headRetryState_prepared (ready : HeadTimeoutReady state recovery head tail deadline) :
    AckPrepared (headRetryState state recovery head tail) := by
  apply withRecovery_ackPrepared (outputState state) (Recovery.timeoutState recovery head tail)
    (outputState_ackPrepared state ready.prepared)
  simp only [outputState, State.now, ready.runtime, Option.map_some, Option.getD_some, Recovery.timeoutState]

theorem headRetryState_clocked (ready : HeadTimeoutReady state recovery head tail deadline) :
    (Recovery.timeoutState recovery head tail).Clocked :=
  Recovery.timeoutState_clocked recovery head tail ready.source ready.clocked

theorem headRetryState_positive (ready : HeadTimeoutReady state recovery head tail deadline) :
    (Recovery.timeoutState recovery head tail).Positive :=
  Recovery.timeoutState_positive recovery head tail ready.source ready.positive

theorem headRetryState_frame (state : State) (recovery : Recovery.State)
    (head : Recovery.Outstanding) (tail : List Recovery.Outstanding) :
    { headRetryState state recovery head tail with recovery := state.recovery, ackReaction := state.ackReaction } = state := rfl

theorem outputState_storage_coherent (state : State) (prepared : AckPrepared state) (storage : StorageCoherent state) :
    StorageCoherent (outputState state) := by
  refine ⟨outputState_storage_valid state storage.1, ?_⟩
  cases selected : state.ackReaction with
  | none => simp only [outputState, selected, Option.map_none]
  | some reaction =>
    have old := storage.2
    simp only [selected] at old
    have coherent : state.recovery.isSome = true ∧
        reaction.Coherent state.core.receiveNext state.core.window state.localReceiveMSS.limit := by
      simpa only [AckCoherent, selected] using prepared.1
    have bounds := ReceiveAdvertisement.candidate_bounds reaction.advertisement state.core.capacity state.core.window state.effectiveMSS
      coherent.2.1
    simp only [outputState, selected, Option.map_some,
      AckReaction.State.window, AckReaction.outputState, ReceiveAdvertisement.commit_window]
    refine ⟨old.1, ?_⟩
    apply ReceiveStore.State.valid_mono state.receiveStore _ state.core.window _ state.core.window old.2
    · exact Nat.add_le_add_left bounds.1 _
    · exact Nat.le_refl _
    · omega

theorem headRetryState_storage_coherent (ready : HeadTimeoutReady state recovery head tail deadline)
    (storage : StorageCoherent state) : StorageCoherent (headRetryState state recovery head tail) :=
  outputState_storage_coherent state ready.prepared storage

theorem headRetryState_fields (ready : HeadTimeoutReady state recovery head tail deadline) :
    let after := Recovery.timeoutState recovery head tail
    (headRetryState state recovery head tail).core = state.core ∧
      (headRetryState state recovery head tail).pending = state.pending ∧
      (headRetryState state recovery head tail).receiveStore = state.receiveStore ∧
      (headRetryState state recovery head tail).now = state.now ∧
      (headRetryState state recovery head tail).ackReaction = (outputState state).ackReaction ∧
      after.outstanding = { head with lastAt := recovery.now, retried := true } :: tail ∧
      after.rto = 2 * recovery.rto ∧ after.deadline = some (recovery.now + 2 * recovery.rto) ∧
      after.frontier = recovery.frontier ∧ after.nextId = recovery.nextId ∧
      after.estimator = recovery.estimator ∧ after.lastSample = recovery.lastSample ∧
      after.duplicateAcks = 0 ∧ after.lastTimedOut = some head.id ∧
      after.timeoutCount = (if recovery.lastTimedOut = some head.id then recovery.timeoutCount + 1 else 1) ∧
      0 < after.timeoutCount ∧ after.timeoutCount ≤ 2 := by
  dsimp only
  have credit := ready.credit
  simp only [headRetryState, outputState, State.now, ready.runtime, Option.map_some,
    Option.getD_some, Recovery.timeoutState, true_and]
  split <;> simp_all <;> omega

theorem head_timeout_payload (ready : HeadTimeoutReady state recovery head tail deadline)
    (output : Input) (encoded : emitAt state state.core.sendUna (state.core.sent.take head.count) = .ok output) :
    output.packet.segment.payload = state.core.sent.take head.count ∧
      output.packet.segment.payload.length = head.count := by
  have payload := emitAt_payload state _ _ output encoded
  exact ⟨payload, by rw [payload, List.length_take, Nat.min_eq_left ready.count_le]⟩

theorem head_timeout_fields (ready : HeadTimeoutReady state recovery head tail deadline)
    (output : Input) (encoded : emitAt state state.core.sendUna (state.core.sent.take head.count) = .ok output) :
    output.packet.header = Output.reverse state.core.inbound ∧
      output.packet.segment.sequence = state.core.sendUna ∧
      output.packet.segment.acknowledgment = state.core.receiveNext ∧
      output.packet.segment.window.val = outputWindow state ∧
      output.packet.segment.flags = 16 ∧ output.packet.segment.reserved = 0 ∧
      output.packet.segment.options = [] ∧ output.packet.segment.urgentPointer = 0 ∧
      output.packet.segment.payload = state.core.sent.take head.count ∧
      output.packet.segment.payload.length = head.count ∧ output.packet.ip.packet.ttl.toNat = 64 := by
  have transport := emitAt_transport state _ _ output encoded
  have payload := head_timeout_payload ready output encoded
  exact ⟨transport.1, transport.2.1, transport.2.2.1, transport.2.2.2.1, transport.2.2.2.2.1,
    transport.2.2.2.2.2.1, transport.2.2.2.2.2.2.1, transport.2.2.2.2.2.2.2,
    payload.1, payload.2, emitAt_ttl state _ _ output encoded⟩

theorem head_timeout_origin (valid : state.Valid) (ready : HeadTimeoutReady state recovery head tail deadline) (stamp : Nat) :
    ∃ output,
      let actual := ApplicationTrace.Step.make state valid (.timeout true) stamp
      actual.result = ⟨headRetryState state recovery head tail, .accepted (.retry head.count), some output, [], none⟩ ∧
      ApplicationTrace.OutputOrigin actual output ∧ actual.emitted = [] ∧
      output.packet.segment.payload = state.core.sent.take head.count := by
  obtain ⟨output, result, encoded⟩ := head_timeout_success_enabled state recovery head tail deadline valid ready
  let actual := ApplicationTrace.Step.make state valid (.timeout true) stamp
  have computed : actual.result =
      ⟨headRetryState state recovery head tail, .accepted (.retry head.count), some output, [], none⟩ := result
  exact ⟨output, computed, .retry head.count true rfl (congrArg Result.decision computed)
    (congrArg Result.output computed), rfl, (head_timeout_payload ready output encoded).1⟩

theorem full_ack_of_retried_head (recovery : Recovery.State) (head : Recovery.Outstanding)
    (tail : List Recovery.Outstanding) (source : recovery.outstanding = head :: tail)
    (positive : recovery.Positive) (retried : head.retried = true) :
    Recovery.sample recovery (Recovery.flight recovery) = none ∧
      Recovery.acknowledgeState recovery (Recovery.flight recovery) =
        { recovery with
          outstanding := [], deadline := none, lastTimedOut := none
          timeoutCount := 0, duplicateAcks := 0 } := by
  have headPositive := positive head (by simp only [source, List.mem_cons_self])
  have full : 0 < Recovery.flight recovery := by
    simp only [Recovery.flight, source, List.map_cons, List.sum_cons]
    omega
  have bounded : head.count ≤ Recovery.flight recovery := by
    simp only [Recovery.flight, source, List.map_cons, List.sum_cons]
    omega
  have member : head ∈ Recovery.retired (Recovery.flight recovery) recovery.outstanding := by
    rw [source]
    simp only [Recovery.retired, Nat.ne_of_gt full, ite_false, bounded, ite_true, List.mem_cons_self]
  have sample := Recovery.sample_retried recovery _ head member retried
  have cleared : Recovery.retire (Recovery.flight recovery) recovery.outstanding = [] :=
    Recovery.retire_all recovery.outstanding positive
  refine ⟨sample, ?_⟩
  simp only [Recovery.acknowledgeState, Nat.ne_of_gt full, ite_false, sample, Option.map_none,
    cleared, List.isEmpty_nil, ite_true]

theorem headRetryState_full_ack (ready : HeadTimeoutReady state recovery head tail deadline) :
    let after := Recovery.timeoutState recovery head tail
    Recovery.sample after (Recovery.flight after) = none ∧
      Recovery.acknowledgeState after (Recovery.flight after) =
        { after with
          outstanding := [], deadline := none, lastTimedOut := none
          timeoutCount := 0, duplicateAcks := 0 } := by
  apply full_ack_of_retried_head (Recovery.timeoutState recovery head tail)
    { head with lastAt := recovery.now, retried := true } tail rfl (headRetryState_positive ready) rfl

theorem headRetryState_two_record_full_ack (ready : HeadTimeoutReady state recovery head [upper] deadline) :
    let after := Recovery.timeoutState recovery head [upper]
    Recovery.flight after = head.count + upper.count ∧
      Recovery.retired (head.count + upper.count) after.outstanding =
        [{ head with lastAt := recovery.now, retried := true }, upper] ∧
      Recovery.sample after (head.count + upper.count) = none ∧
      Recovery.acknowledgeState after (head.count + upper.count) =
        { after with
          outstanding := [], deadline := none, lastTimedOut := none
          timeoutCount := 0, duplicateAcks := 0 } := by
  have first := ready.head_positive
  have last := ready.positive upper (by rw [ready.source]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have count : Recovery.flight (Recovery.timeoutState recovery head [upper]) = head.count + upper.count := by
    simp only [Recovery.flight, Recovery.timeoutState, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.add_zero]
  have retired : Recovery.retired (head.count + upper.count) (Recovery.timeoutState recovery head [upper]).outstanding =
      [{ head with lastAt := recovery.now, retried := true }, upper] := by
    have total : head.count + upper.count ≠ 0 := by omega
    have bounded : head.count ≤ head.count + upper.count := by omega
    simp only [Recovery.timeoutState, Recovery.retired, total, ite_false, bounded, ite_true,
      Nat.add_sub_cancel_left, Nat.ne_of_gt last, Nat.le_refl]
  have cleared := headRetryState_full_ack ready
  dsimp only at cleared ⊢
  rw [count] at cleared
  exact ⟨count, retired, cleared⟩

theorem inOrderCount_of_full_ack (state : State) (packet : Input) (valid : state.Valid)
    (covers : packet.packet.segment.acknowledgment = state.core.sendNext) : inOrderCount state packet = state.core.sent.length := by
  have count := valid.1.2.2.2.1
  have span := valid.1.2.2.2.2.1
  rw [inOrderCount, covers, ← span, Seq.distance_add]
  apply Nat.mod_eq_of_lt
  unfold EstablishedReceive.maxSendWindow at count
  unfold Seq.modulus
  omega

theorem receive_full_ack_of_retried_head (state : State) (packet : Input) (recovery : Recovery.State)
    (reaction : AckReaction.State) (head : Recovery.Outstanding) (tail : List Recovery.Outstanding)
    (valid : state.Valid) (coherent : RecoveryCoherent state) (prepared : AckPrepared state)
    (storage : StorageCoherent state) (runtime : state.recovery = some recovery)
    (ackRuntime : state.ackReaction = some reaction) (source : recovery.outstanding = head :: tail)
    (positive : recovery.Positive) (retried : head.retried = true) (emptyHeld : state.receiveStore.held = [])
    (tuple : packet.packet.header = state.core.inbound) (controls : EstablishedReceive.control packet.packet.segment = none)
    (ack : Flags.ack packet.packet.segment.flags = true) (sequence : packet.packet.segment.sequence = state.core.receiveNext)
    (empty : packet.packet.segment.payload = []) (covers : packet.packet.segment.acknowledgment = state.core.sendNext) :
    ∃ after,
      let retired := { recovery with
        outstanding := [], deadline := none, lastTimedOut := none
        timeoutCount := 0, duplicateAcks := 0 }
      receive state packet = ⟨after, .accepted (.receive state.core.sent.length 0), none, [], none⟩ ∧
      after = inOrderReceivedWith state packet retired ∧ after.recovery = some retired ∧
      after.core.sent = [] ∧ after.core.sendUna = state.core.sendNext ∧
      after.Valid ∧ AckPrepared after ∧ RecoveryCoherent after ∧ StorageCoherent after ∧
      receiveRuns state packet = [] ∧ receivedBytes state packet = [] := by
  have fields : recovery.Valid ∧ recovery.smss = state.effectiveMSS ∧
      Recovery.flight recovery = state.core.sent.length ∧ AckWindowKnown state := by
    simpa only [RecoveryCoherent, runtime] using coherent
  have headPositive := positive head (by simp only [source, List.mem_cons_self])
  have nonempty : 0 < state.core.sent.length := by
    rw [← fields.2.2.1]
    simp only [Recovery.flight, source, List.map_cons, List.sum_cons]
    omega
  obtain ⟨acknowledged, after, accepted, afterEq, actual, runs, bytes, sent, cursor,
      afterValid, afterPrepared, afterCoherent, afterStorage, _, _, _⟩ :=
    receive_empty_full_ack_coherent state packet recovery reaction valid coherent prepared storage runtime ackRuntime
      positive nonempty emptyHeld tuple controls ack sequence empty (inOrderCount_of_full_ack state packet valid covers)
  have cleared := (Recovery.acknowledge_fields _ _ _ accepted).2.trans
    (full_ack_of_retried_head recovery head tail source positive retried).2
  rw [cleared] at afterEq
  refine ⟨after, actual, afterEq, ?_, sent, cursor, afterValid, afterPrepared, afterCoherent, afterStorage, runs, bytes⟩
  rw [afterEq, inOrderReceivedWith, windowState_recovery]

end Netlib.Protocol.TCP.Endpoint
