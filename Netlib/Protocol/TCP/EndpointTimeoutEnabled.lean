import Netlib.Protocol.TCP.EndpointAckEnabled
import Netlib.Protocol.TCP.RecoveryEnabled

namespace Netlib.Protocol.TCP.Endpoint

structure TimeoutReady (state : State) (recovery : Recovery.State)
    (entry : Recovery.Outstanding) (deadline : Nat) : Prop where
  runtime : state.recovery = some recovery
  coherent : RecoveryCoherent state
  prepared : AckPrepared state
  source : recovery.outstanding = [entry]
  positive : 0 < entry.count
  timer : recovery.deadline = some deadline
  due : deadline ≤ recovery.now
  elapsed : entry.lastAt + recovery.rto ≤ recovery.now
  credit : recovery.lastTimedOut = some entry.id → recovery.timeoutCount < 2
  clocked : recovery.Clocked
  window : entry.count ≤ state.sendWindow

theorem emitAt_exists (state : State) (sequence : Seq) (payload : List UInt8)
    (valid : state.Valid) (coherent : AckCoherent state) (bounded : 40 + payload.length ≤ 65535) :
    ∃ output, emitAt state sequence payload = .ok output := by
  cases selected : state.ackReaction with
  | none => simpa only [emitAt, selected] using Output.emitAt_exists state.core sequence payload valid.1 bounded
  | some reaction =>
    simpa only [emitAt, selected] using Output.emitAtWindow_exists state.core sequence (outputWindow state) payload valid.1
      (outputWindow_le state coherent) bounded

theorem emitAt_ttl (state : State) (sequence : Seq) (payload : List UInt8)
    (output : Input) (encoded : emitAt state sequence payload = .ok output) :
    output.packet.ip.packet.ttl.toNat = 64 := by
  cases selected : state.ackReaction with
  | none =>
    rw [(Output.emitAt_fields state.core sequence payload output
      (by simpa only [emitAt, selected] using encoded)).2.2.2]
    rfl
  | some reaction =>
    rw [(Output.emitAtWindow_fields state.core sequence (outputWindow state) payload output
      (by simpa only [emitAt, selected] using encoded)).2.2.2.2]
    rfl

theorem withRecovery_ackPrepared (state : State) (recovery : Recovery.State)
    (prepared : AckPrepared state) (sameTime : recovery.now = state.now) :
    AckPrepared { state with recovery := some recovery } := by
  cases selected : state.ackReaction with
  | none => simp only [AckPrepared, AckCoherent, and_self]
  | some reaction =>
    have coherent : state.recovery.isSome = true ∧
        reaction.Coherent state.core.receiveNext state.core.window state.localReceiveMSS.limit := by
      simpa only [AckCoherent, selected] using prepared.1
    have guards : reaction.WithinTime state.now ∧
        reaction.Covered state.core.capacity state.core.window state.effectiveMSS := by
      simpa only [selected] using prepared.2
    exact ⟨by exact And.intro rfl coherent.2,
      by simpa only [selected, State.now, Option.map_some, Option.getD_some, sameTime] using guards⟩

theorem TimeoutReady.count (ready : TimeoutReady state recovery entry deadline) :
    entry.count = state.core.sent.length := by
  have fields : recovery.Valid ∧ recovery.smss = state.effectiveMSS ∧
      Recovery.flight recovery = state.core.sent.length ∧ AckWindowKnown state := by
    simpa only [RecoveryCoherent, ready.runtime] using ready.coherent
  simpa only [Recovery.flight, ready.source, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero] using fields.2.2.1

theorem TimeoutReady.bounds (ready : TimeoutReady state recovery entry deadline)
    (valid : state.Valid) : entry.count ≤ state.effectiveMSS ∧ 40 + entry.count ≤ state.ipSendLimit := by
  have fields : recovery.Valid ∧ recovery.smss = state.effectiveMSS ∧
      Recovery.flight recovery = state.core.sent.length ∧ AckWindowKnown state := by
    simpa only [RecoveryCoherent, ready.runtime] using ready.coherent
  have bound := fields.1.2.2.2
  have count : entry.count ≤ state.effectiveMSS := by
    simpa only [Recovery.flight, ready.source, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.add_zero, fields.2.1] using bound
  exact ⟨count, Nat.le_trans (Nat.add_le_add_left count 40) valid.2.2.2.2.2.1⟩

def retryState (state : State) (recovery : Recovery.State) (entry : Recovery.Outstanding) : State :=
  { outputState state with recovery := some (Recovery.timeoutState recovery entry []) }

theorem timeout_success_enabled (state : State) (recovery : Recovery.State)
    (entry : Recovery.Outstanding) (deadline : Nat) (valid : state.Valid)
    (ready : TimeoutReady state recovery entry deadline) :
    ∃ output, timeout state true =
        ⟨retryState state recovery entry, .accepted (.retry entry.count), some output, [], none⟩ ∧
      emitAt state state.core.sendUna (state.core.sent.take entry.count) = .ok output := by
  have bounds := ready.bounds valid
  have bounded : 40 + (state.core.sent.take entry.count).length ≤ 65535 := by
    have count := List.length_take_le entry.count state.core.sent
    have ip := valid.2.2.2.2.2.2
    omega
  obtain ⟨output, encoded⟩ := emitAt_exists state state.core.sendUna _ valid ready.prepared.1 bounded
  have timed := Recovery.timeout_of_due recovery entry [] deadline ready.source ready.timer
    ready.positive ready.due ready.elapsed ready.credit
  refine ⟨output, ?_, encoded⟩
  simp only [timeout, valid, not_true_eq_false, ite_false, ready.coherent, ready.runtime, timed,
    Bool.not_true, Bool.false_eq_true, Nat.not_lt.mpr ready.window, Nat.not_lt.mpr (Nat.le_of_eq ready.count),
    Nat.not_lt.mpr bounds.1, Nat.not_lt.mpr bounds.2, false_or,
    ackReady_of_prepared state ready.prepared, encoded, retryState]

theorem retryState_valid (ready : TimeoutReady state recovery entry deadline) (valid : state.Valid) :
    (retryState state recovery entry).Valid := by
  obtain ⟨output, result, _⟩ := timeout_success_enabled state recovery entry deadline valid ready
  simpa only [result] using timeout_valid state true valid

theorem retryState_coherent (ready : TimeoutReady state recovery entry deadline) :
    RecoveryCoherent (retryState state recovery entry) := by
  have fields : recovery.Valid ∧ recovery.smss = state.effectiveMSS ∧
      Recovery.flight recovery = state.core.sent.length ∧ AckWindowKnown state := by
    simpa only [RecoveryCoherent, ready.runtime] using ready.coherent
  have timed := Recovery.timeout_of_due recovery entry [] deadline ready.source ready.timer
    ready.positive ready.due ready.elapsed ready.credit
  exact ⟨Recovery.timeout_valid _ _ _ fields.1 timed, fields.2.1,
    (Recovery.timeout_flight _ _ _ timed).trans fields.2.2.1, fields.2.2.2⟩

theorem retryState_prepared (ready : TimeoutReady state recovery entry deadline) :
    AckPrepared (retryState state recovery entry) := by
  apply withRecovery_ackPrepared (outputState state) (Recovery.timeoutState recovery entry [])
    (outputState_ackPrepared state ready.prepared)
  simp only [outputState, State.now, ready.runtime, Option.map_some, Option.getD_some,
    Recovery.timeoutState]

theorem retryState_clocked (ready : TimeoutReady state recovery entry deadline) :
    (Recovery.timeoutState recovery entry []).Clocked :=
  Recovery.timeoutState_clocked recovery entry [] ready.source ready.clocked

theorem retryState_positive (ready : TimeoutReady state recovery entry deadline) :
    (Recovery.timeoutState recovery entry []).Positive := by
  apply Recovery.timeoutState_positive recovery entry [] ready.source
  simp only [Recovery.State.Positive, ready.source, List.mem_singleton]
  intro selected same
  simpa only [same] using ready.positive

theorem retryState_fields (ready : TimeoutReady state recovery entry deadline) :
    let after := Recovery.timeoutState recovery entry []
    (retryState state recovery entry).core = state.core ∧
      (retryState state recovery entry).pending = state.pending ∧
      (retryState state recovery entry).receiveStore = state.receiveStore ∧
      (retryState state recovery entry).now = state.now ∧
      after.outstanding = [{ entry with lastAt := recovery.now, retried := true }] ∧
      after.rto = 2 * recovery.rto ∧ after.deadline = some (recovery.now + 2 * recovery.rto) ∧
      after.frontier = recovery.frontier ∧ after.nextId = recovery.nextId ∧
      after.estimator = recovery.estimator ∧ after.lastSample = recovery.lastSample ∧
      after.lastTimedOut = some entry.id ∧ 0 < after.timeoutCount ∧ after.timeoutCount ≤ 2 := by
  dsimp only
  have credit := ready.credit
  simp only [retryState, outputState, State.now, ready.runtime, Option.map_some,
    Option.getD_some, Recovery.timeoutState, true_and]
  split <;> simp_all <;> omega

theorem timeout_payload (ready : TimeoutReady state recovery entry deadline)
    (output : Input) (encoded : emitAt state state.core.sendUna (state.core.sent.take entry.count) = .ok output) :
    output.packet.segment.payload = state.core.sent := by
  simpa only [ready.count, List.take_length] using emitAt_payload state _ _ output encoded

theorem retryState_karn (ready : TimeoutReady state recovery entry deadline) :
    Recovery.sample (Recovery.timeoutState recovery entry []) entry.count = none := by
  simp [Recovery.sample, Recovery.retired, Recovery.timeoutState, Nat.ne_of_gt ready.positive]

theorem retryState_full_ack (ready : TimeoutReady state recovery entry deadline) :
    let after := Recovery.timeoutState recovery entry []
    (Recovery.acknowledgeState after entry.count).outstanding = [] ∧
      (Recovery.acknowledgeState after entry.count).deadline = none ∧
      (Recovery.acknowledgeState after entry.count).lastTimedOut = none ∧
      (Recovery.acknowledgeState after entry.count).timeoutCount = 0 ∧
      (Recovery.acknowledgeState after entry.count).rto = after.rto ∧
      (Recovery.acknowledgeState after entry.count).estimator = after.estimator ∧
      (Recovery.acknowledgeState after entry.count).lastSample = after.lastSample := by
  dsimp only
  simp only [Recovery.acknowledgeState, Nat.ne_of_gt ready.positive, ite_false]
  rw [retryState_karn ready]
  simp [Recovery.timeoutState, Recovery.retire, Nat.ne_of_gt ready.positive]

end Netlib.Protocol.TCP.Endpoint
