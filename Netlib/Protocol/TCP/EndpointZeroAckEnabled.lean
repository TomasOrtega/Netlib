import Netlib.Protocol.TCP.EndpointPartialAckEnabled
import Netlib.Protocol.TCP.EndpointTimeoutEnabled

namespace Netlib.Protocol.TCP.Endpoint

structure ZeroAckConditions (state : State) (input : Input)
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
  acknowledgment : input.packet.segment.acknowledgment = state.core.sendUna
  credit : qualifyingDuplicate state input.packet.segment 0 = true → recovery.duplicateAcks < 2

def zeroAckRecovery (state : State) (input : Input) (recovery : Recovery.State) : Recovery.State :=
  if qualifyingDuplicate state input.packet.segment 0 then { recovery with duplicateAcks := recovery.duplicateAcks + 1 }
  else { recovery with duplicateAcks := 0 }

def zeroAckState (state : State) (input : Input) (recovery : Recovery.State) : State :=
  windowState state
    { state with
      recovery := some (zeroAckRecovery state input recovery)
      lastAckWindow := some input.packet.segment.window.val } input.packet.segment

theorem zeroAckRecovery_fixed (state : State) (input : Input) (recovery : Recovery.State) :
    { zeroAckRecovery state input recovery with duplicateAcks := recovery.duplicateAcks } = recovery := by
  unfold zeroAckRecovery
  split <;> rfl

structure ZeroAck (state : State) (input : Input) (recovery : Recovery.State) (after : State) : Prop where
  conditions : ∃ reaction, ZeroAckConditions state input recovery reaction
  afterEq : after = zeroAckState state input recovery
  effect : receiveEffect state input = receivePlain ⟨after, .accepted (.receive 0 0), none, [], none⟩
  valid : after.Valid
  coherent : RecoveryCoherent after
  prepared : AckPrepared after
  storage : StorageCoherent after
  runtime : after.recovery = some (zeroAckRecovery state input recovery)

variable {state after : State} {input : Input} {recovery : Recovery.State} {reaction : AckReaction.State}

private theorem zero_receive_recovery (conditions : ZeroAckConditions state input recovery reaction) :
    receiveRecovery state input.packet.segment 0 = .ok (some (zeroAckRecovery state input recovery)) := by
  cases duplicate : qualifyingDuplicate state input.packet.segment 0 with
  | false =>
    simp only [receiveRecovery, conditions.runtime, Recovery.acknowledge_zero, bind, Except.bind,
      duplicate, Bool.false_eq_true, ite_false, zeroAckRecovery, pure, Except.pure]
  | true =>
    have credit := conditions.credit duplicate
    have allowed : ¬recovery.duplicateAcks + 1 ≥ 3 := by omega
    simp only [receiveRecovery, conditions.runtime, Recovery.acknowledge_zero, bind, Except.bind,
      duplicate, ite_true, zeroAckRecovery, Recovery.duplicate, allowed, ite_false, Functor.map,
      Except.map, pure, Except.pure]

theorem receive_zero_ack_enabled (conditions : ZeroAckConditions state input recovery reaction) :
    ∃ after, ZeroAck state input recovery after := by
  have counted : inOrderCount state input = 0 := by
    unfold inOrderCount
    rw [conditions.acknowledgment, Seq.distance_self]
  have model := EstablishedReceive.receiveWithWindow_empty_forward state.core input reaction.window conditions.valid.1
    conditions.tuple conditions.controls conditions.ack conditions.sequence conditions.empty
    (by rw [conditions.acknowledgment, Seq.distance_self]; exact Nat.zero_le _)
  have modelEq : receiveModel state input = ⟨state.core, .accepted 0 0, none⟩ := by
    simpa only [receiveModel, conditions.ackRuntime, conditions.acknowledgment, Seq.distance_self,
      EstablishedReceive.commit, List.drop_zero, List.append_nil, List.length_nil, Seq.add_zero] using model
  have received : receiveInOrder state input =
      ⟨zeroAckState state input recovery, .accepted (.receive 0 0), none, [], none⟩ := by
    simp only [receiveInOrder, conditions.valid, conditions.coherent, conditions.prepared.1,
      not_true_eq_false, ite_false, modelEq, zero_receive_recovery conditions, issueRequest,
      conditions.ackRuntime, receiveState, conditions.runtime, Option.isSome_some, ite_true]
    unfold zeroAckState windowState
    split <;> simp only [conditions.ackRuntime] <;> rfl
  have old : recovery.Valid ∧ recovery.smss = state.effectiveMSS ∧
      Recovery.flight recovery = state.core.sent.length ∧ AckWindowKnown state := by
    simpa only [RecoveryCoherent, conditions.runtime] using conditions.coherent
  have newValid : (zeroAckRecovery state input recovery).Valid := by
    unfold zeroAckRecovery
    split <;> exact old.1
  have newMSS : (zeroAckRecovery state input recovery).smss = state.effectiveMSS := by
    unfold zeroAckRecovery
    split <;> exact old.2.1
  have newFlight : Recovery.flight (zeroAckRecovery state input recovery) = state.core.sent.length := by
    unfold zeroAckRecovery
    split <;> exact old.2.2.1
  have now : (zeroAckRecovery state input recovery).now = state.now := by
    simp only [State.now, conditions.runtime, Option.map_some, Option.getD_some]
    unfold zeroAckRecovery
    split <;> rfl
  have valid : (zeroAckState state input recovery).Valid := windowState_valid state _ _ conditions.valid
  have runtime : (zeroAckState state input recovery).recovery = some (zeroAckRecovery state input recovery) :=
    windowState_recovery state _ input.packet.segment
  have mss : (zeroAckState state input recovery).effectiveMSS = state.effectiveMSS := by
    unfold zeroAckState
    exact windowState_effectiveMSS state _ input.packet.segment
  have coherent : RecoveryCoherent (zeroAckState state input recovery) := by
    apply recoveryCoherent_of_runtime _ _ runtime newValid
    · exact newMSS.trans mss.symm
    · rw [zeroAckState, windowState_core]
      exact newFlight
    · exact ackWindowKnown_of_field _ input.packet.segment.window (windowState_lastAckWindow state _ _)
  have prepared : AckPrepared (zeroAckState state input recovery) :=
    windowState_ack_prepared state _ _ (withRecovery_ackPrepared state _ conditions.prepared now)
  have storage : StorageCoherent (zeroAckState state input recovery) :=
    windowState_storage_coherent state _ _ conditions.storage
  have raw : receiveRaw state input = receivePlain
      ⟨zeroAckState state input recovery, .accepted (.receive 0 0), none, [], none⟩ := by
    simp only [receiveRaw, conditions.valid, conditions.coherent, conditions.prepared.1, conditions.storage,
      not_true_eq_false, ite_false, prepare_empty_forward state input conditions.valid conditions.tuple conditions.controls
        conditions.ack conditions.sequence conditions.empty (by rw [counted]; exact Nat.zero_le _), received]
  refine ⟨zeroAckState state input recovery, ⟨⟨reaction, conditions⟩, rfl, ?_, valid, coherent, prepared, storage, runtime⟩⟩
  simp only [receiveEffect, raw, receivePlain, valid, storage.1, and_self, ite_true]

theorem ZeroAck.receive (received : ZeroAck state input recovery after) :
    receive state input = ⟨after, .accepted (.receive 0 0), none, [], none⟩ := congrArg ReceiveEffect.result received.effect

theorem ZeroAck.core (received : ZeroAck state input recovery after) : after.core = state.core := by
  rw [received.afterEq]
  exact windowState_core state _ input.packet.segment

theorem ZeroAck.ack_reaction (received : ZeroAck state input recovery after) : after.ackReaction = state.ackReaction := by
  rw [received.afterEq]
  exact windowState_ackReaction state _ input.packet.segment

theorem ZeroAck.store (received : ZeroAck state input recovery after) : after.receiveStore = state.receiveStore := by
  rw [received.afterEq]
  exact windowState_receiveStore state _ input.packet.segment

theorem ZeroAck.pending (received : ZeroAck state input recovery after) : after.pending = state.pending := by
  rw [received.afterEq]
  exact windowState_pending state _ input.packet.segment

theorem ZeroAck.window_space (received : ZeroAck state input recovery after)
    (old : count ≤ state.sendWindow) (incoming : count ≤ input.packet.segment.window.val) : count ≤ after.sendWindow := by
  rw [received.afterEq]
  unfold zeroAckState windowState
  split
  · exact incoming
  · exact old

end Netlib.Protocol.TCP.Endpoint
