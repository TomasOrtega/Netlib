import Netlib.Protocol.TCP.EndpointAckReceiveEnabled

/-!
# Endpoint fields after an empty ACK without recovery

An ACK at the send cursor retires no bytes.
The receive operation can update the peer window and its markers.
All other endpoint fields remain unchanged, including existing buffers and storage.
-/

namespace Netlib.Protocol.TCP.Endpoint

theorem receive_empty_ack (state : State) (input : Input) (valid : state.Valid)
    (disabled : state.recovery = none) (ackDisabled : state.ackReaction = none)
    (storage : state.StorageValid) (tuple : input.packet.header = state.core.inbound)
    (flags : input.packet.segment.flags = 16) (options : input.packet.segment.options = [])
    (empty : input.packet.segment.payload = [])
    (sequence : input.packet.segment.sequence = state.core.receiveNext)
    (acknowledgment : input.packet.segment.acknowledgment = state.core.sendUna) :
    receive state input =
      ⟨windowState state state input.packet.segment, .accepted (.receive 0 0), none, [], none⟩ := by
  have controls : EstablishedReceive.control input.packet.segment = none := by
    simp only [EstablishedReceive.control, flags, options]
    rfl
  have ack : Flags.ack input.packet.segment.flags = true := by rw [flags]; rfl
  have forward : Seq.distance state.core.sendUna input.packet.segment.acknowledgment ≤ state.core.sent.length := by
    simp only [acknowledgment, Seq.distance_self, Nat.zero_le]
  have core : EstablishedReceive.receive state.core input = ⟨state.core, .accepted 0 0, none⟩ := by
    have actual := EstablishedReceive.receive_in_order_of_forward state.core input valid.1 tuple controls ack sequence
      (by simp only [empty, List.length_nil, Nat.zero_le]) forward
    simpa only [empty, acknowledgment, Seq.distance_self, List.length_nil, List.isEmpty_nil, ite_true,
      EstablishedReceive.commit, Seq.add_zero, List.append_nil, List.drop_zero] using actual
  have counted : inOrderCount state input = 0 := by
    simp only [inOrderCount, acknowledgment, Seq.distance_self]
  have plan := prepare_empty_forward state input valid tuple controls ack sequence empty
    (by rw [counted]; exact Nat.zero_le _)
  rw [counted] at plan
  have actual : receiveInOrder state input =
      ⟨windowState state state input.packet.segment, .accepted (.receive 0 0), none, [], none⟩ := by
    rw [receiveInOrder_without_recovery state input valid disabled ackDisabled, core]
    simp only [receiveState, disabled, Option.isSome_none, Bool.false_eq_true, ite_false]
    have retained : { state with recovery := none } = state := by rw [← disabled]
    rw [retained]
  have recoveryCoherent : RecoveryCoherent state := by simp only [RecoveryCoherent, disabled]
  have ackCoherent : AckCoherent state := by simp only [AckCoherent, ackDisabled]
  have storageCoherent : StorageCoherent state := ⟨storage, by simp only [ackDisabled]⟩
  have raw : receiveRaw state input = receivePlain
      ⟨windowState state state input.packet.segment, .accepted (.receive 0 0), none, [], none⟩ := by
    simp only [receiveRaw, valid, recoveryCoherent, ackCoherent, storageCoherent, not_true_eq_false,
      ite_false, plan, actual]
  have finalValid := windowState_valid state state input.packet.segment valid
  have finalStorage : (windowState state state input.packet.segment).StorageValid := by
    unfold windowState
    split <;> exact storage
  simp only [receive, receiveEffect, raw, receivePlain, finalValid, finalStorage, and_self, ite_true]

theorem receive_empty_ack_initial (state : State) (input : Input) (valid : state.Valid)
    (disabled : state.recovery = none) (ackDisabled : state.ackReaction = none)
    (initial : state.receiveStore = ReceiveStore.initial) (tuple : input.packet.header = state.core.inbound)
    (flags : input.packet.segment.flags = 16) (options : input.packet.segment.options = [])
    (empty : input.packet.segment.payload = [])
    (sequence : input.packet.segment.sequence = state.core.receiveNext)
    (acknowledgment : input.packet.segment.acknowledgment = state.core.sendUna) :
    receive state input =
      ⟨windowState state state input.packet.segment, .accepted (.receive 0 0), none, [], none⟩ :=
  receive_empty_ack state input valid disabled ackDisabled
    (storage_valid_of_empty state (by rw [initial]; rfl)) tuple flags options empty sequence acknowledgment

theorem receive_empty_ack_frame (state : State) (input : Input) (valid : state.Valid)
    (disabled : state.recovery = none) (ackDisabled : state.ackReaction = none)
    (storage : state.StorageValid) (tuple : input.packet.header = state.core.inbound)
    (flags : input.packet.segment.flags = 16) (options : input.packet.segment.options = [])
    (empty : input.packet.segment.payload = [])
    (sequence : input.packet.segment.sequence = state.core.receiveNext)
    (acknowledgment : input.packet.segment.acknowledgment = state.core.sendUna) :
    ∃ window first second, (receive state input).state =
      { state with sendWindow := window, sendWL1 := first, sendWL2 := second } := by
  rw [receive_empty_ack state input valid disabled ackDisabled storage tuple flags options empty sequence acknowledgment]
  dsimp only
  unfold windowState
  split
  · exact ⟨input.packet.segment.window.val, input.packet.segment.sequence, input.packet.segment.acknowledgment, rfl⟩
  · exact ⟨state.sendWindow, state.sendWL1, state.sendWL2, rfl⟩

end Netlib.Protocol.TCP.Endpoint
