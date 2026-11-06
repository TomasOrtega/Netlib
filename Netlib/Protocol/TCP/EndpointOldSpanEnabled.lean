import Netlib.Protocol.TCP.EndpointAckReceiveEnabled

namespace Netlib.Protocol.TCP.ReceiveWindow

theorem whole_old_span_rejected (start : Seq) (window consumed length : Nat)
    (positive : 0 < length) (inside : length ≤ consumed)
    (epoch : consumed + window ≤ Seq.modulus) :
    accepts (start.add consumed) window start length = false := by
  by_cases closed : window = 0
  · subst window
    exact positive_length_zero_window _ _ _ positive
  · have openWindow : 0 < window := by omega
    have bounded : consumed < Seq.modulus := by omega
    apply neither_endpoint _ _ _ _ openWindow positive
    · unfold Seq.InInterval
      have distance := Seq.distance_from_advanced start consumed 0 (by omega) bounded
      simp only [Seq.add_zero, Nat.sub_zero] at distance
      rw [distance]
      omega
    · unfold Seq.InInterval
      rw [Seq.distance_from_advanced start consumed (length - 1) (by omega) bounded]
      omega

theorem whole_old_span_segment_rejected (segment : Segment) (window consumed : Nat)
    (noSyn : Flags.syn segment.flags = false) (noFin : Flags.fin segment.flags = false)
    (positive : 0 < segment.payload.length) (inside : segment.payload.length ≤ consumed)
    (epoch : consumed + window ≤ Seq.modulus) :
    acceptsSegment (segment.sequence.add consumed) window segment = false := by
  rw [acceptsSegment, segmentLength_no_control segment noSyn noFin]
  exact whole_old_span_rejected segment.sequence window consumed segment.payload.length positive inside epoch

end Netlib.Protocol.TCP.ReceiveWindow

namespace Netlib.Protocol.TCP.Endpoint

theorem old_span_sequence (state : State) (input : Input) (consumed : Nat) (valid : state.Valid)
    (tuple : input.packet.header = state.core.inbound) (controls : EstablishedReceive.control input.packet.segment = none)
    (nonempty : input.packet.segment.payload ≠ []) (inside : input.packet.segment.payload.length ≤ consumed)
    (cursor : input.packet.segment.sequence.add consumed = state.core.receiveNext)
    (epoch : consumed + offeredWindow state ≤ Seq.modulus) :
    ReceiveReassembly.prepare state.core state.receiveStore input (offeredWindow state) state.now =
      .blocked (.reject .sequence) (some (ReceiveReassembly.request state.core (offeredWindow state) .sequence)) := by
  have outside : ReceiveWindow.acceptsSegment state.core.receiveNext (offeredWindow state) input.packet.segment = false := by
    rw [ReceiveWindow.acceptsSegment, EstablishedReceive.segmentLength_of_control_none _ controls, ← cursor]
    exact ReceiveWindow.whole_old_span_rejected input.packet.segment.sequence (offeredWindow state)
      consumed input.packet.segment.payload.length (List.length_pos_iff.mpr nonempty) inside epoch
  simp only [ReceiveReassembly.prepare, ReceiveReassembly.initialGate, valid.1, not_true_eq_false, ite_false,
    tuple, ne_eq, controls, outside, Bool.not_false, ite_true, Option.map_some]

theorem receive_old_span (state : State) (input : Input) (reaction : AckReaction.State) (consumed : Nat)
    (valid : state.Valid) (coherent : RecoveryCoherent state) (prepared : AckPrepared state)
    (storage : StorageCoherent state) (stored : state.ackReaction = some reaction)
    (tuple : input.packet.header = state.core.inbound) (controls : EstablishedReceive.control input.packet.segment = none)
    (nonempty : input.packet.segment.payload ≠ []) (inside : input.packet.segment.payload.length ≤ consumed)
    (cursor : input.packet.segment.sequence.add consumed = state.core.receiveNext)
    (epoch : consumed + offeredWindow state ≤ Seq.modulus) :
    receive state input =
      ⟨sequenceAfter state reaction, .reject (.input .sequence), none, [],
        some (ReceiveReassembly.request state.core (offeredWindow state) .sequence)⟩ ∧
      receiveRuns state input = [] ∧ receivedBytes state input = [] ∧
      AckPrepared (sequenceAfter state reaction) ∧ ResponseAvailable (sequenceAfter state reaction) true := by
  have plan := old_span_sequence state input consumed valid tuple controls nonempty inside cursor epoch
  have raw : receiveRaw state input = receivePlain
      ⟨sequenceAfter state reaction, .reject (.input .sequence), none, [],
        some (ReceiveReassembly.request state.core (offeredWindow state) .sequence)⟩ := by
    simp only [receiveRaw, valid, coherent, prepared.1, storage, not_true_eq_false, ite_false, plan,
      receiveStopped, issueRequest, stored, ReceiveReassembly.request, EstablishedReceive.request]
    rfl
  let effect : ReceiveEffect := receivePlain
    ⟨sequenceAfter state reaction, .reject (.input .sequence), none, [],
      some (ReceiveReassembly.request state.core (offeredWindow state) .sequence)⟩
  have afterValid : (sequenceAfter state reaction).Valid := valid
  have afterStorage : (sequenceAfter state reaction).StorageValid := storage.1
  have actual : receiveEffect state input = effect := by
    simp only [receiveEffect, raw, effect, receivePlain, afterValid, afterStorage, and_self, ite_true]
  refine ⟨congrArg ReceiveEffect.result actual, congrArg ReceiveEffect.runs actual, ?_,
    sequenceAfter_prepared state reaction stored prepared, sequenceAfter_dispatch state reaction⟩
  change ReceiveStore.bytes (receiveEffect state input).runs = []
  rw [congrArg ReceiveEffect.runs actual]
  rfl

theorem receive_old_span_emits_ack (state : State) (input : Input) (reaction : AckReaction.State) (consumed : Nat)
    (valid : state.Valid) (coherent : RecoveryCoherent state) (prepared : AckPrepared state)
    (storage : StorageCoherent state) (stored : state.ackReaction = some reaction)
    (tuple : input.packet.header = state.core.inbound) (controls : EstablishedReceive.control input.packet.segment = none)
    (nonempty : input.packet.segment.payload ≠ []) (inside : input.packet.segment.payload.length ≤ consumed)
    (cursor : input.packet.segment.sequence.add consumed = state.core.receiveNext)
    (epoch : consumed + offeredWindow state ≤ Seq.modulus) :
    ∃ output, receivedBytes state input = [] ∧
      dispatchAck (receive state input).state true =
        ⟨outputState (sequenceAfter state reaction), .accepted .dispatchAck, some output, [], none⟩ ∧
      emit (sequenceAfter state reaction) [] = .ok output ∧
      output.packet.segment.payload = [] ∧ output.packet.segment.acknowledgment = state.core.receiveNext := by
  obtain ⟨actual, _, bytes, afterPrepared, available⟩ :=
    receive_old_span state input reaction consumed valid coherent prepared storage stored tuple controls nonempty inside cursor epoch
  obtain ⟨output, emitted, encoded⟩ := dispatchAck_success_enabled (sequenceAfter state reaction) valid afterPrepared available
  have fields := emit_transport (sequenceAfter state reaction) [] output encoded
  exact ⟨output, bytes, by simpa only [actual] using emitted, encoded,
    emit_payload (sequenceAfter state reaction) [] output encoded, fields.2.2.1⟩

end Netlib.Protocol.TCP.Endpoint
