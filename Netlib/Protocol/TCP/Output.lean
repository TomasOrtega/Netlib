import Netlib.Protocol.TCP.EstablishedReceive

/-!
# Checked output for the bounded TCP endpoint

The output uses the current cursors and local receive window.
It has ACK, no options, and the reverse endpoint tuple.
The caller supplies send limits and policy permission in the endpoint module.
These bytes do not prove native transmission.
-/

namespace Netlib.Protocol.TCP.Output

namespace ER
export EstablishedReceive (State Input)
end ER

def reverse (header : Packet.Header) : Packet.Header :=
  ⟨header.destination, header.source, header.protocol, header.destinationPort, header.sourcePort⟩

def segment (state : ER.State) (payload : List UInt8) : Segment :=
  computed state.inbound.destination state.inbound.source {
    sourcePort := state.inbound.destinationPort
    destinationPort := state.inbound.sourcePort
    sequence := state.sendNext
    acknowledgment := state.receiveNext
    reserved := 0
    flags := 16
    window := ⟨state.window % 65536, Nat.mod_lt _ (by decide)⟩
    checksum := 0
    urgentPointer := 0
    options := []
    payload := payload }

def ipPacket (state : ER.State) (payload : List UInt8) : IPv4.Packet :=
  ⟨0, 0, true, 64, Packet.Protocol.tcp, state.inbound.destination, state.inbound.source,
    (segment state payload).encodeBytes⟩

def packet (state : ER.State) (payload : List UInt8) : DecodedIPv4 :=
  ⟨⟨ipPacket state payload, IPv4.computedChecksum (ipPacket state payload), []⟩, segment state payload⟩

def bytes (state : ER.State) (payload : List UInt8) : List UInt8 :=
  IPv4.headerBytes (ipPacket state payload) (IPv4.computedChecksum (ipPacket state payload)) ++
    (ipPacket state payload).payload

theorem segment_encodable (state : ER.State) (payload : List UInt8)
    (bounded : 40 + payload.length ≤ 65535) : (segment state payload).Encodable := by
  apply computed_encodable
  simp only [Segment.Encodable, Segment.wireLength, Segment.headerLength, List.length_nil,
    Nat.zero_le, Nat.zero_mod, Options.valid, true_and, Nat.add_zero]
  omega

theorem ip_encodable (state : ER.State) (payload : List UInt8)
    (bounded : 40 + payload.length ≤ 65535) : (ipPacket state payload).Encodable := by
  simp only [IPv4.Packet.Encodable, IPv4.Packet.wireLength, ipPacket, Segment.encodeBytes_length,
    segment, computed, rechecksum, Segment.wireLength, Segment.headerLength, List.length_nil]
  omega

theorem packet_valid (state : ER.State) (payload : List UInt8)
    (bounded : 40 + payload.length ≤ 65535) : (packet state payload).Valid := by
  refine ⟨rfl, ?_⟩
  exact decode_encodeBytes _ _ (segment state payload) (segment_encodable state payload bounded)
    (computed_accepts _ _ _)

theorem encoded (state : ER.State) (payload : List UInt8)
    (bounded : 40 + payload.length ≤ 65535) : encodeIPv4 (packet state payload) = .ok (bytes state payload) := by
  rw [encodeIPv4, ite_eq_left (packet_valid state payload bounded)]
  have valid := IPv4.computedChecksum_valid (ipPacket state payload)
  have size := ip_encodable state payload bounded
  simp only [packet, IPv4.encodeDecoded, size, decide_true, Bool.not_true, Bool.false_eq_true,
    ite_false, valid, bind, Except.bind, pure, List.append_nil]
  rfl

def emit (state : ER.State) (payload : List UInt8) : Except String ER.Input :=
  if state.Valid then
    if bounded : 40 + payload.length ≤ 65535 then
      .ok ⟨bytes state payload, packet state payload,
        decodeIPv4_encodeIPv4 _ _ (encoded state payload bounded)⟩
    else .error "The TCP output exceeds the IPv4 size limit."
  else .error "The TCP output requires a valid endpoint state."

theorem emit_fields (state : ER.State) (payload : List UInt8) (value : ER.Input)
    (accepted : emit state payload = .ok value) :
    state.Valid ∧ 40 + payload.length ≤ 65535 ∧
      value.bytes = bytes state payload ∧ value.packet = packet state payload := by
  unfold emit at accepted
  split at accepted
  · rename_i valid
    split at accepted
    · rename_i bounded
      cases accepted
      exact ⟨valid, bounded, rfl, rfl⟩
    · cases accepted
  · cases accepted

theorem emit_payload (state : ER.State) (payload : List UInt8) (value : ER.Input)
    (accepted : emit state payload = .ok value) : value.packet.segment.payload = payload := by
  rw [(emit_fields state payload value accepted).2.2.2]
  rfl

theorem emit_transport (state : ER.State) (payload : List UInt8) (value : ER.Input)
    (accepted : emit state payload = .ok value) :
    value.packet.header = reverse state.inbound ∧
      value.packet.segment.sequence = state.sendNext ∧
      value.packet.segment.acknowledgment = state.receiveNext ∧
      value.packet.segment.window.val = state.window ∧
      value.packet.segment.flags = 16 ∧ value.packet.segment.reserved = 0 ∧
      value.packet.segment.options = [] ∧ value.packet.segment.urgentPointer = 0 := by
  obtain ⟨valid, _, _, same⟩ := emit_fields state payload value accepted
  rw [same]
  have bound := EstablishedReceive.State.window_bound state valid
  have word : state.window % 65536 = state.window := Nat.mod_eq_of_lt (by omega)
  have protocol := valid.1
  refine ⟨?_, rfl, rfl, word, rfl, rfl, rfl, rfl⟩
  simp only [packet, DecodedIPv4.header, ipPacket, segment, computed, rechecksum, reverse, protocol]

theorem emit_checksums (state : ER.State) (payload : List UInt8) (value : ER.Input)
    (accepted : emit state payload = .ok value) :
    checksumAccepts value.packet.ip.packet.source value.packet.ip.packet.destination value.packet.segment = true ∧
      InternetChecksum.valid (IPv4.headerBytes value.packet.ip.packet value.packet.ip.checksum) = true := by
  rw [(emit_fields state payload value accepted).2.2.2]
  exact ⟨computed_accepts _ _ _, IPv4.computedChecksum_valid _⟩

theorem emit_exists (state : ER.State) (payload : List UInt8) (valid : state.Valid)
    (bounded : 40 + payload.length ≤ 65535) : ∃ value, emit state payload = .ok value := by
  simp only [emit, valid, ite_true, bounded, dite_true]
  exact ⟨_, rfl⟩

end Netlib.Protocol.TCP.Output
