import Netlib.Protocol.TCP.EstablishedReceive
import Netlib.Protocol.TCP.MSS

/-!
# Checked TCP startup outputs

This constructor emits an empty SYN, SYN,ACK, or ACK packet.
It does not require an established application state.
The caller supplies local fields and output permission in the handshake model.
-/

namespace Netlib.Protocol.TCP.ControlOutput

abbrev Input := EstablishedReceive.Input

def Allowed (flags : UInt8) : Prop := flags = 2 ∨ flags = 18 ∨ flags = 16

instance (flags : UInt8) : Decidable (Allowed flags) := by unfold Allowed; infer_instance

def segment (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat) : Segment :=
  computed header.source header.destination {
    sourcePort := header.sourcePort
    destinationPort := header.destinationPort
    sequence := sequence
    acknowledgment := acknowledgment
    reserved := 0
    flags := flags
    window := ⟨window % 65536, Nat.mod_lt _ (by decide)⟩
    checksum := 0
    urgentPointer := 0
    options := []
    payload := [] }

def ipPacket (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat) : IPv4.Packet :=
  ⟨0, 0, true, 64, Packet.Protocol.tcp, header.source, header.destination,
    (segment header sequence acknowledgment flags window).encodeBytes⟩

def packet (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat) : DecodedIPv4 :=
  let ip := ipPacket header sequence acknowledgment flags window
  ⟨⟨ip, IPv4.computedChecksum ip, []⟩, segment header sequence acknowledgment flags window⟩

def bytes (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat) : List UInt8 :=
  let ip := ipPacket header sequence acknowledgment flags window
  IPv4.headerBytes ip (IPv4.computedChecksum ip) ++ ip.payload

theorem segment_encodable (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat) :
    (segment header sequence acknowledgment flags window).Encodable := by
  apply computed_encodable
  simp only [Segment.Encodable, Segment.wireLength, Segment.headerLength, List.length_nil,
    Nat.zero_le, Nat.zero_mod, Options.valid, true_and]
  decide

theorem ip_encodable (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat) :
    (ipPacket header sequence acknowledgment flags window).Encodable := by
  simp only [IPv4.Packet.Encodable, IPv4.Packet.wireLength, ipPacket, Segment.encodeBytes_length,
    segment, computed, rechecksum, Segment.wireLength, Segment.headerLength, List.length_nil]
  decide

theorem packet_valid (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat) :
    (packet header sequence acknowledgment flags window).Valid := by
  exact ⟨rfl, decode_encodeBytes _ _ _ (segment_encodable _ _ _ _ _) (computed_accepts _ _ _)⟩

theorem encoded (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat) :
    encodeIPv4 (packet header sequence acknowledgment flags window) = .ok (bytes header sequence acknowledgment flags window) := by
  rw [encodeIPv4, ite_eq_left (packet_valid _ _ _ _ _)]
  have valid := IPv4.computedChecksum_valid (ipPacket header sequence acknowledgment flags window)
  have size := ip_encodable header sequence acknowledgment flags window
  simp only [packet, IPv4.encodeDecoded, size, decide_true, Bool.not_true, Bool.false_eq_true,
    ite_false, valid, bind, Except.bind, pure, List.append_nil]
  rfl

def emit (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat) : Except String Input :=
  if header.protocol ≠ Packet.Protocol.tcp then .error "The control output requires a TCP tuple."
  else if ¬Allowed flags then .error "The control output requires SYN, SYN,ACK, or ACK."
  else if window > 65535 then .error "The control window exceeds its 16-bit field."
  else .ok ⟨bytes header sequence acknowledgment flags window,
    packet header sequence acknowledgment flags window, decodeIPv4_encodeIPv4 _ _ (encoded _ _ _ _ _)⟩

theorem emit_fields (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat)
    (value : Input) (accepted : emit header sequence acknowledgment flags window = .ok value) :
    header.protocol = Packet.Protocol.tcp ∧ Allowed flags ∧ window ≤ 65535 ∧
      value.bytes = bytes header sequence acknowledgment flags window ∧
      value.packet = packet header sequence acknowledgment flags window := by
  unfold emit at accepted
  split at accepted
  · cases accepted
  · rename_i transport
    split at accepted
    · cases accepted
    · rename_i flagsValid
      split at accepted
      · cases accepted
      · cases accepted
        exact ⟨by simpa using transport, by simpa using flagsValid, by omega, rfl, rfl⟩

theorem emit_transport (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat)
    (value : Input) (accepted : emit header sequence acknowledgment flags window = .ok value) :
    value.packet.header = header ∧ value.packet.segment.sequence = sequence ∧
      value.packet.segment.acknowledgment = acknowledgment ∧ value.packet.segment.window.val = window ∧
      value.packet.segment.flags = flags ∧ value.packet.segment.options = [] ∧
      value.packet.segment.payload = [] ∧ value.packet.segment.reserved = 0 ∧ value.packet.segment.urgentPointer = 0 := by
  obtain ⟨transport, _, bound, _, same⟩ := emit_fields _ _ _ _ _ _ accepted
  rw [same]
  have word : window % 65536 = window := Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, rfl, rfl, word, rfl, rfl, rfl, rfl, rfl⟩
  cases header
  simp_all only [packet, DecodedIPv4.header, ipPacket, segment, computed, rechecksum]

theorem emit_checksums (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat)
    (value : Input) (accepted : emit header sequence acknowledgment flags window = .ok value) :
    checksumAccepts value.packet.ip.packet.source value.packet.ip.packet.destination value.packet.segment = true ∧
      InternetChecksum.valid (IPv4.headerBytes value.packet.ip.packet value.packet.ip.checksum) = true := by
  rw [(emit_fields _ _ _ _ _ _ accepted).2.2.2.2]
  exact ⟨computed_accepts _ _ _, IPv4.computedChecksum_valid _⟩

theorem emit_exists (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat)
    (transport : header.protocol = Packet.Protocol.tcp) (allowed : Allowed flags) (bounded : window ≤ 65535) :
    ∃ value, emit header sequence acknowledgment flags window = .ok value := by
  simp only [emit, transport, ne_eq, not_true_eq_false, ite_false, allowed, Nat.not_lt.mpr bounded]
  exact ⟨_, rfl⟩

theorem emit_length (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat)
    (value : Input) (accepted : emit header sequence acknowledgment flags window = .ok value) : value.bytes.length = 40 := by
  rw [(emit_fields _ _ _ _ _ _ accepted).2.2.2.1]
  simp only [bytes, List.length_append, IPv4.headerBytes_length, ipPacket, Segment.encodeBytes_length,
    segment, computed, rechecksum, Segment.wireLength, Segment.headerLength, List.length_nil]

def outputOptions (offer : Option MSS.Value) : List UInt8 :=
  (offer.map MSS.encode).getD []

@[simp] theorem outputOptions_length (offer : Option MSS.Value) :
    (outputOptions offer).length = if offer.isSome then 4 else 0 := by
  cases offer <;> simp [outputOptions]

theorem outputOptions_valid (offer : Option MSS.Value) : Options.valid (outputOptions offer) = true := by
  cases offer with
  | none => simp [outputOptions]
  | some value => exact MSS.encode_valid value

def segmentWithMSS (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat)
    (offer : Option MSS.Value) : Segment :=
  computed header.source header.destination {
    sourcePort := header.sourcePort
    destinationPort := header.destinationPort
    sequence := sequence
    acknowledgment := acknowledgment
    reserved := 0
    flags := flags
    window := ⟨window % 65536, Nat.mod_lt _ (by decide)⟩
    checksum := 0
    urgentPointer := 0
    options := outputOptions offer
    payload := [] }

def ipPacketWithMSS (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat)
    (offer : Option MSS.Value) : IPv4.Packet :=
  ⟨0, 0, true, 64, Packet.Protocol.tcp, header.source, header.destination,
    (segmentWithMSS header sequence acknowledgment flags window offer).encodeBytes⟩

def packetWithMSS (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat)
    (offer : Option MSS.Value) : DecodedIPv4 :=
  let ip := ipPacketWithMSS header sequence acknowledgment flags window offer
  ⟨⟨ip, IPv4.computedChecksum ip, []⟩, segmentWithMSS header sequence acknowledgment flags window offer⟩

def bytesWithMSS (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat)
    (offer : Option MSS.Value) : List UInt8 :=
  let ip := ipPacketWithMSS header sequence acknowledgment flags window offer
  IPv4.headerBytes ip (IPv4.computedChecksum ip) ++ ip.payload

theorem segmentWithMSS_encodable (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat)
    (offer : Option MSS.Value) : (segmentWithMSS header sequence acknowledgment flags window offer).Encodable := by
  apply computed_encodable
  simp only [Segment.Encodable, Segment.wireLength, Segment.headerLength, List.length_nil,
    outputOptions_length, outputOptions_valid]
  cases offer <;> simp

theorem ipPacketWithMSS_encodable (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat)
    (offer : Option MSS.Value) : (ipPacketWithMSS header sequence acknowledgment flags window offer).Encodable := by
  simp only [IPv4.Packet.Encodable, IPv4.Packet.wireLength, ipPacketWithMSS, Segment.encodeBytes_length,
    segmentWithMSS, computed, rechecksum, Segment.wireLength, Segment.headerLength, List.length_nil, outputOptions_length]
  cases offer <;> simp

theorem packetWithMSS_valid (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat)
    (offer : Option MSS.Value) : (packetWithMSS header sequence acknowledgment flags window offer).Valid := by
  exact ⟨rfl, decode_encodeBytes _ _ _ (segmentWithMSS_encodable _ _ _ _ _ _) (computed_accepts _ _ _)⟩

theorem encodedWithMSS (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat)
    (offer : Option MSS.Value) :
    encodeIPv4 (packetWithMSS header sequence acknowledgment flags window offer) = .ok (bytesWithMSS header sequence acknowledgment flags window offer) := by
  rw [encodeIPv4, ite_eq_left (packetWithMSS_valid _ _ _ _ _ _)]
  have valid := IPv4.computedChecksum_valid (ipPacketWithMSS header sequence acknowledgment flags window offer)
  have size := ipPacketWithMSS_encodable header sequence acknowledgment flags window offer
  simp only [packetWithMSS, IPv4.encodeDecoded, size, decide_true, Bool.not_true, Bool.false_eq_true,
    ite_false, valid, bind, Except.bind, pure, List.append_nil]
  rfl

def emitWithMSS (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat)
    (offer : Option MSS.Value) : Except String Input :=
  if header.protocol ≠ Packet.Protocol.tcp then .error "The control output requires a TCP tuple."
  else if ¬Allowed flags then .error "The control output requires SYN, SYN,ACK, or ACK."
  else if window > 65535 then .error "The control window exceeds its 16-bit field."
  else if offer.isSome = false ∨ flags = 2 ∨ flags = 18 then
    .ok ⟨bytesWithMSS header sequence acknowledgment flags window offer,
      packetWithMSS header sequence acknowledgment flags window offer,
      decodeIPv4_encodeIPv4 _ _ (encodedWithMSS _ _ _ _ _ _)⟩
  else .error "An MSS advertisement requires SYN or SYN,ACK output."

@[simp] theorem emitWithMSS_none (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat) :
    emitWithMSS header sequence acknowledgment flags window none = emit header sequence acknowledgment flags window := rfl

theorem emitWithMSS_fields (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat)
    (offer : Option MSS.Value) (value : Input)
    (accepted : emitWithMSS header sequence acknowledgment flags window offer = .ok value) :
    header.protocol = Packet.Protocol.tcp ∧ Allowed flags ∧ window ≤ 65535 ∧
      (offer.isSome = true → flags = 2 ∨ flags = 18) ∧
      value.bytes = bytesWithMSS header sequence acknowledgment flags window offer ∧
      value.packet = packetWithMSS header sequence acknowledgment flags window offer := by
  unfold emitWithMSS at accepted
  split at accepted
  · cases accepted
  · rename_i transport
    split at accepted
    · cases accepted
    · rename_i flagsValid
      split at accepted
      · cases accepted
      · split at accepted
        · rename_i placement
          cases accepted
          exact ⟨by simpa using transport, by simpa using flagsValid, by omega,
            by intro present; exact placement.resolve_left (by rw [present]; decide), rfl, rfl⟩
        · cases accepted

theorem emitWithMSS_transport (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat)
    (offer : Option MSS.Value) (value : Input)
    (accepted : emitWithMSS header sequence acknowledgment flags window offer = .ok value) :
    value.packet.header = header ∧ value.packet.segment.sequence = sequence ∧
      value.packet.segment.acknowledgment = acknowledgment ∧ value.packet.segment.window.val = window ∧
      value.packet.segment.flags = flags ∧ value.packet.segment.options = outputOptions offer ∧
      value.packet.segment.payload = [] ∧ value.packet.segment.reserved = 0 ∧ value.packet.segment.urgentPointer = 0 := by
  obtain ⟨transport, _, bound, _, _, same⟩ := emitWithMSS_fields _ _ _ _ _ _ _ accepted
  rw [same]
  have word : window % 65536 = window := Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, rfl, rfl, word, rfl, rfl, rfl, rfl, rfl⟩
  cases header
  simp_all only [packetWithMSS, DecodedIPv4.header, ipPacketWithMSS, segmentWithMSS, computed, rechecksum]

theorem emitWithMSS_checksums (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat)
    (offer : Option MSS.Value) (value : Input)
    (accepted : emitWithMSS header sequence acknowledgment flags window offer = .ok value) :
    checksumAccepts value.packet.ip.packet.source value.packet.ip.packet.destination value.packet.segment = true ∧
      InternetChecksum.valid (IPv4.headerBytes value.packet.ip.packet value.packet.ip.checksum) = true := by
  rw [(emitWithMSS_fields _ _ _ _ _ _ _ accepted).2.2.2.2.2]
  exact ⟨computed_accepts _ _ _, IPv4.computedChecksum_valid _⟩

theorem emitWithMSS_exists (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat)
    (offer : Option MSS.Value) (transport : header.protocol = Packet.Protocol.tcp) (allowed : Allowed flags)
    (bounded : window ≤ 65535) (placement : offer.isSome = true → flags = 2 ∨ flags = 18) :
    ∃ value, emitWithMSS header sequence acknowledgment flags window offer = .ok value := by
  have selected : offer.isSome = false ∨ flags = 2 ∨ flags = 18 := by
    cases offer with
    | none => exact .inl rfl
    | some value => exact .inr (placement rfl)
  simp only [emitWithMSS, transport, ne_eq, not_true_eq_false, ite_false, allowed, Nat.not_lt.mpr bounded, selected, ite_true]
  exact ⟨_, rfl⟩

theorem emitWithMSS_length (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8) (window : Nat)
    (offer : Option MSS.Value) (value : Input)
    (accepted : emitWithMSS header sequence acknowledgment flags window offer = .ok value) :
    value.bytes.length = 40 + (outputOptions offer).length := by
  rw [(emitWithMSS_fields _ _ _ _ _ _ _ accepted).2.2.2.2.1]
  simp only [bytesWithMSS, List.length_append, IPv4.headerBytes_length, ipPacketWithMSS, Segment.encodeBytes_length,
    segmentWithMSS, computed, rechecksum, Segment.wireLength, Segment.headerLength, List.length_nil]
  omega

end Netlib.Protocol.TCP.ControlOutput
