import Netlib.Protocol.TCP.Segment

/-!
# TCP framing over the selected IPv4 profile

The TCP segment uses all bytes of the declared IPv4 payload.
Trailing link padding remains outside the transport segment.
-/

namespace Netlib.Protocol.TCP

structure DecodedIPv4 where
  ip : IPv4.Decoded
  segment : Segment
  deriving Repr, BEq, DecidableEq

def DecodedIPv4.header (value : DecodedIPv4) : Packet.Header :=
  ⟨value.ip.packet.source, value.ip.packet.destination, Packet.Protocol.tcp,
    value.segment.sourcePort, value.segment.destinationPort⟩

def DecodedIPv4.Valid (value : DecodedIPv4) : Prop :=
  value.ip.packet.protocol = Packet.Protocol.tcp ∧
    decode value.ip.packet.source value.ip.packet.destination value.ip.packet.payload = .ok value.segment

instance (value : DecodedIPv4) : Decidable value.Valid := by
  unfold DecodedIPv4.Valid
  cases decode value.ip.packet.source value.ip.packet.destination value.ip.packet.payload with
  | error error => simp; infer_instance
  | ok segment => simp only [Except.ok.injEq]; infer_instance

def decodeIPv4 (bytes : List UInt8) : Except String DecodedIPv4 := do
  let ip ← IPv4.decode bytes
  if ip.packet.protocol != Packet.Protocol.tcp then throw "The IPv4 protocol must be TCP."
  let segment ← decode ip.packet.source ip.packet.destination ip.packet.payload
  return ⟨ip, segment⟩

def encodeIPv4 (value : DecodedIPv4) : Except String (List UInt8) :=
  if value.Valid then IPv4.encodeDecoded value.ip
  else .error "The decoded TCP segment must agree with the IPv4 fields and all payload bytes."

theorem decodeIPv4_layers (bytes : List UInt8) (value : DecodedIPv4)
    (accepted : decodeIPv4 bytes = .ok value) :
    IPv4.decode bytes = .ok value.ip ∧ value.Valid := by
  cases ip : IPv4.decode bytes with
  | error error => simp [decodeIPv4, ip, bind, Except.bind] at accepted
  | ok decoded =>
    simp only [decodeIPv4, ip, bind, Except.bind] at accepted
    split at accepted
    · simp [throw] at accepted
    · rename_i protocol
      cases transport : decode decoded.packet.source decoded.packet.destination decoded.packet.payload with
      | error error => simp [transport] at accepted
      | ok segment =>
        simp [transport, pure] at accepted
        cases accepted
        exact ⟨rfl, by simpa [DecodedIPv4.Valid] using And.intro protocol transport⟩

theorem decodeIPv4_header (bytes : List UInt8) (value : DecodedIPv4)
    (accepted : decodeIPv4 bytes = .ok value) :
    value.header = ⟨value.ip.packet.source, value.ip.packet.destination, value.ip.packet.protocol,
      value.segment.sourcePort, value.segment.destinationPort⟩ := by
  simp [DecodedIPv4.header, (decodeIPv4_layers bytes value accepted).2.1]

theorem encodeIPv4_decodeIPv4 (bytes : List UInt8) (value : DecodedIPv4)
    (accepted : decodeIPv4 bytes = .ok value) : encodeIPv4 value = .ok bytes := by
  obtain ⟨ip, coherent⟩ := decodeIPv4_layers bytes value accepted
  rw [encodeIPv4, ite_eq_left coherent]
  exact IPv4.encode_decode bytes value.ip ip

theorem decodeIPv4_encodeIPv4 (value : DecodedIPv4) (bytes : List UInt8)
    (encoded : encodeIPv4 value = .ok bytes) : decodeIPv4 bytes = .ok value := by
  unfold encodeIPv4 at encoded
  split at encoded
  · rename_i coherent
    have ip := IPv4.decode_encodeDecoded value.ip bytes encoded
    have protocol := coherent.1
    simp [decodeIPv4, ip, protocol, coherent.2, bind, Except.bind, pure]
    rfl
  · cases encoded

end Netlib.Protocol.TCP
