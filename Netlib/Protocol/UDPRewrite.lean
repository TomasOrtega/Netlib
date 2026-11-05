import Netlib.Protocol.UDP

/-!
# Payload-preserving IPv4 UDP rewriting

The target supplies the translated tuple and the caller supplies the next TTL.
Payload, TOS, identification, and DF are preserved. Output omits link padding.
An omitted UDP checksum stays omitted; present checksums and the IPv4 checksum
are computed over the changed fields.
-/

namespace Netlib.Protocol.UDPRewrite

open InternetChecksum

def SourceValid (input : UDP.DecodedIPv4) : Prop :=
  input.Valid ∧ input.ip.packet.Encodable ∧
    InternetChecksum.valid (IPv4.headerBytes input.ip.packet input.ip.checksum) = true

theorem sourceValid_of_decoded (bytes : List UInt8) (input : UDP.DecodedIPv4)
    (accepted : UDP.decodeIPv4 bytes = .ok input) : SourceValid input := by
  obtain ⟨decoded, coherent⟩ := UDP.decodeIPv4_layers bytes input accepted
  exact ⟨coherent, IPv4.decode_valid bytes input.ip decoded⟩

theorem sourceValid_of_encoded (input : UDP.DecodedIPv4) (bytes : List UInt8)
    (encoded : UDP.encodeIPv4 input = .ok bytes) : SourceValid input :=
  sourceValid_of_decoded bytes input (UDP.decodeIPv4_encodeIPv4 input bytes encoded)

def datagram (input : UDP.DecodedIPv4) (target : Packet.Header) : UDP.Datagram :=
  if input.datagram.checksum = 0 then
    ⟨target.sourcePort, target.destinationPort, 0, input.datagram.payload⟩
  else UDP.computed target.source target.destination target.sourcePort target.destinationPort input.datagram.payload

@[simp] theorem datagram_payload (input : UDP.DecodedIPv4) (target : Packet.Header) :
    (datagram input target).payload = input.datagram.payload := by
  unfold datagram
  split <;> rfl

@[simp] theorem datagram_sourcePort (input : UDP.DecodedIPv4) (target : Packet.Header) :
    (datagram input target).sourcePort = target.sourcePort := by
  unfold datagram
  split <;> rfl

@[simp] theorem datagram_destinationPort (input : UDP.DecodedIPv4) (target : Packet.Header) :
    (datagram input target).destinationPort = target.destinationPort := by
  unfold datagram
  split <;> rfl

theorem datagram_encodable (input : UDP.DecodedIPv4) (target : Packet.Header) (valid : SourceValid input) :
    (datagram input target).Encodable := by
  have bounded := (UDP.decode_fields _ _ _ _ valid.1.2).1
  simpa only [UDP.Datagram.Encodable, UDP.Datagram.wireLength, datagram_payload] using bounded

theorem datagram_accepts (input : UDP.DecodedIPv4) (target : Packet.Header) :
    UDP.checksumAccepts target.source target.destination (datagram input target) = true := by
  unfold datagram
  split
  · simp [UDP.checksumAccepts]
  · exact UDP.computed_accepts _ _ _ _ _

theorem datagram_checksum_omitted_iff (input : UDP.DecodedIPv4) (target : Packet.Header) :
    (datagram input target).checksum = 0 ↔ input.datagram.checksum = 0 := by
  unfold datagram
  split
  · simp_all
  · exact iff_of_false (UDP.computed_nonzero _ _ _ _ _) (by assumption)

def ipPacket (input : UDP.DecodedIPv4) (target : Packet.Header) (ttl : UInt8) : IPv4.Packet :=
  { tos := input.ip.packet.tos
    identification := input.ip.packet.identification
    dontFragment := input.ip.packet.dontFragment
    ttl := ttl
    protocol := target.protocol
    source := target.source
    destination := target.destination
    payload := (datagram input target).encodeBytes }

theorem ipPacket_length (input : UDP.DecodedIPv4) (target : Packet.Header) (ttl : UInt8) (valid : SourceValid input) :
    (ipPacket input target ttl).wireLength = input.ip.packet.wireLength := by
  have sourceLength := UDP.decode_length _ _ _ _ valid.1.2
  simp only [IPv4.Packet.wireLength, ipPacket, UDP.Datagram.encodeBytes_length,
    UDP.Datagram.wireLength, datagram_payload]
  rw [sourceLength]
  rfl

theorem ipPacket_encodable (input : UDP.DecodedIPv4) (target : Packet.Header) (ttl : UInt8) (valid : SourceValid input) :
    (ipPacket input target ttl).Encodable := by
  unfold IPv4.Packet.Encodable
  rw [ipPacket_length input target ttl valid]
  exact valid.2.1

def transformed (input : UDP.DecodedIPv4) (target : Packet.Header) (ttl : UInt8) : UDP.DecodedIPv4 :=
  ⟨⟨ipPacket input target ttl, IPv4.computedChecksum (ipPacket input target ttl), []⟩, datagram input target⟩

def wireBytes (input : UDP.DecodedIPv4) (target : Packet.Header) (ttl : UInt8) : List UInt8 :=
  IPv4.headerBytes (ipPacket input target ttl) (IPv4.computedChecksum (ipPacket input target ttl)) ++
    (ipPacket input target ttl).payload

theorem transformed_header (input : UDP.DecodedIPv4) (target : Packet.Header) (ttl : UInt8)
    (transport : target.protocol = Packet.Protocol.udp) : (transformed input target ttl).header = target := by
  cases target
  simp_all [transformed, UDP.DecodedIPv4.header, ipPacket]

theorem transformed_valid (input : UDP.DecodedIPv4) (target : Packet.Header) (ttl : UInt8)
    (valid : SourceValid input) (transport : target.protocol = Packet.Protocol.udp) :
    (transformed input target ttl).Valid := by
  refine ⟨transport, ?_⟩
  exact UDP.decode_encodeBytes target.source target.destination (datagram input target)
    (datagram_encodable input target valid) (datagram_accepts input target)

theorem transformed_encoded (input : UDP.DecodedIPv4) (target : Packet.Header) (ttl : UInt8)
    (valid : SourceValid input) (transport : target.protocol = Packet.Protocol.udp) :
    UDP.encodeIPv4 (transformed input target ttl) = .ok (wireBytes input target ttl) := by
  rw [UDP.encodeIPv4, ite_eq_left (transformed_valid input target ttl valid transport)]
  have bounded := ipPacket_encodable input target ttl valid
  have checked := IPv4.computedChecksum_valid (ipPacket input target ttl)
  simp only [IPv4.encodeDecoded, transformed, bounded, decide_true, Bool.not_true,
    Bool.false_eq_true, ite_false, checked, bind, Except.bind, pure, List.append_nil]
  rfl

structure Certified (input : UDP.DecodedIPv4) (target : Packet.Header) (ttl : UInt8) where
  packet : UDP.DecodedIPv4
  bytes : List UInt8
  generated : packet = transformed input target ttl
  encoded : UDP.encodeIPv4 packet = .ok bytes

def rewrite (input : UDP.DecodedIPv4) (target : Packet.Header) (ttl : UInt8)
    (valid : SourceValid input) (transport : target.protocol = Packet.Protocol.udp) : Certified input target ttl :=
  ⟨transformed input target ttl, wireBytes input target ttl, rfl, transformed_encoded input target ttl valid transport⟩

namespace Certified

variable {input : UDP.DecodedIPv4} {target : Packet.Header} {nextTTL : UInt8}

theorem decoded (result : Certified input target nextTTL) : UDP.decodeIPv4 result.bytes = .ok result.packet :=
  UDP.decodeIPv4_encodeIPv4 result.packet result.bytes result.encoded

theorem target_udp (result : Certified input target nextTTL) : target.protocol = Packet.Protocol.udp := by
  have protocol := (UDP.decodeIPv4_layers _ _ result.decoded).2.1
  rw [result.generated] at protocol
  exact protocol

theorem header (result : Certified input target nextTTL) (transport : target.protocol = Packet.Protocol.udp) :
    result.packet.header = target := by
  rw [result.generated]
  exact transformed_header input target nextTTL transport

theorem payload (result : Certified input target nextTTL) : result.packet.datagram.payload = input.datagram.payload := by
  rw [result.generated]
  exact datagram_payload _ _

theorem ttl (result : Certified input target nextTTL) : result.packet.ip.packet.ttl = nextTTL := by
  rw [result.generated]
  rfl

theorem metadata (result : Certified input target nextTTL) :
    result.packet.ip.packet.tos = input.ip.packet.tos ∧
      result.packet.ip.packet.identification = input.ip.packet.identification ∧
      result.packet.ip.packet.dontFragment = input.ip.packet.dontFragment := by
  rw [result.generated]
  exact ⟨rfl, rfl, rfl⟩

theorem padding (result : Certified input target nextTTL) : result.packet.ip.padding = [] := by
  rw [result.generated]
  rfl

theorem checksum_omitted_iff (result : Certified input target nextTTL) :
    result.packet.datagram.checksum = 0 ↔ input.datagram.checksum = 0 := by
  rw [result.generated]
  exact datagram_checksum_omitted_iff input target

theorem ipv4_checksum (result : Certified input target nextTTL) :
    InternetChecksum.valid (IPv4.headerBytes result.packet.ip.packet result.packet.ip.checksum) = true :=
  (IPv4.decode_valid _ _ (UDP.decodeIPv4_layers _ _ result.decoded).1).2

theorem udp_checksum (result : Certified input target nextTTL) (present : input.datagram.checksum ≠ 0) :
    InternetChecksum.valid (UDP.pseudoHeader result.packet.ip.packet.source result.packet.ip.packet.destination
      result.packet.datagram.lengthWord ++ result.packet.ip.packet.payload) = true := by
  have nonzero : result.packet.datagram.checksum ≠ 0 := fun zero => present (result.checksum_omitted_iff.mp zero)
  exact UDP.decode_verified _ _ _ _ (UDP.decodeIPv4_layers _ _ result.decoded).2.2 nonzero

theorem length (result : Certified input target nextTTL) (valid : SourceValid input) :
    result.packet.ip.packet.wireLength = input.ip.packet.wireLength := by
  rw [result.generated]
  exact ipPacket_length input target nextTTL valid

theorem bytes_length (result : Certified input target nextTTL) :
    result.bytes.length = result.packet.ip.packet.wireLength := by
  have encoded : IPv4.encodeDecoded result.packet.ip = .ok result.bytes := by
    have accepted := result.encoded
    unfold UDP.encodeIPv4 at accepted
    split at accepted
    · exact accepted
    · cases accepted
  obtain ⟨bounded, checked⟩ := IPv4.encodeDecoded_valid _ _ encoded
  simp only [IPv4.encodeDecoded, bounded, decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
    checked, bind, Except.bind, pure] at encoded
  have exactBytes := Except.ok.inj encoded
  rw [← exactBytes, List.length_append, List.length_append, IPv4.headerBytes_length, result.padding]
  simp [IPv4.Packet.wireLength, Nat.add_comm]

end Certified
end Netlib.Protocol.UDPRewrite
