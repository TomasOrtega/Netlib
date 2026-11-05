import Netlib.Protocol.TCP.IPv4
import Netlib.Protocol.FlowNAT

/-!
# Payload-preserving IPv4 TCP rewriting

The target supplies the translated tuple and the caller supplies the next TTL.
The rewrite keeps the payload, transport control fields, options, and received reserved bits.
The two checksum calculations include the changed fields. The output has no link padding.
-/

namespace Netlib.Protocol.TCPRewrite

open InternetChecksum

def SourceValid (input : TCP.DecodedIPv4) : Prop :=
  input.Valid ∧ input.ip.packet.Encodable ∧
    InternetChecksum.valid (IPv4.headerBytes input.ip.packet input.ip.checksum) = true

theorem sourceValid_of_decoded (bytes : List UInt8) (input : TCP.DecodedIPv4)
    (accepted : TCP.decodeIPv4 bytes = .ok input) : SourceValid input := by
  obtain ⟨decoded, coherent⟩ := TCP.decodeIPv4_layers bytes input accepted
  exact ⟨coherent, IPv4.decode_valid bytes input.ip decoded⟩

theorem sourceValid_of_encoded (input : TCP.DecodedIPv4) (bytes : List UInt8)
    (encoded : TCP.encodeIPv4 input = .ok bytes) : SourceValid input :=
  sourceValid_of_decoded bytes input (TCP.decodeIPv4_encodeIPv4 input bytes encoded)

def segment (input : TCP.DecodedIPv4) (target : Packet.Header) : TCP.Segment :=
  TCP.rechecksum target.source target.destination
    { input.segment with sourcePort := target.sourcePort, destinationPort := target.destinationPort }

@[simp] theorem segment_payload (input : TCP.DecodedIPv4) (target : Packet.Header) :
    (segment input target).payload = input.segment.payload := rfl

@[simp] theorem segment_sourcePort (input : TCP.DecodedIPv4) (target : Packet.Header) :
    (segment input target).sourcePort = target.sourcePort := rfl

@[simp] theorem segment_destinationPort (input : TCP.DecodedIPv4) (target : Packet.Header) :
    (segment input target).destinationPort = target.destinationPort := rfl

@[simp] theorem segment_options (input : TCP.DecodedIPv4) (target : Packet.Header) :
    (segment input target).options = input.segment.options := rfl

@[simp] theorem segment_headerLength (input : TCP.DecodedIPv4) (target : Packet.Header) :
    (segment input target).headerLength = input.segment.headerLength := rfl

theorem segment_transport (input : TCP.DecodedIPv4) (target : Packet.Header) :
    (segment input target).sequence = input.segment.sequence ∧
      (segment input target).acknowledgment = input.segment.acknowledgment ∧
      (segment input target).reserved = input.segment.reserved ∧
      (segment input target).flags = input.segment.flags ∧
      (segment input target).window = input.segment.window ∧
      (segment input target).urgentPointer = input.segment.urgentPointer ∧
      (segment input target).options = input.segment.options := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem segment_encodable (input : TCP.DecodedIPv4) (target : Packet.Header) (valid : SourceValid input) :
    (segment input target).Encodable := by
  have bounded := (TCP.decode_fields _ _ _ _ valid.1.2).1
  apply TCP.rechecksum_encodable
  simpa only [TCP.Segment.Encodable, TCP.Segment.wireLength, TCP.Segment.headerLength] using bounded

theorem segment_accepts (input : TCP.DecodedIPv4) (target : Packet.Header) :
    TCP.checksumAccepts target.source target.destination (segment input target) = true := TCP.rechecksum_accepts _ _ _

def ipPacket (input : TCP.DecodedIPv4) (target : Packet.Header) (ttl : UInt8) : IPv4.Packet :=
  { tos := input.ip.packet.tos
    identification := input.ip.packet.identification
    dontFragment := input.ip.packet.dontFragment
    ttl := ttl
    protocol := target.protocol
    source := target.source
    destination := target.destination
    payload := (segment input target).encodeBytes }

theorem ipPacket_length (input : TCP.DecodedIPv4) (target : Packet.Header) (ttl : UInt8) (valid : SourceValid input) :
    (ipPacket input target ttl).wireLength = input.ip.packet.wireLength := by
  have sourceLength := TCP.decode_length _ _ _ _ valid.1.2
  simp only [IPv4.Packet.wireLength, ipPacket, TCP.Segment.encodeBytes_length,
    TCP.Segment.wireLength, segment_headerLength, segment_payload]
  rw [sourceLength]
  rfl

theorem ipPacket_encodable (input : TCP.DecodedIPv4) (target : Packet.Header) (ttl : UInt8) (valid : SourceValid input) :
    (ipPacket input target ttl).Encodable := by
  unfold IPv4.Packet.Encodable
  rw [ipPacket_length input target ttl valid]
  exact valid.2.1

def transformed (input : TCP.DecodedIPv4) (target : Packet.Header) (ttl : UInt8) : TCP.DecodedIPv4 :=
  ⟨⟨ipPacket input target ttl, IPv4.computedChecksum (ipPacket input target ttl), []⟩, segment input target⟩

def wireBytes (input : TCP.DecodedIPv4) (target : Packet.Header) (ttl : UInt8) : List UInt8 :=
  IPv4.headerBytes (ipPacket input target ttl) (IPv4.computedChecksum (ipPacket input target ttl)) ++
    (ipPacket input target ttl).payload

theorem transformed_header (input : TCP.DecodedIPv4) (target : Packet.Header) (ttl : UInt8)
    (transport : target.protocol = Packet.Protocol.tcp) : (transformed input target ttl).header = target := by
  cases target
  simp_all [transformed, TCP.DecodedIPv4.header, ipPacket]

theorem transformed_valid (input : TCP.DecodedIPv4) (target : Packet.Header) (ttl : UInt8)
    (valid : SourceValid input) (transport : target.protocol = Packet.Protocol.tcp) :
    (transformed input target ttl).Valid := by
  refine ⟨transport, ?_⟩
  exact TCP.decode_encodeBytes target.source target.destination (segment input target)
    (segment_encodable input target valid) (segment_accepts input target)

theorem transformed_encoded (input : TCP.DecodedIPv4) (target : Packet.Header) (ttl : UInt8)
    (valid : SourceValid input) (transport : target.protocol = Packet.Protocol.tcp) :
    TCP.encodeIPv4 (transformed input target ttl) = .ok (wireBytes input target ttl) := by
  rw [TCP.encodeIPv4, ite_eq_left (transformed_valid input target ttl valid transport)]
  have bounded := ipPacket_encodable input target ttl valid
  have checked := IPv4.computedChecksum_valid (ipPacket input target ttl)
  simp only [IPv4.encodeDecoded, transformed, bounded, decide_true, Bool.not_true,
    Bool.false_eq_true, ite_false, checked, bind, Except.bind, pure, List.append_nil]
  rfl

structure Certified (input : TCP.DecodedIPv4) (target : Packet.Header) (ttl : UInt8) where
  packet : TCP.DecodedIPv4
  bytes : List UInt8
  generated : packet = transformed input target ttl
  encoded : TCP.encodeIPv4 packet = .ok bytes

def rewrite (input : TCP.DecodedIPv4) (target : Packet.Header) (ttl : UInt8)
    (valid : SourceValid input) (transport : target.protocol = Packet.Protocol.tcp) : Certified input target ttl :=
  ⟨transformed input target ttl, wireBytes input target ttl, rfl, transformed_encoded input target ttl valid transport⟩

namespace Certified

variable {input : TCP.DecodedIPv4} {target : Packet.Header} {nextTTL : UInt8}

theorem decoded (result : Certified input target nextTTL) : TCP.decodeIPv4 result.bytes = .ok result.packet :=
  TCP.decodeIPv4_encodeIPv4 result.packet result.bytes result.encoded

theorem target_tcp (result : Certified input target nextTTL) : target.protocol = Packet.Protocol.tcp := by
  have protocol := (TCP.decodeIPv4_layers _ _ result.decoded).2.1
  rw [result.generated] at protocol
  exact protocol

theorem header (result : Certified input target nextTTL) (transport : target.protocol = Packet.Protocol.tcp) :
    result.packet.header = target := by
  rw [result.generated]
  exact transformed_header input target nextTTL transport

theorem payload (result : Certified input target nextTTL) : result.packet.segment.payload = input.segment.payload := by
  rw [result.generated]
  exact segment_payload _ _

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

theorem transport (result : Certified input target nextTTL) :
    result.packet.segment.sequence = input.segment.sequence ∧
      result.packet.segment.acknowledgment = input.segment.acknowledgment ∧
      result.packet.segment.reserved = input.segment.reserved ∧
      result.packet.segment.flags = input.segment.flags ∧
      result.packet.segment.window = input.segment.window ∧
      result.packet.segment.urgentPointer = input.segment.urgentPointer ∧
      result.packet.segment.options = input.segment.options := by
  rw [result.generated]
  exact segment_transport input target

theorem ipv4_checksum (result : Certified input target nextTTL) :
    InternetChecksum.valid (IPv4.headerBytes result.packet.ip.packet result.packet.ip.checksum) = true :=
  (IPv4.decode_valid _ _ (TCP.decodeIPv4_layers _ _ result.decoded).1).2

theorem tcp_checksum (result : Certified input target nextTTL) :
    InternetChecksum.valid (TCP.pseudoHeader result.packet.ip.packet.source result.packet.ip.packet.destination
      result.packet.segment.lengthWord ++ result.packet.ip.packet.payload) = true :=
  TCP.decode_checksum _ _ _ _ (TCP.decodeIPv4_layers _ _ result.decoded).2.2

theorem length (result : Certified input target nextTTL) (valid : SourceValid input) :
    result.packet.ip.packet.wireLength = input.ip.packet.wireLength := by
  rw [result.generated]
  exact ipPacket_length input target nextTTL valid

theorem bytes_length (result : Certified input target nextTTL) :
    result.bytes.length = result.packet.ip.packet.wireLength := by
  have encoded : IPv4.encodeDecoded result.packet.ip = .ok result.bytes := by
    have accepted := result.encoded
    unfold TCP.encodeIPv4 at accepted
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

def rewriteFlow (input : TCP.DecodedIPv4) (entry : FlowNAT.Entry) (direction : FlowNAT.Direction) (ttl : UInt8)
    (valid : SourceValid input) (wellFormed : entry.WellFormed) (selected : input.header = entry.input direction) :
    Certified input (entry.output direction) ttl :=
  rewrite input (entry.output direction) ttl valid
    ((entry.output_protocol wellFormed direction).trans (congrArg Packet.Header.protocol selected).symm)

theorem rewriteFlow_header (input : TCP.DecodedIPv4) (entry : FlowNAT.Entry) (direction : FlowNAT.Direction) (ttl : UInt8)
    (valid : SourceValid input) (wellFormed : entry.WellFormed) (selected : input.header = entry.input direction) :
    (rewriteFlow input entry direction ttl valid wellFormed selected).packet.header =
      (entry.rewrite direction).apply input.header := by
  let result := rewriteFlow input entry direction ttl valid wellFormed selected
  calc
    result.packet.header = entry.output direction := result.header result.target_tcp
    _ = (entry.rewrite direction).apply input.header := by
      rw [selected, entry.rewrite_correct wellFormed direction]

end Netlib.Protocol.TCPRewrite
