import Netlib.Protocol.IPv4Reassembly
import Netlib.Protocol.TCP.Rewrite

/-!
This byte adapter does a check of the TCP payload in an IPv4 reassembly output.
It adds no connection-state interpretation or ordinary conntrack transition.
-/

namespace Netlib.Protocol.TCP.Reassembly

structure Source (output : IPv4Reassembly.Output) where
  bytes : List UInt8
  packet : TCP.DecodedIPv4
  encoded : IPv4.encode output.packet = .ok bytes
  decoded : TCP.decodeIPv4 bytes = .ok packet
  same : packet.ip.packet = output.packet

def source (output : IPv4Reassembly.Output) : Except String (Source output) :=
  match encoded : IPv4.encode output.packet with
  | .error reason => .error reason
  | .ok bytes =>
    match decoded : TCP.decodeIPv4 bytes with
    | .error reason => .error reason
    | .ok packet =>
      if same : packet.ip.packet = output.packet then .ok ⟨bytes, packet, encoded, decoded, same⟩
      else .error "TCP decoding must preserve the reassembled IPv4 packet."

theorem Source.valid (value : Source output) : TCPRewrite.SourceValid value.packet :=
  TCPRewrite.sourceValid_of_decoded value.bytes value.packet value.decoded

theorem Source.payload (value : Source output) : value.packet.ip.packet.payload = output.packet.payload :=
  congrArg IPv4.Packet.payload value.same

theorem Source.transport_decoded (value : Source output) :
    TCP.decode output.packet.source output.packet.destination output.packet.payload = .ok value.packet.segment := by
  have checked := value.valid.1.2
  rw [value.same] at checked
  exact checked

theorem Source.segmentBytes (value : Source output) :
    value.packet.segment.encodeBytes = output.packet.payload :=
  (TCP.decode_fields _ _ _ _ value.transport_decoded).2.2

theorem Source.protocol (value : Source output) : output.packet.protocol = Packet.Protocol.tcp := by
  have selected := value.valid.1.1
  rw [value.same] at selected
  exact selected

theorem Source.header (value : Source output) :
    value.packet.header = ⟨output.packet.source, output.packet.destination, output.packet.protocol,
      value.packet.segment.sourcePort, value.packet.segment.destinationPort⟩ := by
  have selected := TCP.decodeIPv4_header value.bytes value.packet value.decoded
  rw [value.same] at selected
  exact selected

theorem Source.checksum (value : Source output) :
    InternetChecksum.valid (TCP.pseudoHeader output.packet.source output.packet.destination
      value.packet.segment.lengthWord ++ output.packet.payload) = true :=
  TCP.decode_checksum _ _ _ _ value.transport_decoded

theorem Source.padding (value : Source output) : value.packet.ip.padding = [] := by
  have decoded := (TCP.decodeIPv4_layers _ _ value.decoded).1
  have encoded := IPv4.decode_encode output.packet value.bytes value.encoded
  have same := Except.ok.inj (decoded.symm.trans encoded)
  exact congrArg IPv4.Decoded.padding same

theorem Source.bytes_eq (value : Source output) :
    value.bytes = IPv4.headerBytes output.packet (IPv4.computedChecksum output.packet) ++ output.packet.payload := by
  have encoded := value.encoded
  unfold IPv4.encode at encoded
  split at encoded
  · exact (Except.ok.inj encoded).symm
  · cases encoded

theorem Source.length (value : Source output) :
    value.bytes.length = output.packet.wireLength := by
  rw [value.bytes_eq, List.length_append, IPv4.headerBytes_length]
  simp [IPv4.Packet.wireLength, Nat.add_comm]

def Source.rewriteFlow (value : Source output) (entry : FlowNAT.Entry) (direction : FlowNAT.Direction) (ttl : UInt8)
    (wellFormed : entry.WellFormed) (selected : value.packet.header = entry.input direction) :
    TCPRewrite.Certified value.packet (entry.output direction) ttl :=
  TCPRewrite.rewriteFlow value.packet entry direction ttl value.valid wellFormed selected

theorem Source.rewriteFlow_header (value : Source output) (entry : FlowNAT.Entry)
    (direction : FlowNAT.Direction) (ttl : UInt8) (wellFormed : entry.WellFormed)
    (selected : value.packet.header = entry.input direction) :
    (value.rewriteFlow entry direction ttl wellFormed selected).packet.header =
      (entry.rewrite direction).apply value.packet.header :=
  TCPRewrite.rewriteFlow_header value.packet entry direction ttl value.valid wellFormed selected

end Netlib.Protocol.TCP.Reassembly
