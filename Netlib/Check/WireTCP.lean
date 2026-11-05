import Netlib.Check.TCP
import Netlib.Import.EthernetIPv4

/-! Untagged Ethernet supplies the IPv4 addresses used by mandatory TCP checksum validation. -/

namespace Netlib.Check.WireTCP

open Protocol
namespace Model
export Netlib.Protocol.TCP (DecodedIPv4 decodeIPv4 encodeIPv4)
end Model

structure Checked (bytes : List UInt8) where
  envelope : Import.EthernetIPv4.Envelope
  packet : Model.DecodedIPv4
  ethernet : Import.EthernetIPv4.decode bytes = .ok envelope
  transport : Model.decodeIPv4 envelope.payload = .ok packet

def checkBytes (bytes : List UInt8) : Except String (Checked bytes) :=
  match ethernet : Import.EthernetIPv4.decode bytes with
  | .error reason => .error reason
  | .ok envelope =>
    match transport : Model.decodeIPv4 envelope.payload with
    | .error reason => .error reason
    | .ok packet => .ok ⟨envelope, packet, ethernet, transport⟩

def Checked.header (checked : Checked bytes) : Packet.Header := checked.packet.header

theorem Checked.header_fields (checked : Checked bytes) :
    checked.header = ⟨checked.packet.ip.packet.source, checked.packet.ip.packet.destination,
      checked.packet.ip.packet.protocol, checked.packet.segment.sourcePort, checked.packet.segment.destinationPort⟩ :=
  Protocol.TCP.decodeIPv4_header checked.envelope.payload checked.packet checked.transport

def Checked.encode (checked : Checked bytes) : Except String (List UInt8) := do
  let payload ← Model.encodeIPv4 checked.packet
  return Import.EthernetIPv4.encode { checked.envelope with payload }

theorem Checked.encode_eq (checked : Checked bytes) : checked.encode = .ok bytes := by
  simp only [Checked.encode, Protocol.TCP.encodeIPv4_decodeIPv4 _ _ checked.transport, bind, Except.bind]
  have reconstructed := Import.EthernetIPv4.encode_decode bytes checked.envelope checked.ethernet
  simpa only [pure, Except.pure] using congrArg Except.ok reconstructed

theorem Checked.tcp_checksum (checked : Checked bytes) :
    InternetChecksum.valid (Protocol.TCP.pseudoHeader checked.packet.ip.packet.source checked.packet.ip.packet.destination
      checked.packet.segment.lengthWord ++ checked.packet.ip.packet.payload) = true :=
  Protocol.TCP.decode_checksum _ _ _ _ (Protocol.TCP.decodeIPv4_layers _ _ checked.transport).2.2

structure Input where
  bytes : List UInt8

def Input.fromJson (json : Lean.Json) : Except String Input := do
  Import.PacketFields.fields json ["schema", "raw"]
  if (← (← json.getObjVal? "schema").getNat?) != 1 then throw "Use TCP wire schema 1."
  return ⟨← Import.EAPOL.bytesFromHex (← (← json.getObjVal? "raw").getStr?)⟩

def Input.parse (text : String) : Except String Input := do Input.fromJson (← Import.Json.parse text)

def Input.check (input : Input) : Except String (Checked input.bytes) := checkBytes input.bytes

def assumptions : List String := [
  "The bytes describe one untagged Ethernet IPv4 capture without FCS and with completed checksums.",
  "The selected IPv4 profile has IHL five and no fragments. Completed reassembly has a separate source interface.",
  "Ethernet padding remains outside the declared IPv4 payload and TCP segment."] ++ Check.TCP.assumptions

def Checked.renderJson (checked : Checked bytes) : Lean.Json := Lean.Json.mkObj [
  ("scope", Lean.toJson "untagged-ipv4-tcp-framing"), ("valid", Lean.toJson true), ("bytes", Lean.toJson bytes.length),
  ("header", Import.PacketFields.headerJson checked.header),
  ("sourceMAC", Lean.toJson checked.envelope.source.render), ("destinationMAC", Lean.toJson checked.envelope.destination.render),
  ("ttl", Lean.toJson checked.packet.ip.packet.ttl.toNat), ("tos", Lean.toJson checked.packet.ip.packet.tos.toNat),
  ("identification", Lean.toJson checked.packet.ip.packet.identification.val),
  ("dontFragment", Lean.toJson checked.packet.ip.packet.dontFragment),
  ("ipv4Checksum", Lean.toJson checked.packet.ip.checksum.val), ("tcpChecksumVerified", Lean.toJson true),
  ("segment", Check.TCP.segmentJson checked.packet.segment),
  ("ethernetPaddingHex", Lean.toJson (Import.EAPOL.bytesToHex checked.packet.ip.padding)),
  ("assumptions", Lean.toJson assumptions)]

def Checked.render (checked : Checked bytes) : String := "IPV4 TCP FRAME BYTES VALID\n" ++ checked.renderJson.pretty

end Netlib.Check.WireTCP
