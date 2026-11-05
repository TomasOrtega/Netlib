import Netlib.Import.EthernetIPv4
import Netlib.Import.PacketFields
import Netlib.Protocol.UDP
import Netlib.Standards.Basic

/-!
# IPv4 UDP capture checks

Packet fields come from decoded bytes. A zero UDP checksum remains explicitly omitted.
The selected profile excludes options, fragments, and extra data inside the IP payload.
-/

namespace Netlib.Check.Wire

open Protocol

structure Checked (bytes : List UInt8) where
  envelope : Import.EthernetIPv4.Envelope
  packet : UDP.DecodedIPv4
  ethernet : Import.EthernetIPv4.decode bytes = .ok envelope
  transport : UDP.decodeIPv4 envelope.payload = .ok packet

def checkBytes (bytes : List UInt8) : Except String (Checked bytes) :=
  match ethernet : Import.EthernetIPv4.decode bytes with
  | .error error => .error error
  | .ok envelope =>
    match transport : UDP.decodeIPv4 envelope.payload with
    | .error error => .error error
    | .ok packet => .ok ⟨envelope, packet, ethernet, transport⟩

def Checked.header (checked : Checked bytes) : Packet.Header := checked.packet.header

theorem Checked.header_fields (checked : Checked bytes) :
    checked.header = ⟨checked.packet.ip.packet.source, checked.packet.ip.packet.destination,
      checked.packet.ip.packet.protocol, checked.packet.datagram.sourcePort, checked.packet.datagram.destinationPort⟩ :=
  UDP.decodeIPv4_header checked.envelope.payload checked.packet checked.transport

def Checked.encode (checked : Checked bytes) : Except String (List UInt8) := do
  let payload ← UDP.encodeIPv4 checked.packet
  return Import.EthernetIPv4.encode { checked.envelope with payload }

theorem Checked.encode_eq (checked : Checked bytes) : checked.encode = .ok bytes := by
  simp only [encode, UDP.encodeIPv4_decodeIPv4 _ _ checked.transport, bind, Except.bind]
  have reconstructed := Import.EthernetIPv4.encode_decode bytes checked.envelope checked.ethernet
  simpa only [pure, Except.pure] using congrArg Except.ok reconstructed

theorem Checked.udp_checksum_verified (checked : Checked bytes) (present : checked.packet.datagram.checksum ≠ 0) :
    InternetChecksum.valid (UDP.pseudoHeader checked.packet.ip.packet.source checked.packet.ip.packet.destination
      checked.packet.datagram.lengthWord ++ checked.packet.ip.packet.payload) = true :=
  UDP.decode_verified _ _ _ _ (UDP.decodeIPv4_layers _ _ checked.transport).2.2 present

structure Input where
  bytes : List UInt8

def Input.fromJson (json : Lean.Json) : Except String Input := do
  Import.PacketFields.fields json ["schema", "raw"]
  if (← (← json.getObjVal? "schema").getNat?) != 1 then throw "Use wire schema 1."
  return ⟨← Import.EAPOL.bytesFromHex (← (← json.getObjVal? "raw").getStr?)⟩

def Input.parse (text : String) : Except String Input := do
  Input.fromJson (← Import.Json.parse text)

def Input.check (input : Input) : Except String (Checked input.bytes) := checkBytes input.bytes

def sources : List Standards.Source := [
  ⟨"Internet Protocol", "RFC 791", "3.1", "https://www.rfc-editor.org/rfc/rfc791.html"⟩,
  ⟨"User Datagram Protocol", "RFC 768", "Format and Fields", "https://www.rfc-editor.org/rfc/rfc768.html"⟩,
  ⟨"Computing the Internet Checksum", "RFC 1071", "1", "https://www.rfc-editor.org/rfc/rfc1071.html"⟩]

def assumptions : List String := [
  "Bytes describe an untagged Ethernet capture without FCS at the declared network stage.",
  "Checksum-offload intermediates are outside this byte-only profile; capture complete checksum bytes.",
  "The selected profile has IPv4 IHL 5, no fragmentation, and UDP length equal to the entire IP payload.",
  "A zero UDP checksum is permitted as omitted and supplies no UDP checksum validation.",
  "Checksums detect the modeled arithmetic condition; they do not establish identity, freshness, or cryptographic integrity.",
  "Decoded headers do not establish routing, firewall permission, eventual delivery, or complete implementation refinement."]

def Checked.renderJson (checked : Checked bytes) : Lean.Json := Lean.Json.mkObj [
  ("scope", Lean.toJson "untagged-ipv4-udp-wire-profile-1"),
  ("valid", Lean.toJson true), ("bytes", Lean.toJson bytes.length),
  ("header", Import.PacketFields.headerJson checked.header),
  ("destinationMAC", Lean.toJson checked.envelope.destination.render),
  ("sourceMAC", Lean.toJson checked.envelope.source.render),
  ("ttl", Lean.toJson checked.packet.ip.packet.ttl.toNat),
  ("tos", Lean.toJson checked.packet.ip.packet.tos.toNat),
  ("identification", Lean.toJson checked.packet.ip.packet.identification.val),
  ("dontFragment", Lean.toJson checked.packet.ip.packet.dontFragment),
  ("ipv4Checksum", Lean.toJson checked.packet.ip.checksum.val),
  ("udpChecksum", Lean.toJson checked.packet.datagram.checksum.val),
  ("udpChecksumVerified", Lean.toJson (checked.packet.datagram.checksum != 0)),
  ("payloadHex", Lean.toJson (Import.EAPOL.bytesToHex checked.packet.datagram.payload)),
  ("ethernetPaddingHex", Lean.toJson (Import.EAPOL.bytesToHex checked.packet.ip.padding)),
  ("sources", Lean.toJson (sources.map fun source => Lean.Json.mkObj [
    ("document", Lean.toJson source.document), ("version", Lean.toJson source.version),
    ("clause", Lean.toJson source.clause), ("url", Lean.toJson source.url)])),
  ("assumptions", Lean.toJson assumptions)]

def Checked.render (checked : Checked bytes) : String :=
  "IPV4 UDP BYTES VALID FOR SELECTED PROFILE\n" ++ checked.renderJson.pretty

end Netlib.Check.Wire
