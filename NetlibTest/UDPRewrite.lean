import Netlib.Protocol.UDPRewrite
import Netlib.Packet.Rewrite

namespace NetlibTest.UDPRewrite

open Netlib Packet Protocol

private def original : Header := ⟨3221225986, 3405803778, Packet.Protocol.udp, 41000, 8080⟩
private def translated : Header := ⟨3405803777, 3325256706, Packet.Protocol.udp, 40000, 9000⟩

example (result : Protocol.UDPRewrite.Certified input target ttl) :
    UDP.decodeIPv4 result.bytes = .ok result.packet := result.decoded

example (result : Protocol.UDPRewrite.Certified input target ttl) :
    result.packet.datagram.payload = input.datagram.payload ∧
      result.packet.ip.packet.ttl = ttl ∧
      (result.packet.datagram.checksum = 0 ↔ input.datagram.checksum = 0) :=
  ⟨result.payload, result.ttl, result.checksum_omitted_iff⟩

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError error)

private structure Prepared where
  bytes : List UInt8
  packet : UDP.DecodedIPv4
  decoded : UDP.decodeIPv4 bytes = .ok packet

private theorem Prepared.valid (value : Prepared) : Protocol.UDPRewrite.SourceValid value.packet :=
  Protocol.UDPRewrite.sourceValid_of_decoded value.bytes value.packet value.decoded

private def read (bytes : List UInt8) : IO Prepared :=
  match decoded : UDP.decodeIPv4 bytes with
  | .error error => throw (IO.userError error)
  | .ok packet => pure ⟨bytes, packet, decoded⟩

private def make (header : Header) (payload : List UInt8) (omitted : Bool := false)
    (ttl : UInt8 := 64) (identification : InternetChecksum.Word := 0x4321) : IO Prepared := do
  let datagram : UDP.Datagram := if omitted then ⟨header.sourcePort, header.destinationPort, 0, payload⟩
    else UDP.computed header.source header.destination header.sourcePort header.destinationPort payload
  let udp ← unwrap (UDP.encode header.source header.destination datagram)
  let ip : IPv4.Packet := ⟨0x28, identification, true, ttl, header.protocol, header.source, header.destination, udp⟩
  read (← unwrap (IPv4.encode ip))

private def inspect (input : Prepared) (target : Header) (ttl : UInt8)
    (transport : target.protocol = Packet.Protocol.udp) : IO Unit := do
  let result := Protocol.UDPRewrite.rewrite input.packet target ttl input.valid transport
  let decoded ← unwrap (UDP.decodeIPv4 result.bytes)
  ensure (decoded == result.packet && decoded.header == target &&
      decoded.datagram.payload == input.packet.datagram.payload && decoded.ip.packet.ttl == ttl &&
      decoded.ip.packet.tos == input.packet.ip.packet.tos &&
      decoded.ip.packet.identification == input.packet.ip.packet.identification &&
      decoded.ip.packet.dontFragment == input.packet.ip.packet.dontFragment && decoded.ip.padding.isEmpty &&
      decoded.ip.packet.wireLength == input.packet.ip.packet.wireLength && result.bytes.length == decoded.ip.packet.wireLength)
    "Rewriting must preserve the exact payload, metadata, and length while changing only the selected tuple, TTL, and checksums."
  ensure (InternetChecksum.valid (IPv4.headerBytes decoded.ip.packet decoded.ip.checksum) &&
      decide (decoded.datagram.checksum = 0 ↔ input.packet.datagram.checksum = 0))
    "Canonical output must have a valid IPv4 checksum and preserve UDP checksum omission exactly."
  if decoded.datagram.checksum != 0 then
    ensure (InternetChecksum.valid (UDP.pseudoHeader target.source target.destination decoded.datagram.lengthWord ++ decoded.ip.packet.payload))
      "A present UDP checksum must cover both translated addresses, ports, length, and payload."

private def translationTests : IO Unit := do
  for payload in [[], [1], [1, 2], [1, 2, 3], [1, 2, 3, 4], [255, 0, 0, 128, 42]] do
    for omitted in [false, true] do
      let input ← make original payload omitted
      inspect input original 64 rfl
      let unchanged := Protocol.UDPRewrite.rewrite input.packet original 64 input.valid rfl
      ensure (unchanged.bytes == input.bytes) "An unchanged canonical packet must retain its exact bytes."
      inspect input translated 63 rfl
      inspect input translated 0 rfl
      let rewritten := Protocol.UDPRewrite.rewrite input.packet translated 63 input.valid rfl
      ensure (rewritten.packet.ip.checksum != input.packet.ip.checksum)
        "The translated tuple and changed TTL must affect this example's IPv4 checksum."
      let ttlOnly := Protocol.UDPRewrite.rewrite input.packet original 63 input.valid rfl
      ensure (ttlOnly.packet.datagram.checksum == input.packet.datagram.checksum &&
          ttlOnly.packet.ip.checksum != input.packet.ip.checksum)
        "A TTL-only change must update the IPv4 checksum without changing a UDP checksum."
      let reply ← make translated.reverse (payload ++ [42]) omitted
      inspect reply original.reverse 63 rfl
      let restored := Protocol.UDPRewrite.rewrite reply.packet original.reverse 63 reply.valid rfl
      ensure (restored.packet.header == original.reverse && restored.packet.datagram.payload == payload ++ [42])
        "Return translation must restore the original reverse tuple while retaining the reply's own payload."

private def zeroAndBoundsTests : IO Unit := do
  let input ← make original [0x13, 0xa3]
  let zeroTarget : Header := ⟨3221225985, 3325256706, Packet.Protocol.udp, 0, 0⟩
  let mapped := Protocol.UDPRewrite.rewrite input.packet zeroTarget 63 input.valid rfl
  ensure (mapped.packet.datagram.checksum == 65535)
    "A translated tuple whose computed UDP checksum is zero must transmit ffff."
  let seed ← make original [1, 2, 3] false 64 0
  let identification := IPv4.computedChecksum seed.packet.ip.packet
  let zeroIP ← make original [1, 2, 3] false 64 identification
  ensure (zeroIP.packet.ip.checksum == 0) "The dual-zero IPv4 test must start with a computed zero checksum."
  let alternate := { zeroIP.packet with ip := { zeroIP.packet.ip with checksum := 65535 } }
  let alternate ← read (← unwrap (UDP.encodeIPv4 alternate))
  let canonical := Protocol.UDPRewrite.rewrite alternate.packet original 64 alternate.valid rfl
  ensure (alternate.packet.ip.checksum == 65535 && canonical.packet.ip.checksum == 0 &&
      canonical.packet.datagram.payload == alternate.packet.datagram.payload)
    "Both valid IPv4 zero words must decode while rewrite emits the canonical computed word."
  let largest ← make original (List.replicate 65507 0) true
  let maximum := Protocol.UDPRewrite.rewrite largest.packet translated 63 largest.valid rfl
  ensure (maximum.bytes.length == 65535 && maximum.packet.datagram.payload.length == 65507 &&
      maximum.packet.datagram.checksum == 0 && (← unwrap (UDP.decodeIPv4 maximum.bytes)).header == translated)
    "A maximal valid IPv4 UDP payload must remain encodable after translation without losing omission or bytes."
  let padded ← read (input.bytes ++ [0, 255, 0])
  let stripped := Protocol.UDPRewrite.rewrite padded.packet translated 63 padded.valid rfl
  ensure (padded.packet.ip.padding == [0, 255, 0] && stripped.packet.ip.padding.isEmpty &&
      stripped.packet.datagram.payload == input.packet.datagram.payload)
    "Link padding must not become UDP payload or be emitted as part of the canonical IPv4 datagram."

def run : IO Unit := do
  translationTests
  zeroAndBoundsTests
  IO.println "Payload-preserving UDP rewrite tests passed."

end NetlibTest.UDPRewrite
