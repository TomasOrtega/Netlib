import Netlib.Protocol.TCP.IPv4
import Netlib.Import.EthernetIPv4

namespace NetlibTest.TCPIPv4

open Netlib Protocol InternetChecksum

private def source : Packet.Address := 3221225985
private def destination : Packet.Address := 3325256706

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def reject (value : Except String α) (message : String) : IO Unit := do
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def seed (payload : List UInt8) (options : List UInt8 := []) : TCP.Segment := {
  sourcePort := 12345, destinationPort := 80, sequence := TCP.Seq.ofNat 4294967295,
  acknowledgment := TCP.Seq.ofNat 2147483648, reserved := 15, flags := 255,
  window := 65535, checksum := 0, urgentPointer := 65535, options, payload }

private def packet (payload : List UInt8) : IPv4.Packet :=
  ⟨0x28, 0x4321, true, 64, Packet.Protocol.tcp, source, destination, payload⟩

private def compositionTests : IO Unit := do
  for payload in [[], [1], [1, 2], [1, 2, 3], [0, 255, 128, 42]] do
    for options in [[], [1, 2, 4, 5, 180, 254, 2, 0], List.replicate 40 1] do
      let segment := TCP.rechecksum source destination (seed payload options)
      let tcp ← unwrap (TCP.encode source destination segment)
      let bytes ← unwrap (IPv4.encode (packet tcp))
      let padded := bytes ++ [0, 255, 0]
      let decoded ← unwrap (TCP.decodeIPv4 padded)
      ensure (decoded.segment == segment && decoded.segment.payload == payload &&
          decoded.ip.padding == [0, 255, 0] && decoded.ip.packet.protocol == Packet.Protocol.tcp &&
          decoded.header == ⟨source, destination, Packet.Protocol.tcp, 12345, 80⟩ &&
          (← unwrap (TCP.encodeIPv4 decoded)) == padded)
        "IPv4 TCP composition must preserve all accepted transport fields and keep external padding separate."
      let frame : Import.EthernetIPv4.Envelope := ⟨⟨0, 1, 2, 3, 4, 5⟩, ⟨6, 7, 8, 9, 10, 11⟩, padded⟩
      let envelope ← unwrap (Import.EthernetIPv4.decode (Import.EthernetIPv4.encode frame))
      let transported ← unwrap (TCP.decodeIPv4 envelope.payload)
      ensure (transported == decoded && Import.EthernetIPv4.encode envelope == Import.EthernetIPv4.encode frame)
        "Ethernet framing must retain the IPv4 bytes and padding without extending TCP payload."

private def rejectionTests : IO Unit := do
  let segment := TCP.rechecksum source destination (seed [1, 2, 3])
  let tcp ← unwrap (TCP.encode source destination segment)
  let bytes ← unwrap (IPv4.encode (packet tcp))
  let decoded ← unwrap (TCP.decodeIPv4 bytes)
  reject (TCP.decodeIPv4 (← unwrap (IPv4.encode { packet tcp with protocol := Packet.Protocol.udp })))
    "TCP composition must reject another IPv4 protocol."
  for changed in [{ packet tcp with source := source + 1 }, { packet tcp with destination := destination + 1 }] do
    reject (TCP.decodeIPv4 (← unwrap (IPv4.encode changed)))
      "A repaired IPv4 checksum cannot conceal a TCP pseudoheader address change."
  reject (TCP.decodeIPv4 ((bytes.toArray.modify 10 (· + 1)).toList))
    "An invalid IPv4 checksum must reject before transport acceptance."
  reject (TCP.decodeIPv4 (bytes.take (bytes.length - 1)))
    "A truncated IPv4 declared payload must reject."
  let short ← unwrap (IPv4.encode (packet (tcp.take 19)))
  reject (TCP.decodeIPv4 short)
    "A complete IPv4 envelope cannot supply a truncated TCP fixed header."
  reject (TCP.encodeIPv4 { decoded with segment := { decoded.segment with window := 1 } })
    "A supplied TCP object must agree with the retained IPv4 payload."
  reject (TCP.encodeIPv4 { decoded with ip := { decoded.ip with packet := { decoded.ip.packet with protocol := Packet.Protocol.udp } } })
    "Decoded coherence requires the TCP protocol number."
  reject (TCP.encodeIPv4 { decoded with ip := { decoded.ip with checksum := decoded.ip.checksum + 1 } })
    "A coherent transport object cannot hide an invalid retained IPv4 checksum."

private def zeroAndBoundsTests : IO Unit := do
  let zeroBytes ← unwrap (Import.EAPOL.bytesFromHex "30390050000000000000000050101000000000008312")
  let bytes ← unwrap (IPv4.encode (packet zeroBytes))
  let decoded ← unwrap (TCP.decodeIPv4 bytes)
  ensure (decoded.segment.checksum == 0 && decoded.segment.payload == [0x83, 0x12] &&
      (← unwrap (TCP.encodeIPv4 decoded)) == bytes)
    "The independent valid checksum-zero segment must remain ordinarily verified through IPv4 composition."
  let alternateTCP := zeroBytes.take 16 ++ [255, 255] ++ zeroBytes.drop 18
  let alternateBytes ← unwrap (IPv4.encode (packet alternateTCP))
  let alternate ← unwrap (TCP.decodeIPv4 alternateBytes)
  ensure (alternate.segment.checksum == 65535 &&
      (← unwrap (TCP.encodeIPv4 alternate)) == alternateBytes &&
      (TCP.rechecksum source destination alternate.segment).checksum == 0)
    "The alternate valid checksum word ffff must re-encode exactly while recomputation returns canonical zero."
  let maximumSegment := TCP.rechecksum source destination (seed (List.replicate 65495 0))
  let maximumTCP ← unwrap (TCP.encode source destination maximumSegment)
  let maximum ← unwrap (IPv4.encode (packet maximumTCP))
  ensure (maximum.length == 65535 && (← unwrap (TCP.decodeIPv4 maximum)).segment.payload.length == 65495)
    "The selected twenty-byte IPv4 header leaves at most 65515 complete TCP bytes."
  let oversized := TCP.rechecksum source destination { maximumSegment with payload := 0 :: maximumSegment.payload }
  let oversizedTCP ← unwrap (TCP.encode source destination oversized)
  reject (IPv4.encode (packet oversizedTCP))
    "Standalone TCP encodability does not bypass the enclosing IPv4 total-length bound."

example (bytes : List UInt8) (value : TCP.DecodedIPv4) (accepted : TCP.decodeIPv4 bytes = .ok value) :
    TCP.encodeIPv4 value = .ok bytes := TCP.encodeIPv4_decodeIPv4 _ _ accepted

example (value : TCP.DecodedIPv4) (bytes : List UInt8) (encoded : TCP.encodeIPv4 value = .ok bytes) :
    TCP.decodeIPv4 bytes = .ok value := TCP.decodeIPv4_encodeIPv4 _ _ encoded

def run : IO Unit := do
  compositionTests
  rejectionTests
  zeroAndBoundsTests
  IO.println "Static IPv4 TCP composition tests passed."

end NetlibTest.TCPIPv4
