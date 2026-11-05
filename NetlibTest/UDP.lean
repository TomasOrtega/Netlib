import Netlib.Protocol.UDP
import Netlib.Import.EAPOL
import Netlib.Import.Json

namespace NetlibTest.UDP

open Netlib Netlib.Protocol Netlib.Protocol.UDP

private def source : Packet.Address := 3221225985
private def destination : Packet.Address := 3325256706
private def sample : Datagram := computed source destination 12345 53 [1, 2, 3]
private def vector : List UInt8 := [0x30, 0x39, 0, 0x35, 0, 11, 0xdf, 0x30, 1, 2, 3]

example : pseudoHeader source destination 11 = [192, 0, 2, 1, 198, 51, 100, 2, 0, 17, 0, 11] := by rfl
example : sample.checksum = 0xdf30 := by decide
example : decode source destination vector = .ok sample := by rfl
example : (computed source destination 0 0 [0x13, 0xa3]).checksum = 65535 := by decide

example (datagram : Datagram) (bytes : List UInt8) (encoded : encode source destination datagram = .ok bytes) :
    decode source destination bytes = .ok datagram := decode_encode _ _ _ _ encoded

example (bytes : List UInt8) (datagram : Datagram) (accepted : decode source destination bytes = .ok datagram) :
    encode source destination datagram = .ok bytes := encode_decode _ _ _ _ accepted

example (bytes : List UInt8) (value : DecodedIPv4) (accepted : decodeIPv4 bytes = .ok value) :
    encodeIPv4 value = .ok bytes := encodeIPv4_decodeIPv4 _ _ accepted

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError error)

private def reject (value : Except String α) (message : String) : IO Unit :=
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def ipPacket (payload : List UInt8) : IPv4.Packet :=
  ⟨0, 7, true, 64, Packet.Protocol.udp, source, destination, payload⟩

private def codecTests : IO Unit := do
  let bytes ← unwrap (encodeComputed source destination 12345 53 [1, 2, 3])
  ensure (bytes == vector) "UDP checksum bytes must match the independent pseudoheader vector."
  for payload in [[], [1], [1, 2], [1, 2, 3], [1, 2, 3, 4], [0, 255, 128, 0, 42]] do
    let datagram := computed source destination 0 65535 payload
    let encoded ← unwrap (encode source destination datagram)
    let decoded ← unwrap (decode source destination encoded)
    ensure (decoded == datagram && decoded.payload == payload && decoded.checksum != 0 &&
        InternetChecksum.valid (pseudoHeader source destination datagram.lengthWord ++ encoded))
      "Computed UDP checksums must validate odd and even payloads, including zero source ports."
    ensure ((← unwrap (encode source destination decoded)) == encoded)
      "Every accepted datagram must reproduce its exact bytes."
  let zero := computed source destination 0 0 [0x13, 0xa3]
  ensure (zero.checksum == 65535 && checksumAccepts source destination zero)
    "A computed zero must be transmitted as ffff rather than omitted."
  let omitted : Datagram := ⟨0, 0, 0, [1, 2, 3]⟩
  let omittedBytes ← unwrap (encode source destination omitted)
  ensure ((← unwrap (decode source destination omittedBytes)) == omitted &&
      (← unwrap (decode (source + 1) destination omittedBytes)).checksum == 0 &&
      !InternetChecksum.valid (pseudoHeader source destination omitted.lengthWord ++ omittedBytes))
    "An omitted checksum is accepted explicitly and supplies no pseudoheader checksum validation."
  for position in [0, 2, 6, 8, 10] do
    let corrupted := bytes.toArray.modify position (fun byte => byte + 1)
    reject (decode source destination corrupted.toList) "Changed ports, checksum, or payload bytes must fail a present checksum."
  reject (decode (source + 1) destination bytes) "A different IPv4 source must fail the UDP pseudoheader checksum."
  reject (decode source (destination + 1) bytes) "A different IPv4 destination must fail the UDP pseudoheader checksum."
  reject (decode source destination (bytes.take 7)) "A UDP header needs all eight bytes."
  reject (decode source destination ((bytes.toArray.set! 5 7).toList)) "A declared UDP length below eight must fail."
  reject (decode source destination (bytes ++ [0])) "Unexplained bytes inside the UDP input must fail the exact length profile."
  reject (decode source destination (bytes.take 10)) "A truncated UDP payload must fail its declared length."
  let largest : Datagram := ⟨65535, 0, 0, List.replicate 65527 0⟩
  let maximum ← unwrap (encode source destination largest)
  ensure (maximum.length == 65535 && (← unwrap (decode source destination maximum)).payload.length == 65527)
    "The UDP codec must support the full 65535-byte length range independently of the enclosing IPv4 limit."
  reject (encode source destination { largest with payload := 0 :: largest.payload })
    "A UDP datagram beyond its 16-bit length field must fail."

private def compositionTests : IO Unit := do
  let udp ← unwrap (encodeComputed source destination 12345 53 [1, 2, 3])
  let bytes ← unwrap (IPv4.encode (ipPacket udp))
  let value ← unwrap (decodeIPv4 (bytes ++ [0, 255, 0]))
  ensure (value.header == (Packet.Header.mk source destination Packet.Protocol.udp 12345 53) &&
      value.datagram.payload == [1, 2, 3] && value.ip.padding == [0, 255, 0] &&
      (← unwrap (encodeIPv4 value)) == bytes ++ [0, 255, 0])
    "IPv4 composition must derive every header field from bytes and retain only external padding."
  let tail ← unwrap (IPv4.encode (ipPacket (udp ++ [0])))
  reject (decodeIPv4 tail) "The selected IPv4 payload cannot contain an unexplained UDP tail."
  let other ← unwrap (IPv4.encode { ipPacket udp with protocol := Packet.Protocol.tcp })
  reject (decodeIPv4 other) "UDP composition must reject a different IPv4 protocol."
  for packet in [{ ipPacket udp with source := source + 1 }, { ipPacket udp with destination := destination + 1 }] do
    let changed ← unwrap (IPv4.encode packet)
    reject (decodeIPv4 changed) "A recomputed IPv4 checksum cannot conceal a UDP pseudoheader address change."
  reject (encodeIPv4 { value with datagram := { value.datagram with destinationPort := 54 } })
    "An encoder must reject a supplied UDP object that disagrees with the retained IPv4 payload."
  let oversized ← unwrap (encode source destination ⟨0, 0, 0, List.replicate 65527 0⟩)
  reject (IPv4.encode (ipPacket oversized)) "The enclosing IPv4 limit is smaller than the independent UDP length limit."

private def nativeTests : IO Unit := do
  let lines := (← IO.FS.readFile "examples/wire/native/data-frames.jsonl").splitOn "\n" |>.filter (!·.isEmpty)
  ensure (lines.length == 7) "The fresh complete-checksum fixture must retain seven native UDP frames."
  for line in lines do
    let row ← unwrap (Import.Json.parse line)
    let raw ← unwrap ((← unwrap (row.getObjVal? "hex")).getStr?)
    let bytes ← unwrap (Import.EAPOL.bytesFromHex raw)
    let value ← unwrap (decodeIPv4 (bytes.drop 14))
    ensure (value.datagram.checksum != 0 &&
        InternetChecksum.valid (pseudoHeader value.ip.packet.source value.ip.packet.destination value.datagram.lengthWord ++
          value.ip.packet.payload) && (← unwrap (encodeIPv4 value)) == bytes.drop 14)
      "Actual native bytes must have a completed UDP checksum and exact accepted-byte reconstruction."
  let old := (← IO.FS.readFile "examples/admission/native/data-frames.jsonl").splitOn "\n" |>.filter (!·.isEmpty)
  for line in old do
    let row ← unwrap (Import.Json.parse line)
    let raw ← unwrap ((← unwrap (row.getObjVal? "hex")).getStr?)
    let bytes ← unwrap (Import.EAPOL.bytesFromHex raw)
    reject (decodeIPv4 (bytes.drop 14)) "Earlier checksum-offload intermediates must not be relabeled as completed valid UDP wire bytes."

def run : IO Unit := do
  codecTests
  compositionTests
  nativeTests
  IO.println "IPv4 UDP wire codec tests passed."

end NetlibTest.UDP
