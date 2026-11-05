import Netlib.Protocol.IPv4Fragment

namespace NetlibTest.IPv4Fragment

open Netlib Protocol
open Netlib.Protocol.IPv4Fragment

private def base (payload : List UInt8) (df : Bool := false) : IPv4.Packet :=
  ⟨0x28, 0x4321, df, 63, 17, 3221225986, 3325256706, payload⟩

example (packet : Packet) (bytes : List UInt8) (encoded : encode packet = .ok bytes) :
    decode bytes = .ok ⟨packet, computedChecksum packet, []⟩ := decode_encode _ _ encoded

example (value : Decoded) (bytes : List UInt8) (accepted : decode bytes = .ok value) :
    encodeDecoded value = .ok bytes := encode_decode _ _ accepted

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

private def raw (packet : Packet) : List UInt8 := headerBytes packet (computedChecksum packet) ++ packet.payload

private def codecTests : IO Unit := do
  for packet in [
      Packet.mk (base [] true) false 0,
      ⟨base [1, 2, 3] true, false, 0⟩,
      ⟨base (List.replicate 16 42), true, 0⟩,
      ⟨base (List.replicate 8 128), true, 7⟩,
      ⟨base [1, 2, 3], false, 8191⟩] do
    let bytes ← unwrap (encode packet)
    let value ← unwrap (decode (bytes ++ [0, 255, 0]))
    ensure (value.packet == packet && value.padding == [0, 255, 0] &&
        (← unwrap (encodeDecoded value)) == bytes ++ [0, 255, 0] &&
        InternetChecksum.valid (headerBytes value.packet value.checksum))
      "Fragment codecs must retain MF, offset, DF, metadata, checksum, and outside padding exactly."
    reject (decode ((bytes.toArray.modify 4 (· + 1)).toList))
      "A changed fragment identification must fail its original checksum."
    reject (decode ((bytes.toArray.set! 0 0x46).toList)) "The selected fragment codec excludes IPv4 options."
    reject (decode ((bytes.toArray.set! 3 19).toList)) "A declared fragment shorter than its header must fail."
    reject (decode (bytes.take 19)) "A fragment needs all twenty header bytes."
    if !packet.payload.isEmpty then
      reject (decode (bytes.take (bytes.length - 1))) "A truncated fragment payload must fail its declared length."
  let reserved := ({ toPacket := base (List.replicate 8 0), moreFragments := true, offset := 0 } : Packet)
  let bytes := raw reserved
  let header := ((bytes.take 20).toArray.set! 6 0x80 |>.set! 10 0 |>.set! 11 0).toList
  let checksum := InternetChecksum.checksum header
  let bad := (header.toArray.set! 10 (InternetChecksum.highByte checksum) |>.set! 11 (InternetChecksum.lowByte checksum)).toList ++ reserved.payload
  ensure (InternetChecksum.valid (bad.take 20)) "The reserved-flag regression must retain a valid header checksum."
  reject (decode bad) "The reserved flag must fail independently of checksum validity."
  for packet in [
      Packet.mk (base (List.replicate 8 0) true) true 0,
      ⟨base [1] true, false, 1⟩,
      ⟨base (List.replicate 7 0), true, 0⟩,
      ⟨base [], true, 0⟩,
      ⟨base [], false, 1⟩] do
    reject (encode packet) "Inconsistent DF, MF, alignment, and empty offset parts must fail encoding."
    reject (decode (raw packet)) "The same inconsistent fields must fail raw decoding despite a computed checksum."
  let maximum : Packet := ⟨base (List.replicate 65515 0), false, 0⟩
  ensure ((← unwrap (encode maximum)).length == 65535) "A full-length unfragmented member must remain representable."
  reject (encode { maximum with toPacket := { maximum.toPacket with payload := 0 :: maximum.payload } })
    "A fragment beyond the 16-bit total length must fail."

private def zeroTests : IO Unit := do
  let seed : Packet := ⟨{ base [1, 2, 3] with identification := 0 }, false, 0⟩
  let packet := { seed with toPacket := { seed.toPacket with identification := computedChecksum seed } }
  ensure (computedChecksum packet == 0) "The zero-representation case must have a computed zero checksum."
  for word in ([0, 65535] : List InternetChecksum.Word) do
    let value : Decoded := ⟨packet, word, [255]⟩
    let bytes ← unwrap (encodeDecoded value)
    ensure ((← unwrap (decode bytes)) == value)
      "Both valid IPv4 checksum zero words must roundtrip without changing the received representation."

def run : IO Unit := do
  codecTests
  zeroTests
  IO.println "IPv4 fragment wire codec tests passed."

end NetlibTest.IPv4Fragment
