import Netlib.Protocol.TCP.Segment

namespace NetlibTest.TCPSegment

open Netlib Protocol InternetChecksum

private def ensure (value : Bool) (message : String) : IO Unit := do
  unless value do throw (IO.userError message)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def reject (value : Except String α) (message : String) : IO Unit := do
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def source : Packet.Address := 3221225986
private def destination : Packet.Address := 3405803778

private def sample : TCP.Segment := {
  sourcePort := 41000, destinationPort := 8080, sequence := TCP.Seq.ofNat 4294967295,
  acknowledgment := TCP.Seq.ofNat 2147483648, reserved := 15, flags := 255,
  window := 65535, checksum := 0, urgentPointer := 65535,
  options := [1, 2, 4, 5, 180, 0, 0, 0], payload := [0, 17, 255] }

private def roundtrip (segment : TCP.Segment) : IO Unit := do
  let checked := TCP.rechecksum source destination segment
  let bytes ← load (TCP.encode source destination checked)
  let decoded ← load (TCP.decode source destination bytes)
  let encoded ← load (TCP.encode source destination decoded)
  ensure (decoded == checked && encoded == bytes && bytes.length == segment.wireLength)
    "Accepted TCP fields, raw options, reserved bits, checksum, and payload must round-trip exactly."
  ensure (InternetChecksum.valid (TCP.pseudoHeader source destination checked.lengthWord ++ bytes))
    "Every encoded TCP segment must verify its complete mandatory pseudoheader checksum."
  ensure (decoded.options == segment.options && decoded.reserved == segment.reserved &&
    decoded.sequence == segment.sequence && decoded.acknowledgment == segment.acknowledgment &&
    decoded.flags == segment.flags && decoded.urgentPointer == segment.urgentPointer)
    "Opaque sequence values and received metadata cannot be normalized during framing."

private def replaceByte (bytes : List UInt8) (index : Nat) (value : UInt8) : List UInt8 :=
  bytes.take index ++ value :: bytes.drop (index + 1)

private def repaired (bytes : List UInt8) : List UInt8 :=
  let blank := bytes.take 16 ++ [0, 0] ++ bytes.drop 18
  let length : Word := ⟨bytes.length % 65536, Nat.mod_lt _ (by decide)⟩
  let checksum := InternetChecksum.checksum (TCP.pseudoHeader source destination length ++ blank)
  bytes.take 16 ++ wordBytes checksum ++ bytes.drop 18

def run : IO Unit := do
  roundtrip sample
  roundtrip { sample with options := [], payload := [] }
  roundtrip { sample with options := List.replicate 40 1, payload := [1] }
  roundtrip { sample with options := [253, 4, 170, 187], payload := [1, 2] }
  let generated := TCP.computed source destination sample
  ensure (generated.reserved == 0 && generated.sequence == sample.sequence && generated.options == sample.options)
    "Fresh generation zeroes reserved bits while retaining supplied segment contents."
  let zero : TCP.Segment := ⟨0, 0, TCP.Seq.ofNat 0, TCP.Seq.ofNat 0, 0, 0, 0, 0, 0, [], [175, 227]⟩
  ensure ((TCP.rechecksum 0 0 zero).checksum == 0 && TCP.checksumAccepts 0 0 zero)
    "A valid TCP checksum word zero must remain an ordinary verified zero."
  let zeroBytes ← load (TCP.encode 0 0 zero)
  let decodedZero ← load (TCP.decode 0 0 zeroBytes)
  ensure (decodedZero == zero && decodedZero.checksum == 0) "Zero checksum is valid only through mandatory verification."
  reject (TCP.decode 0 0 { zero with payload := [] }.encodeBytes) "Checksum zero cannot request TCP checksum omission."
  let bytes ← load (TCP.encode source destination generated)
  reject (TCP.decode 0 destination bytes) "A wrong pseudoheader source must fail verification."
  reject (TCP.decode source 0 bytes) "A wrong pseudoheader destination must fail verification."
  reject (TCP.decode source destination (replaceByte bytes (bytes.length - 1) 0)) "Payload corruption must fail verification."
  for size in List.range 20 do
    reject (TCP.decode source destination (bytes.take size)) "Every truncated fixed header must reject."
  for offset in List.range 5 do
    reject (TCP.decode source destination (repaired (replaceByte bytes 12 (UInt8.ofNat (offset * 16)))))
      "Data offset below five must reject even with a repaired checksum."
  reject (TCP.decode source destination (repaired (replaceByte (bytes.take 20) 12 240)))
    "A data offset beyond the available option region must reject despite a valid checksum."
  for options in [[1], [0, 0, 0], List.replicate 44 1, [0, 1, 0, 0], [2, 3, 0, 0]] do
    reject (TCP.encode source destination (TCP.rechecksum source destination { sample with options }))
      "Header alignment, maximum size, EOL padding, and malformed MSS framing must be enforced."
  let maximum : TCP.Segment := { sample with options := [], payload := List.replicate 65515 0 }
  let oversized : TCP.Segment := { maximum with payload := 0 :: maximum.payload }
  ensure (decide maximum.Encodable && !decide oversized.Encodable)
    "The standalone TCP pseudoheader length must stay within sixteen bits."
  reject (TCP.encode source destination oversized) "A 65536-byte TCP segment cannot wrap its pseudoheader length."

end NetlibTest.TCPSegment
