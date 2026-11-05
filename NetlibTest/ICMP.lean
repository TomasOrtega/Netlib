import Netlib.Protocol.ICMP

namespace NetlibTest.ICMP

open Netlib.Protocol Netlib.Protocol.ICMP

example (message : Message) : decode (encode message) = .ok ⟨message, computedChecksum message⟩ :=
  decode_encode message

example (wire : List UInt8) (value : Decoded) (accepted : decode wire = .ok value) :
    encodeDecoded value = .ok wire := encode_decode wire value accepted

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

def run : IO Unit := do
  let timeoutWire : List UInt8 := [11, 1, 244, 254, 0, 0, 0, 0]
  let timeout ← unwrap (decode timeoutWire)
  ensure (kindPrefix timeout.message.kind == [11, 1] && (← unwrap (encodeDecoded timeout)) == timeoutWire)
    "Reassembly Time Exceeded must decode code one and preserve its exact valid bytes."
  for kind in [Kind.timeExceeded, .reassemblyTimeout, .fragmentationNeeded 0, .fragmentationNeeded 1500, .fragmentationNeeded 65535] do
    for quote in [[], [1], [1, 2], [1, 2, 3], List.replicate 28 255, List.replicate 29 0] do
      let message : Message := ⟨kind, quote⟩
      let wire := encode message
      let value ← unwrap (decode wire)
      ensure (value.message == message && wire.length == quote.length + 8 && InternetChecksum.valid wire &&
          (← unwrap (encodeDecoded value)) == wire)
        "ICMP errors must preserve kind, MTU, odd quotes, checksum, and exact bytes."
      reject (decode (wire.toArray.modify 2 (· + 1)).toList) "A corrupted ICMP checksum must fail."
      reject (decode (wire.toArray.modify 4 (· + 1)).toList) "A nonzero unused ICMP field must fail."
      reject (decode (wire.toArray.modify 1 (fun _ => 7)).toList) "An unsupported ICMP code must fail."
  let odd := encode ⟨.timeExceeded, [1, 2, 3]⟩
  reject (decode (odd.take (odd.length - 1))) "A truncated odd ICMP quote must fail its checksum."
  reject (decode (odd ++ [1])) "Unaccounted bytes participate in the ICMP checksum."
  reject (decode (odd.take 7)) "An ICMP error needs its complete eight-byte header."
  let zero := encode ⟨.timeExceeded, [244, 255]⟩
  ensure (zero == [11, 0, 0, 0, 0, 0, 0, 0, 244, 255])
    "The ICMP checksum vector must preserve a computed positive zero."
  for checksum in [0, 65535] do
    let wire := bytes ⟨.timeExceeded, [244, 255]⟩ checksum
    let decoded ← unwrap (decode wire)
    ensure (decoded.checksum == checksum && (← unwrap (encodeDecoded decoded)) == wire)
      "Both valid checksum zero representations must survive accepted-byte reconstruction."
  let large := encode ⟨.fragmentationNeeded 0, List.replicate 65535 0⟩
  ensure ((← unwrap (encodeDecoded (← unwrap (decode large)))) == large)
    "The independent ICMP codec must preserve maximum-length quoted IPv4 bytes."
  IO.println "ICMP error codec tests passed."

end NetlibTest.ICMP
