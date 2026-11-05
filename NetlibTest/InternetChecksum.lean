import Netlib.Protocol.InternetChecksum

namespace NetlibTest.InternetChecksum

open Netlib.Protocol.InternetChecksum

example (first rest : List UInt8) (even : first.length % 2 = 0) :
    valid (first ++ wordBytes (checksum (first ++ [0, 0] ++ rest)) ++ rest) = true :=
  synthesize_valid first rest even

example (first rest : List UInt8) (even : first.length % 2 = 0) :
    valid (first ++ wordBytes (transmittedChecksum (first ++ [0, 0] ++ rest)) ++ rest) = true :=
  synthesize_nonzero_valid first rest even

example (value : Word) : read16 (highByte value) (lowByte value) = value := read16_bytes value

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  let rfc : List UInt8 := [0, 1, 242, 3, 244, 245, 246, 247]
  ensure ((sum rfc).val == 56818 && (checksum rfc).val == 8717)
    "RFC1071 section3 must sum to0xddf2 and checksum to0x220d."
  ensure ((sum (rfc.take 7)).val == 56571 && sum (rfc.take 7) == sum (rfc.take 7 ++ [0]))
    "A final odd byte must be the high byte of a zero-padded word."
  ensure ((sum []).val == 0 && (checksum []).val == 65535 && !valid [] &&
      !valid [0, 0] && valid [255, 255] && valid [255, 255, 255, 255])
    "End-around carry must retain positive and negative zero rather than treating zero as valid."
  for n in [0, 1, 255, 256, 257, 32768, 65534, 65535] do
    let value : Word := ⟨n % 65536, Nat.mod_lt _ (by decide)⟩
    ensure (read16 (highByte value) (lowByte value) == value && (wordBytes value).length == 2)
      "Network-order word encoding must retain all sixteen bits."
  for first in ([[], [0, 1], [255, 255, 255, 255], List.replicate 20 170] : List (List UInt8)) do
    for rest in [[], [1], [0, 255], [1, 2, 3], List.replicate 255 255, List.replicate 256 170] do
      let cleared := first ++ [0, 0] ++ rest
      ensure (valid (first ++ wordBytes (checksum cleared) ++ rest) &&
          valid (first ++ wordBytes (transmittedChecksum cleared) ++ rest) && transmittedChecksum cleared != 0)
        "Synthesis must work at any aligned zero field, including odd suffixes and repeated carries."
  let zero : List UInt8 := [0, 1, 255, 254]
  ensure (checksum (zero ++ [0, 0]) == 0 && transmittedChecksum (zero ++ [0, 0]) == 65535 &&
      valid (zero ++ [0, 0]) && valid (zero ++ [255, 255]))
    "UDP's zero-to-ffff transmission rule must preserve checksum validity."
  ensure (!valid ([1] ++ wordBytes (checksum [1, 0, 0, 2]) ++ [2]))
    "Checksum insertion requires an even byte offset."
  IO.println "Internet checksum tests passed."

end NetlibTest.InternetChecksum
