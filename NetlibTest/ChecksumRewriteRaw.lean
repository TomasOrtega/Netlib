import Netlib.Protocol.ChecksumRewriteRaw

namespace NetlibTest.ChecksumRewriteRaw

open Netlib.Protocol Netlib.Protocol.InternetChecksum Netlib.Protocol.ChecksumRewriteRaw

example (checksum : Word) (removed added : Nat) :
    (update (update checksum removed added) added removed).val % 65535 = checksum.val % 65535 :=
  update_inverse_mod checksum removed added

example : update 0 0 0 = 65535 := by decide
example : update 0 1 2 = 65534 := by decide
example : update 0xdd2f 0x5555 0x3285 = 65535 := by decide

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  ensure (update 0 0 0 == 65535 && update 0 1 2 == 65534)
    "A raw zero checksum participates in arithmetic instead of marking omission."
  for checksum in ([0, 1, 2, 32767, 65534, 65535] : List Word) do
    for (oldTotal, newTotal) in ([(17664, 17665), (65535, 65536), (65536, 131071),
        (65535, 1), (1, 65535)] : List (Nat × Nat)) do
      let rewritten := update checksum oldTotal newTotal
      ensure (rewritten != 0 &&
          (fold (oldTotal + checksum.val)).val % 65535 == (fold (newTotal + rewritten.val)).val % 65535)
        "Incremental replacement must retain the checksum residue, including corrupted checksums."
      ensure (((fold (oldTotal + checksum.val)) == 65535) == ((fold (newTotal + rewritten.val)) == 65535))
        "Positive checksum contexts must preserve both validity and invalidity."
      ensure ((update rewritten newTotal oldTotal).val % 65535 == checksum.val % 65535)
        "Raw roundtrips must restore the residue of both zero representations."
  IO.println "Raw incremental checksum tests passed."

end NetlibTest.ChecksumRewriteRaw
