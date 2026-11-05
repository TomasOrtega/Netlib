import Netlib.Protocol.IPv4InputFragment

namespace NetlibTest.IPv4InputFragment

open Netlib.Protocol

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def base : IPv4.Packet :=
  ⟨187, 4137, false, 63, 17, 3221225986, 3405803778, []⟩

private def rejects (bytes : List UInt8) : Bool :=
  match IPv4InputFragment.decode bytes with
  | .error _ => true
  | .ok _ => false

private def failed : Except String α → Bool
  | .error _ => true
  | .ok _ => false

def run : IO Unit := do
  for df in [false, true] do
    for mf in [false, true] do
      for offset in ([0, 1, 8191] : List (Fin 8192)) do
        for size in [0, 7, 8, 11] do
          let packet : IPv4Fragment.Packet :=
            ⟨{ base with dontFragment := df, payload := (List.range size).map UInt8.ofNat }, mf, offset⟩
          let bytes ← unwrap (IPv4InputFragment.encode packet)
          let padding := [91, 92, 93]
          let decoded ← unwrap (IPv4InputFragment.decode (bytes ++ padding))
          ensure (decoded.packet == packet && decoded.padding == padding)
            "Ingress framing must preserve DF, MF, offset, empty data, and unaligned payloads."
          ensure ((← unwrap (IPv4InputFragment.encodeDecoded decoded)) == bytes ++ padding)
            "Accepted ingress fragment bytes must reconstruct exactly, including padding."
  let packet : IPv4Fragment.Packet := ⟨{ base with dontFragment := true, payload := [1, 2, 3] }, true, 1⟩
  let bytes ← unwrap (IPv4InputFragment.encode packet)
  ensure (failed (IPv4Fragment.decode bytes) && !rejects bytes)
    "Reassembly inputs need a framing codec independent of the strict generated-fragment profile."
  ensure (rejects (bytes.take 19) && rejects (bytes.take (bytes.length - 1)))
    "A truncated header or declared payload must reject."
  for position in [0, 2, 6, 10] do
    let replacement : UInt8 := if position == 0 then 70 else if position == 2 then 255 else 128
    let changed := bytes.take position ++ [replacement] ++ bytes.drop (position + 1)
    ensure (rejects changed) "Unsupported framing or a corrupt IPv4 checksum must reject."
  let huge : IPv4Fragment.Packet := ⟨{ base with payload := List.replicate 65516 0 }, false, 0⟩
  ensure (failed (IPv4InputFragment.encode huge)) "A fragment cannot exceed the IPv4 total-length field."
  IO.println "Ingress IPv4 fragment codec tests passed."

end NetlibTest.IPv4InputFragment
