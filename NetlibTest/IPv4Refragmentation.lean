import Netlib.Protocol.IPv4Refragmentation

namespace NetlibTest.IPv4Refragmentation

open Netlib Protocol
open Netlib.Protocol.IPv4Refragmentation

private def tiny : Budget := ⟨28, by decide⟩
private def ingress : Budget := ⟨596, by decide⟩
private def route : Budget := ⟨1500, by decide⟩

private def source (payload : List UInt8) : IPv4.Packet :=
  ⟨0x2b, 0x4321, false, 63, 17, 3221225986, 3325256706, payload⟩

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

private def canonical (packet : IPv4Fragment.Packet) : IPv4Fragment.Decoded :=
  ⟨packet, IPv4Fragment.computedChecksum packet, []⟩

private instance : Inhabited IPv4Fragment.Decoded := ⟨canonical ⟨source [], false, 0⟩⟩

private def part (packet : IPv4.Packet) (df : Bool) (start count : Nat) (more : Bool) : IPv4Fragment.Decoded :=
  IPv4Fragmentation.fragmentDecoded (outputPacket packet df) ⟨start, packet.payload.drop start |>.take count, more⟩

example (result : CertifiedFamily packet budget df) :
    IPv4Fragmentation.Layout 0 packet.payload
      ((IPv4Fragmentation.sort result.fragments).map IPv4Fragmentation.asPiece) := result.layout

example (result : CertifiedFamily packet budget df) (part : IPv4Fragment.Decoded)
    (member : part ∈ result.fragments) : part.packet.wireLength ≤ budget.val := result.fits part member

example (result : CertifiedGenerated packet budget df) :
    result.fragments.flatMap (·.packet.payload) = packet.payload := result.payload

example (result : CertifiedGenerated packet budget df) :
    reassemble result.fragments = .ok (outputPacket packet df) := result.reassembled

private def generationTests : IO Unit := do
  let packet := source (List.range 25 |>.map UInt8.ofNat)
  for df in [false, true] do
    let result ← unwrap (checkGenerated packet tiny df)
    ensure (result.fragments.map (·.packet.payload.length) == [8, 8, 8, 1] &&
        result.fragments.map (·.packet.offset.val) == [0, 1, 2, 3] &&
        result.fragments.map (·.packet.moreFragments) == [true, true, true, false])
      "A 28-byte budget must support eight-byte nonfinal payloads."
    ensure ((← unwrap (reassemble result.fragments.reverse)) == outputPacket packet df)
      "Reassembly must accept the selected output DF behavior and arbitrary arrival order."
    for fragment in result.fragments do
      let bytes ← unwrap (IPv4InputFragment.encodeDecoded fragment)
      ensure ((← unwrap (IPv4InputFragment.decode bytes)) == fragment &&
          fragment.packet.wireLength ≤ tiny.val && fragment.packet.dontFragment == df)
        "Generated DF fragments must round-trip through the permissive input codec."
    if df then
      reject (IPv4Fragment.encodeDecoded result.fragments.head!)
        "The strict output codec must remain distinct from DF re-fragmentation."
    discard <| unwrap (check packet tiny df result.fragments)
  let large := source (List.replicate 1208 42)
  let capped ← unwrap (checkGenerated large (route.cap ingress) false)
  ensure ((route.cap ingress).val == 596 && capped.fragments.map (·.packet.payload.length) == [576, 576, 56])
    "A larger route MTU must retain the accepted ingress fragment size cap."
  let empty ← unwrap (checkGenerated (source []) tiny false)
  ensure (empty.fragments.length == 1 && empty.fragments.head!.packet.wireLength == 20)
    "An empty complete payload must retain its one-packet representation."
  reject (checkGenerated (source (List.replicate 65516 0)) route false)
    "An oversized reconstructed IPv4 packet must fail before fragment generation."

private def observedTests : IO Unit := do
  let packet := source (List.range 25 |>.map UInt8.ofNat)
  let budget : Budget := ⟨36, by decide⟩
  let observed := [part packet false 0 8 true, part packet false 8 8 true, part packet false 16 9 false]
  let generated ← unwrap (checkGenerated packet budget false)
  ensure (generated.fragments.map (·.packet.payload.length) == [16, 9])
    "The copying generator must use its computed capacity."
  let checked ← unwrap (check packet budget false observed.reverse)
  ensure (checked.fragments == observed.reverse && (← unwrap (reassemble checked.fragments)) == packet)
    "An observed legal family must preserve its actual boundaries and arrival order."
  let padded := observed.map (fun fragment => { fragment with padding := [0xaa, 0xbb] })
  let paddedResult ← unwrap (check packet budget false padded)
  ensure (paddedResult.fragments == padded)
    "Trailing capture padding must remain separate from reconstructed payload."
  let dfObserved := [part packet true 0 8 true, part packet true 8 8 true, part packet true 16 9 false]
  discard <| unwrap (check packet budget true dfObserved)
  reject (check packet budget false dfObserved)
    "The observed family must use the caller's selected DF behavior."
  reject (check packet budget false []) "An empty observed family must fail."
  reject (check packet tiny false observed) "Every observed packet must fit the selected budget."
  reject (check (source (List.replicate 25 0)) budget false observed)
    "Observed payload must equal the expected complete packet exactly."
  reject (check packet budget false (observed ++ [observed.head!]))
    "Duplicate observed fragments must fail family certification."
  reject (check packet budget false [part packet false 0 8 true, part packet false 16 9 false])
    "A gap must prevent family certification."
  reject (check packet budget false [part packet false 0 16 true, part packet false 8 17 false])
    "Overlapping observed ranges must fail family certification."
  reject (check packet budget false [part packet false 0 8 false, part packet false 8 17 false])
    "A final fragment cannot precede more payload."
  reject (check packet budget false [part packet false 0 8 true, part packet false 8 16 true])
    "A family without a final fragment must fail."
  reject (check packet budget false [part packet false 0 9 true, part packet false 8 17 false])
    "Nonfinal payload lengths must be aligned."
  reject (check packet budget false [part packet false 0 0 true, part packet false 0 25 false])
    "Empty nonfinal fragments must fail even when the remaining payload is complete."
  let badChecksum := { observed.head! with checksum := 0 } :: observed.tail!
  reject (check packet budget false badChecksum) "Observed IP header checksums must be valid."
  let wrongTTL := canonical { observed.head!.packet with ttl := 62 } :: observed.tail!
  reject (check packet budget false wrongTTL) "Checksummed TTL changes must fail uniform metadata validation."
  let mixedDF := observed.head! :: dfObserved.tail!
  reject (check packet budget false mixedDF) "Mixed output DF flags must fail metadata validation."

def run : IO Unit := do
  generationTests
  observedTests
  IO.println "IPv4 re-fragmentation contract tests passed."

end NetlibTest.IPv4Refragmentation
