import Netlib.Protocol.IPv4Fragmentation
import Netlib.Protocol.UDP

namespace NetlibTest.IPv4Fragmentation

open Netlib Protocol
open Netlib.Protocol.IPv4Fragmentation

private def minimum : MTU := ⟨68, by decide⟩
private def medium : MTU := ⟨600, by decide⟩
private def maximum : MTU := ⟨65535, by decide⟩

private def source (payload : List UInt8) (df : Bool := false) : IPv4.Packet :=
  ⟨0x28, 0x4321, df, 63, 17, 3221225986, 3325256706, payload⟩

example (result : Certified packet mtu) : reassemble result.fragments = .ok packet := result.reassembled
example (result : Certified packet mtu) (family : List IPv4Fragment.Decoded) (permutation : family.Perm result.fragments) :
    reassemble family = .ok packet := result.reassembled_perm family permutation
example (result : Certified packet mtu) : result.fragments.flatMap (·.packet.payload) = packet.payload := result.payload

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

private def alter (parts : List IPv4Fragment.Decoded) (index : Nat)
    (change : IPv4Fragment.Packet → IPv4Fragment.Packet) : List IPv4Fragment.Decoded :=
  (parts.toArray.modify index fun part => canonical (change part.packet)).toList

private def verify (packet : IPv4.Packet) (mtu : MTU) (count : Nat) : IO Unit := do
  let result ← unwrap (check packet mtu)
  ensure (result.fragments.length == count && !result.fragments.isEmpty && result.bytes.length == count &&
      (← unwrap (reassemble result.fragments)) == packet && (← unwrap (reassemble result.fragments.reverse)) == packet)
    "Generated fragment families must fit the expected count and reassemble exactly in either arrival order."
  let mut next := 0
  for (part, index) in result.fragments.zipIdx do
    let bytes := fragmentBytes part
    let decoded ← unwrap (IPv4Fragment.decode bytes)
    ensure (decoded == part && part.packet.wireLength ≤ mtu.val && bytes.length == part.packet.wireLength &&
        part.packet.offset.val * 8 == next && part.packet.moreFragments == (index + 1 < count) &&
        metadata part == { packet with payload := [] } &&
        InternetChecksum.valid (IPv4Fragment.headerBytes part.packet part.checksum))
      "Every fragment must have the exact offset, final flag, preserved metadata, bounded length, and valid header checksum."
    if part.packet.moreFragments then
      ensure (!part.packet.payload.isEmpty && part.packet.payload.length % 8 == 0)
        "Each nonfinal chunk must contain a positive multiple of eight payload bytes."
    next := next + part.packet.payload.length
  ensure (next == packet.payload.length && result.fragments.flatMap (·.packet.payload) == packet.payload)
    "Contiguous chunks must preserve every original payload byte without loss, duplication, or overlap."

private def finalCapacityTests : IO Unit := do
  for preceding in [1, 2, 3] do
    for finalLength in [577, 578, 579, 580] do
      let packet := source (List.replicate (preceding * 576 + finalLength) 42)
      let result ← unwrap (check packet medium)
      ensure (result.fragments.map (·.packet.payload.length) == List.replicate preceding 576 ++ [finalLength])
        "The final fragment must use the full MTU payload capacity without alignment rounding."
      verify packet medium (preceding + 1)
  let oddMTU : MTU := ⟨69, by decide⟩
  let result ← unwrap (check (source (List.replicate 97 42)) oddMTU)
  ensure (result.fragments.map (·.packet.payload.length) == [48, 49])
    "An odd MTU must allow its unaligned final payload byte."

private def boundaryTests : IO Unit := do
  verify (source []) minimum 1
  verify (source (List.replicate 48 42) true) minimum 1
  verify (source (List.replicate 49 42)) minimum 2
  verify (source (List.replicate 100 42)) minimum 3
  verify (source (List.replicate 580 42) true) medium 1
  verify (source (List.replicate 581 42)) medium 2
  verify (source (List.replicate 1152 42)) medium 2
  verify (source (List.replicate 1153 42)) medium 2
  verify (source (List.replicate 1157 42)) medium 3
  verify (source (List.replicate 3000 42)) minimum 63
  verify (source (List.replicate 65515 42)) minimum 1365
  verify (source (List.replicate 65515 42) true) maximum 1
  reject (check (source (List.replicate 49 0) true) minimum)
    "An oversized DF packet must report an explicit fragmentation error."
  reject (check (source (List.replicate 65516 0)) maximum)
    "An oversized source datagram must fail before generating fragments."

private def familyTests : IO Unit := do
  let packet := source (List.replicate 1200 42)
  let result ← unwrap (check packet medium)
  let parts := result.fragments
  ensure (parts.length == 3) "The strict family regressions require three nonempty parts."
  reject (reassemble []) "An empty family cannot establish a reassembled datagram."
  reject (reassemble (parts.drop 1)) "A missing first fragment must fail the initial zero offset."
  reject (reassemble (parts.take 1 ++ parts.drop 2)) "A missing middle fragment must fail contiguous coverage."
  reject (reassemble (parts.take 2)) "A missing final fragment must fail completion."
  reject (reassemble (parts ++ parts.take 1)) "Duplicate parts must not be silently discarded."
  reject (reassemble (alter parts 1 fun part => { part with offset := part.offset - 1 }))
    "An overlapping but independently checksummed fragment must fail reassembly."
  reject (reassemble (alter parts 0 fun part => { part with offset := 1 }))
    "A gap before the first checksummed part must fail reassembly."
  reject (reassemble (alter parts 0 fun part => { part with moreFragments := false }))
    "A final fragment cannot be followed by further parts."
  reject (reassemble (alter parts 2 fun part => { part with moreFragments := true }))
    "An aligned final payload with MF set still lacks a final part."
  for change in [
      (fun part : IPv4.Packet => { part with identification := part.identification + 1 }),
      (fun part => { part with ttl := part.ttl - 1 }),
      (fun part => { part with tos := part.tos + 1 }),
      (fun part => { part with source := part.source + 1 }),
      (fun part => { part with destination := part.destination + 1 }),
      (fun part => { part with protocol := 6 })] do
    reject (reassemble (alter parts 1 fun part => { part with toPacket := change part.toPacket }))
      "The strict family must reject mismatched identification, TTL, TOS, addresses, or protocol."
  let damaged := (parts.toArray.modify 1 fun part => { part with checksum := part.checksum + 1 }).toList
  reject (reassemble damaged) "A valid offset layout cannot hide a bad fragment header checksum."

private def udpTests : IO Unit := do
  for omitted in [false, true] do
    let payload := (List.range 2001).map UInt8.ofNat
    let datagram : UDP.Datagram := if omitted then ⟨41000, 9000, 0, payload⟩
      else UDP.computed 3221225986 3325256706 41000 9000 payload
    let bytes ← unwrap (UDP.encode 3221225986 3325256706 datagram)
    let packet := source bytes
    let result ← unwrap (check packet medium)
    let recovered ← unwrap (reassemble result.fragments.reverse)
    let decoded ← unwrap (UDP.decode recovered.source recovered.destination recovered.payload)
    ensure (result.fragments.length == 4 && recovered.payload == bytes && decoded == datagram &&
        decoded.payload == payload && decide (decoded.checksum = 0 ↔ omitted = true))
      "Fragmentation must split the whole UDP segment and preserve its checksum word and payload through reassembly."

def run : IO Unit := do
  finalCapacityTests
  boundaryTests
  familyTests
  udpTests
  IO.println "MTU fragmentation and strict reassembly tests passed."

end NetlibTest.IPv4Fragmentation
