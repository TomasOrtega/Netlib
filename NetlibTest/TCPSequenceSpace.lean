import Netlib.Protocol.TCP.SequenceSpace

namespace NetlibTest.TCPSequenceSpace

open Netlib.Protocol.TCP

example (first second : Seq) (offset : Nat) :
    Seq.distance (first.add offset) (second.add offset) = Seq.distance first second :=
  Seq.distance_translate first second offset

example (first middle last : Seq) (firstStep : Seq.Before first middle) (secondStep : Seq.Before middle last)
    (span : Seq.distance first middle + Seq.distance middle last < Seq.halfSpace) : Seq.Before first last :=
  Seq.before_trans_of_sum_lt_halfSpace first middle last firstStep secondStep span

example (origin first second : Seq) (length : Nat) (short : length < Seq.halfSpace)
    (firstInside : Seq.InInterval origin length first) (secondInside : Seq.InInterval origin length second) :
    Seq.Before first second ↔ Seq.distance origin first < Seq.distance origin second :=
  Seq.common_arc_before origin first second length short firstInside secondInside

example : True := by
  fail_if_success have _ : Ord Seq := inferInstance
  fail_if_success have _ : LT Seq := inferInstance
  trivial

private def ensure (value : Bool) (message : String) : IO Unit := do
  unless value do throw (IO.userError message)

private def unsignedDistance (first second : Nat) : Nat :=
  if first ≤ second then second - first else 4294967296 - first + second

private def referenceBefore (first second : Nat) : Bool :=
  if first < second then decide (second - first < 2147483648)
  else decide (2147483648 < first - second)

private def referenceAdd (first offset : Nat) : Nat :=
  let total := first + offset % 4294967296
  if total < 4294967296 then total else total - 4294967296

private def boundaries : List Nat := [0, 1, 2, 15, 16, 17, 2147483646, 2147483647,
  2147483648, 2147483649, 2147483650, 4294967279, 4294967280, 4294967294, 4294967295]

private def fixtureTests : IO Unit := do
  let fixtures : List (Nat × Nat × Nat × Bool) := [
    (0, 0, 0, false), (0, 1, 1, true), (1, 0, 4294967295, false),
    (4294967295, 0, 1, true), (0, 4294967295, 4294967295, false),
    (4294967294, 2, 4, true), (4294967294, 3, 5, true), (3, 4294967294, 4294967291, false),
    (0, 2147483647, 2147483647, true), (0, 2147483648, 2147483648, false),
    (2147483648, 0, 2147483648, false), (0, 2147483649, 2147483649, false),
    (2147483649, 0, 2147483647, true), (4294967295, 2147483647, 2147483648, false),
    (4294967280, 15, 31, true), (17, 4294967280, 4294967263, false)]
  for (first, second, delta, ordered) in fixtures do
    ensure (Seq.distance (Seq.ofNat first) (Seq.ofNat second) == delta &&
      Seq.before (Seq.ofNat first) (Seq.ofNat second) == ordered)
      "Independent boundary vectors must preserve wrap, equality, and open half-space comparison."
  ensure ((Seq.ofNat 4294967313).val == 17 && (Seq.ofNat 12884901907).val == 19)
    "Wire sequence construction must reduce arbitrary natural inputs to 32 bits."

private def arithmeticTests : IO Unit := do
  let offsets := [0, 1, 2, 17, 2147483647, 2147483648, 2147483649, 4294967295,
    4294967296, 4294967297, 12884901907]
  let lengths := [0, 1, 2, 16, 2147483647, 2147483648, 2147483649, 4294967295,
    4294967296, 4294967297]
  for first in boundaries do
    let a := Seq.ofNat first
    for second in boundaries do
      let b := Seq.ofNat second
      let delta := unsignedDistance first second
      ensure (Seq.distance a b == delta && Seq.before a b == referenceBefore first second &&
        (Seq.distance a b == 0) == (first == second) && a.add delta == b && !Seq.before a a)
        "Cyclic distance must agree with independent conditional subtraction and equality."
      ensure (!(Seq.before a b && Seq.before b a)) "Open half-space comparison must remain asymmetric."
      for offset in offsets do
        ensure ((a.add offset).val == referenceAdd first offset &&
          Seq.distance (a.add offset) (b.add offset) == delta &&
          Seq.before (a.add offset) (b.add offset) == referenceBefore first second)
          "Translation must preserve serial comparison and distance across every selected wrap boundary."
      for length in lengths do
        ensure (Seq.inInterval a length b == decide (delta < length))
          "Interval membership must use unsigned forward distance and exclude its upper endpoint."
  for first in boundaries do
    for middle in boundaries do
      for last in boundaries do
        let a := Seq.ofNat first
        let c := Seq.ofNat last
        let span := unsignedDistance first middle + unsignedDistance middle last
        if referenceBefore first middle && referenceBefore middle last && decide (span < 2147483648) then
          ensure (Seq.before a c) "Transitivity applies only when the combined forward span is below the half-space."

private def arcTests : IO Unit := do
  for originValue in [0, 2147483648, 4294967292] do
    let origin := Seq.ofNat originValue
    for length in [1, 2, 8, 17, 2147483647] do
      let coordinates := [0, 1, 2, 7, 8, 16, 2147483646].filter (· < length)
      for first in coordinates do
        let a := origin.add first
        ensure (Seq.inInterval origin length a && Seq.distance origin a == first)
          "Every bounded arc coordinate must identify exactly its forward sequence position."
        for second in coordinates do
          let b := origin.add second
          ensure (Seq.before a b == decide (first < second))
            "Serial comparison inside a common short arc must equal ordinary coordinate comparison."
          if first ≤ second then
            ensure (Seq.distance a b == second - first) "Ordered coordinates must yield the exact nonwrapping distance."
  let start := Seq.ofNat 4294967294
  ensure (Seq.inInterval start 4 (Seq.ofNat 1) && !Seq.inInterval start 4 (Seq.ofNat 2) &&
    !Seq.inInterval start 0 start && Seq.inInterval start 1 start)
    "A wrapping half-open interval must exclude its endpoint, and an empty interval must exclude its start."
  let a := Seq.ofNat 0
  let b := Seq.ofNat 1610612736
  let c := Seq.ofNat 3221225472
  ensure (Seq.before a b && Seq.before b c && Seq.before c a && !Seq.before a c)
    "Cyclic serial comparison has a concrete three-cycle and cannot provide unrestricted transitivity."
  let a := Seq.ofNat 4294967291
  let b := Seq.ofNat 4294967295
  let c := Seq.ofNat 2147483643
  ensure (Seq.before a b && Seq.before b c && Seq.distance a c == 2147483648 &&
    !Seq.before a c && !Seq.before c a)
    "A combined span equal to the half-space is incomparable, so transitivity requires a strict bound."

private def occupiedTests : IO Unit := do
  for flagsValue in List.range 256 do
    let flags := UInt8.ofNat flagsValue
    let controls := (if flagsValue % 4 ≥ 2 then 1 else 0) + flagsValue % 2
    for payload in [0, 1, 37, 65515, 4294967295, 4294967296, 4294967297] do
      ensure (occupiedLength payload flags == payload + controls)
        "Only SYN and FIN consume sequence positions in addition to the payload."
      for initial in [0, 2147483648, 4294967295] do
        ensure ((nextSequence (Seq.ofNat initial) payload flags).val == referenceAdd initial (payload + controls))
          "The next sequence position must include both controls and preserve modular wrap for arbitrary payload lengths."
  ensure (occupiedLength 0 0x10 == 0 && occupiedLength 0 0x04 == 0 && occupiedLength 0 0x02 == 1 &&
    occupiedLength 0 0x01 == 1 && occupiedLength 0 0x03 == 2 && occupiedLength 5 0xff == 7)
    "ACK and RST add no positions; SYN and FIN each add one even when both are present."

def run : IO Unit := do
  fixtureTests
  arithmeticTests
  arcTests
  occupiedTests

end NetlibTest.TCPSequenceSpace
