import Netlib.Protocol.TCP.ReceiveWindow

namespace NetlibTest.TCPReceiveWindow

open Netlib.Protocol.TCP
open Netlib.Protocol.TCP.ReceiveWindow

example (next sequence : Seq) (window length : Nat) :
    accepts next window sequence length = true ↔ Acceptable next window sequence length :=
  accepts_correct next window sequence length

example (next sequence : Seq) (window length offset : Nat) :
    accepts (next.add offset) window (sequence.add offset) length = accepts next window sequence length :=
  accepts_translate next sequence window length offset

example (next : Seq) (window : Nat) (positive : 0 < window) (short : window < Seq.halfSpace) :
    accepts next window (next.add (Seq.modulus - 1)) (window + 2) = false :=
  covered_window_rejected next window positive short

example (next : Seq) (window : Nat) (positive : 0 < window) (short : window < Seq.halfSpace) :
    (∀ position, Seq.InInterval next window position →
      Seq.InInterval (next.add (Seq.modulus - 1)) (window + 2) position) ∧
      accepts next window (next.add (Seq.modulus - 1)) (window + 2) = false :=
  covered_window_counterexample next window positive short

example : accepts (Seq.ofNat 100) 10 (Seq.ofNat 99) 12 = false := by decide

example : Seq.InInterval (Seq.ofNat 99) 12 (Seq.ofNat 100) ∧
    Seq.InInterval (Seq.ofNat 99) 12 (Seq.ofNat 109) := by decide

example (window : Netlib.Protocol.InternetChecksum.Word) : window.val < Seq.halfSpace :=
  unscaled_short window

private def ensure (value : Bool) (message : String) : IO Unit := do
  unless value do throw (IO.userError message)

private def referenceInside (left width position : Nat) : Bool :=
  if width = 0 then false
  else if left + width ≤ 4294967296 then decide (left ≤ position ∧ position < left + width)
  else decide (left ≤ position ∨ position < left + width - 4294967296)

private def referenceLast (sequence length : Nat) : Nat :=
  let last := sequence + length - 1
  if last < 4294967296 then last else last - 4294967296

private def referenceAccepts (next window sequence length : Nat) : Bool :=
  if length = 0 then
    if window = 0 then sequence == next else referenceInside next window sequence
  else if window = 0 then false
  else referenceInside next window sequence || referenceInside next window (referenceLast sequence length)

private def sample (sequence flags payloadLength : Nat) : Segment :=
  { sourcePort := 12345
    destinationPort := 80
    sequence := Seq.ofNat sequence
    acknowledgment := Seq.ofNat 0
    reserved := 0
    flags := UInt8.ofNat flags
    window := 8192
    checksum := 0
    urgentPointer := 0
    options := []
    payload := List.replicate payloadLength 0x5a }

private def fixtureTests : IO Unit := do
  let fixtures : List (Nat × Nat × Nat × Nat × Bool) := [
    (10, 0, 10, 0, true), (10, 0, 11, 0, false), (10, 0, 9, 0, false),
    (10, 0, 10, 1, false), (10, 0, 9, 2, false),
    (10, 3, 10, 0, true), (10, 3, 11, 0, true), (10, 3, 12, 0, true),
    (10, 3, 13, 0, false), (10, 3, 9, 0, false),
    (10, 3, 10, 1, true), (10, 3, 12, 1, true), (10, 3, 13, 1, false),
    (10, 3, 9, 2, true), (10, 3, 9, 1, false), (10, 3, 12, 2, true),
    (10, 3, 13, 2, false), (10, 3, 9, 5, false),
    (100, 10, 99, 12, false), (100, 10, 99, 11, true), (100, 10, 100, 11, true),
    (4294967294, 4, 4294967294, 0, true), (4294967294, 4, 4294967295, 0, true),
    (4294967294, 4, 0, 0, true), (4294967294, 4, 1, 0, true), (4294967294, 4, 2, 0, false),
    (4294967294, 4, 4294967293, 2, true), (4294967294, 4, 4294967293, 6, false),
    (0, 1, 4294967295, 2, true), (0, 1, 4294967295, 3, false),
    (0, 2147483647, 2147483646, 0, true), (0, 2147483647, 2147483647, 0, false)]
  for (next, window, sequence, length, expected) in fixtures do
    ensure (accepts (Seq.ofNat next) window (Seq.ofNat sequence) length == expected)
      "The four sequence tests must match each independent boundary fixture."
    ensure (referenceAccepts next window sequence length == expected)
      "The split-window reference must match each literal fixture."
  ensure (!accepts (Seq.ofNat 100) 10 (Seq.ofNat 99) 12 &&
    referenceInside 99 12 100 && referenceInside 99 12 109)
    "Interior overlap alone does not satisfy the first-or-last requirement."
  for offset in List.range 10 do
    ensure (referenceInside 99 12 (100 + offset))
      "The rejected segment contains every position of the receive window."
  ensure (accepts (Seq.ofNat 10) 3 (Seq.ofNat 12) 9)
    "The sequence test does not require the whole segment to fit."

private def matrixTests : IO Unit := do
  let points := [0, 1, 2, 9, 10, 11, 12, 13, 65534, 65535, 2147483646,
    2147483647, 2147483648, 2147483649, 4294967293, 4294967294, 4294967295]
  let windows := [0, 1, 2, 3, 10, 65535, 2147483647]
  let lengths := [0, 1, 2, 3, 10, 12, 65535, 2147483647, 4294967295]
  for next in points do
    for sequence in points do
      for window in windows do
        for length in lengths do
          let expected := referenceAccepts next window sequence length
          let observed := accepts (Seq.ofNat next) window (Seq.ofNat sequence) length
          ensure (observed == expected)
            "Sequence tests must agree with the independent split-window calculation."
          for offset in [0, 1, 65535, 2147483648, 4294967295, 4294967296, 4294967313] do
            ensure (accepts ((Seq.ofNat next).add offset) window ((Seq.ofNat sequence).add offset) length == expected)
              "A common translation must keep the result across sequence wrap."
          if bounded : window ≤ 65535 then
            let word : Netlib.Protocol.InternetChecksum.Word := ⟨window, by omega⟩
            ensure (acceptsUnscaled (Seq.ofNat next) word (Seq.ofNat sequence) length == expected)
              "The unscaled adapter must use all 16 bits of the window field."

private def controlTests : IO Unit := do
  for flags in List.range 256 do
    let controls := (if flags % 4 ≥ 2 then 1 else 0) + flags % 2
    for payloadLength in [0, 1, 2, 9, 20] do
      let occupied := payloadLength + controls
      for next in [0, 10, 4294967295] do
        for sequence in [0, 9, 10, 11, 4294967294, 4294967295] do
          let segment := sample sequence flags payloadLength
          ensure (segmentLength segment == occupied)
            "Only SYN and FIN add sequence positions beyond the payload byte count."
          for window in [0, 1, 2, 10, 65535] do
            ensure (acceptsSegment (Seq.ofNat next) window segment == referenceAccepts next window sequence occupied)
              "The segment adapter must count control positions before the sequence test."
  ensure (acceptsSegment (Seq.ofNat 10) 0 (sample 10 0x10 0) &&
    acceptsSegment (Seq.ofNat 10) 0 (sample 10 0x04 0) &&
    !acceptsSegment (Seq.ofNat 10) 0 (sample 10 0x02 0) &&
    !acceptsSegment (Seq.ofNat 10) 0 (sample 10 0x01 0))
    "This sequence test does not process the RST action or require the ACK flag."
  ensure (acceptsSegment (Seq.ofNat 10) 1 (sample 9 0x03 0) &&
    !acceptsSegment (Seq.ofNat 10) 1 (sample 9 0x02 0))
    "A segment with SYN and FIN has two occupied positions."

def run : IO Unit := do
  fixtureTests
  matrixTests
  controlTests

end NetlibTest.TCPReceiveWindow
