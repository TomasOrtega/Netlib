import Netlib.Protocol.TCP.ReceiveWindowEnabled

namespace NetlibTest.TCPReceiveWindowEnabled

open Netlib.Protocol.TCP
open Netlib.Protocol.TCP.ReceiveWindow

example (start : Seq) (window length : Nat) (positive : 0 < length)
    (epoch : length + window ≤ Seq.modulus) :
    accepts (start.add length) window start length = false :=
  whole_old_range_rejected start window length positive epoch

example : accepts ((Seq.ofNat 4294967294).add 4) 4294967292 (Seq.ofNat 4294967294) 4 = false := by decide

example : accepts ((Seq.ofNat 7).add Seq.modulus) 0 (Seq.ofNat 7) Seq.modulus = false := by decide

example : accepts ((Seq.ofNat 7).add Seq.modulus) 1 (Seq.ofNat 7) Seq.modulus = true := by decide

example : accepts ((Seq.ofNat 7).add 0) 0 (Seq.ofNat 7) 0 = true := by decide

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def inside (left width position : Nat) : Bool :=
  if width = 0 then false
  else if left + width ≤ 4294967296 then decide (left ≤ position ∧ position < left + width)
  else decide (left ≤ position ∨ position < left + width - 4294967296)

private def wraps (value : Nat) : Nat :=
  if value < 4294967296 then value else value - 4294967296

private def reference (start window length : Nat) : Bool :=
  if window = 0 then false
  else
    let next := wraps (start + length)
    let last := wraps (start + length - 1)
    inside next window start || inside next window last

private def segment (start length : Nat) : Segment := {
  sourcePort := 41000
  destinationPort := 9000
  sequence := Seq.ofNat start
  acknowledgment := Seq.ofNat 200
  reserved := 0
  flags := 16
  window := 1600
  checksum := 0
  urgentPointer := 0
  options := []
  payload := List.replicate length 42 }

private def geometry : IO Unit := do
  let starts := [0, 1, 9, 65535, 2147483647, 2147483648, 4294967294, 4294967295]
  let lengths := [1, 2, 4, 400, 65535, 2147483647, 4294967295, 4294967296]
  let windows := [0, 1, 2, 400, 65535, 2147483648, 4294967292, 4294967295]
  for start in starts do
    for length in lengths do
      for window in windows do
        if bound : length + window ≤ Seq.modulus then
          if positive : 0 < length then
            let _ := whole_old_range_rejected (Seq.ofNat start) window length positive bound
            ensure (!accepts ((Seq.ofNat start).add length) window (Seq.ofNat start) length &&
                !reference start window length)
              "Every whole old range must miss the window in both modular and split-interval calculations."
          else throw (IO.userError "The whole-old test requires nonempty ranges.")
        else
          pure ()
      if length < 4294967296 then
        ensure (accepts ((Seq.ofNat start).add length) 1 ((Seq.ofNat start).add length) length)
          "A new range at the current cursor must remain acceptable."
        ensure (accepts ((Seq.ofNat start).add length) 1 ((Seq.ofNat start).add 1) length)
          "A partly old range with a final position at the cursor is outside the whole-old theorem."
  ensure (accepts ((Seq.ofNat 7).add Seq.modulus) 1 (Seq.ofNat 7) Seq.modulus)
    "A full-cycle range with a positive window must violate the epoch bound rather than receive a false rejection proof."

private def segmentCases : IO Unit := do
  for start in [0, 9, 4294967294, 4294967295] do
    for length in [1, 4, 400, 800] do
      let value := segment start length
      for window in [0, 1, 1600, 65535] do
        ensure (!acceptsSegment (value.sequence.add value.payload.length) window value)
          "A control-free repeated packet must be rejected after its entire payload was consumed."


def run : IO Unit := do
  geometry
  segmentCases
  IO.println "Whole old receive-range tests passed."

end NetlibTest.TCPReceiveWindowEnabled
