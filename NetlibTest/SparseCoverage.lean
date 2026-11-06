import Netlib.Theory.SparseCoverage

namespace NetlibTest.SparseCoverage

namespace S
export Netlib.Theory.SparseCoverage (Run State Result Stop initial current accept Compatible Slice)
end S

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def accepted (value : Except S.Stop (S.Result Meta)) : IO (S.Result Meta) :=
  match value with
  | .ok result => pure result
  | .error reason => throw (IO.userError s!"Sparse input stopped: {repr reason}")

private def stopped (value : Except S.Stop α) (reason : S.Stop) : Bool :=
  match value with | .error actual => actual == reason | .ok _ => false

private def payload (value : UInt8) : List UInt8 := List.replicate 200 value

theorem supported_input_exists (state : S.State Meta) (position bound : Nat)
    (bytes : List UInt8) (metadata : Meta) (valid : state.Valid bound)
    (nonempty : bytes ≠ []) (inside : position + bytes.length ≤ bound)
    (geometry : S.Compatible (S.current state position bytes metadata) state.runs) :
    ∃ result, S.accept state position bytes metadata bound = .ok result :=
  Netlib.Theory.SparseCoverage.accept_exists state position bytes metadata bound valid nonempty inside geometry

theorem unseen_hole_limits_frontier (state : S.State Meta) (bound position : Nat)
    (valid : state.Valid bound) (hole : ¬state.Covers position) : state.frontier ≤ position :=
  state.frontier_le_of_not_covered bound valid position hole

theorem accepted_byte_has_source (state : S.State Meta) (position bound : Nat)
    (bytes : List UInt8) (metadata : Meta) (result : S.Result Meta)
    (selected : S.accept state position bytes metadata bound = .ok result)
    (index : Nat) (byte : UInt8) (present : bytes[index]? = some byte) :
    result.source.bytes[result.offset + index]? = some byte :=
  Netlib.Theory.SparseCoverage.accept_index state position bytes metadata bound result selected index byte present

theorem repeated_slice_keeps_source (state : S.State Meta) (position bound : Nat)
    (bytes : List UInt8) (metadata : Meta) (result : S.Result Meta)
    (selected : S.accept state position bytes metadata bound = .ok result)
    (source : S.Run Meta) (member : source ∈ state.runs) (offset : Nat)
    (slice : S.Slice source position bytes offset) :
    result.state = state ∧ result.source = source ∧ result.offset = offset ∧ result.novel = 0 :=
  Netlib.Theory.SparseCoverage.accept_first_source state position bytes metadata bound result selected source member offset slice

def run : IO Unit := do
  let high ← accepted (S.accept (S.initial : S.State Nat) 600 (payload 6) 60 800)
  check (high.state.frontier == 0 && high.state.highEnd == 800 && high.state.count == 200)
    "A high end must not cover earlier holes."
  check (high.source.sourceID == 0 && high.source.metadata == 60 && high.offset == 0 && high.novel == 200)
    "The first original run must have its internal source."
  check (decide (¬high.state.Covers 400)) "The unseen middle hole must remain open."
  let middle ← accepted (S.accept high.state 200 (payload 2) 20 800)
  check (middle.state.frontier == 0 && middle.state.highEnd == 800 && middle.state.count == 400)
    "A second disjoint observation must leave both holes open."
  let slice ← accepted (S.accept middle.state 650 (List.replicate 50 6) 999 800)
  check (slice.state == middle.state && slice.novel == 0 && slice.offset == 50)
    "A contained exact slice must add no coverage or source ID."
  check (slice.source == high.source && slice.source.metadata == 60 && slice.state.nextID == 2)
    "A repeated slice must retain the whole first source."
  check (stopped (S.accept middle.state 650 (List.replicate 50 8) 888 800) .conflict)
    "Changed contained bytes must stop as a conflict."
  check (stopped (S.accept middle.state 350 (List.replicate 100 2) 35 800) .overlap)
    "A mixed overlap must not fill the unseen part."
  check (stopped (S.accept middle.state 790 (List.replicate 20 6) 79 800) .bounds)
    "A right-edge violation must stop before insertion."
  check (stopped (S.accept middle.state 400 [] 40 800) .empty)
    "An empty observation must add no run."
  let firstHole ← accepted (S.accept middle.state 0 (payload 0) 0 800)
  check (firstHole.state.frontier == 400 && firstHole.state.highEnd == 800 && firstHole.state.count == 600)
    "Filling the first unseen hole must advance only through covered bytes."
  check (firstHole.source.sourceID == 2 && firstHole.state.runs.length == 3)
    "A new hole must mint a source and retain all original runs."
  check (firstHole.state.runs.any (fun run => run == high.source))
    "Historical high data must remain in the ledger."
  let final ← accepted (S.accept firstHole.state 400 (payload 4) 40 800)
  check (final.state.frontier == 800 && final.state.highEnd == 800 && final.state.count == 800)
    "The second hole must complete the covered prefix."
  check (final.state.nextID == 4 && final.state.runs.length == 4 && decide (final.state.Valid 800))
    "Four original runs must retain four unique sources."
  let oldSlice ← accepted (S.accept final.state 250 (List.replicate 100 2) 777 800)
  check (oldSlice.state == final.state && oldSlice.source == middle.source && oldSlice.offset == 50)
    "A later contained slice must still use the original source."
  let joined := payload 0 ++ payload 2
  check (stopped (S.accept final.state 0 joined 12 800) .overlap)
    "A packet across two original runs must retain the overlap stop."
  let invalid : S.State Nat := ⟨[high.source], 0⟩
  check (stopped (S.accept invalid 0 (payload 0) 0 800) .invalid)
    "An unallocated source must fail seed validation."
  let functional ← accepted (S.accept (S.initial : S.State (Nat → Nat)) 0 [7] (fun value => value + 9) 1)
  check (functional.source.metadata 4 == 13)
    "Generic source metadata must not need an equality instance."

end NetlibTest.SparseCoverage
