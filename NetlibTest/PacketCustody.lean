import Netlib.Theory.PacketCustody

namespace NetlibTest.PacketCustody

open Netlib.Theory.PacketCustody

private structure Payload where
  kind : String
  bytes : List UInt8
  operation : Nat → Nat

private def packet (kind : String) (bytes : List UInt8) (offset : Nat) : Payload :=
  ⟨kind, bytes, fun input => input + offset⟩

private def initial : State Payload := .initial

private def base : State Payload :=
  mint (mint initial (packet "data" [1, 2, 3] 10)) (packet "ack" [4, 5] 20)

example (before : State α) (payload : α) (valid : before.Valid) : (mint before payload).Valid :=
  mint_valid before payload valid

example {before : State α} {parent : Nat} (result : Copied before parent) (valid : before.Valid) :
    result.state.Valid ∧ parent < result.item.id ∧ result.item.value.payload = result.source.value.payload :=
  ⟨result.valid valid, result.earlier valid, result.payload⟩

example {before : State α} {id : Nat} {disposition : Disposition}
    (result : Resolved before id disposition) (valid : before.Valid) :
    resolve result.state id .dropped = .error .notPending := result.no_repeat valid .dropped

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load (result : Except Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error.describe)

private def absent (result : Except Error α) : Bool :=
  match result with
  | .error .notPending => true
  | _ => false

private def missing (result : Except Error α) : Bool :=
  match result with
  | .error .notFound => true
  | _ => false

private def originalTests : IO Unit := do
  ensure (base.nextID == 2 && base.pending.map (·.id) == [0, 1] &&
      base.pending.map (·.value.parent) == [none, none] && base.resolutions.isEmpty && base.dropped == 0)
    "A send must allocate a pending original. An omitted action must not establish loss."
  ensure (base.pendingID (·.kind == "data") == some 0 && base.pendingID (·.kind == "ack") == some 1)
    "Selection must use an actual pending payload."
  let assigned ← load (resolve base 0 .assigned)
  ensure (assigned.item.value.payload.bytes == [1, 2, 3] &&
      assigned.item.value.payload.operation 7 == 17 && assigned.state.pending.map (·.id) == [1] &&
      assigned.state.count .assigned == 1 && assigned.state.dropped == 0 &&
      assigned.state.pendingID (·.kind == "data") == none)
    "Assignment must consume the actual data packet without counting link loss."
  for disposition in [Disposition.assigned, .delivered, .dropped] do
    ensure (absent (resolve assigned.state 0 disposition))
      "A consumed identity must fail for every later disposition."
  let copied ← load (copy assigned.state 0)
  ensure (copied.source.id == 0 && copied.item.id == 2 && copied.item.value.parent == some 0 &&
      copied.item.value.payload.bytes == [1, 2, 3] && copied.item.value.payload.operation 7 == 17 &&
      copied.state.pending.map (·.id) == [1, 2] && copied.state.dropped == 0)
    "An explicit historical copy must allocate a new identity and retain its parent's exact payload."
  let ack ← load (resolve copied.state 1 .delivered)
  let dropped ← load (resolve ack.state 2 .dropped)
  ensure (dropped.state.pending.isEmpty && dropped.state.nextID == 3 &&
      dropped.state.resolutions.map (·.item.id) == [0, 1, 2] &&
      dropped.state.count .assigned == 1 && dropped.state.count .delivered == 1 && dropped.state.dropped == 1)
    "Only the explicit packet drop must spend loss allowance."
  let descendant ← load (copy dropped.state 2)
  ensure (descendant.item.id == 3 && descendant.item.value.parent == some 2 &&
      descendant.item.value.payload.bytes == [1, 2, 3] && descendant.item.value.payload.operation 1 == 11 &&
      descendant.state.resolutions.length == 3 && descendant.state.pending.map (·.id) == [3] &&
      descendant.state.dropped == 1)
    "Copying a discarded copy must retain its actual parent and source bytes."
  ensure (missing (copy descendant.state 4) && missing (copy descendant.state 99) &&
      absent (resolve descendant.state 4 .dropped) && absent (resolve descendant.state 99 .delivered))
    "Unknown and unallocated identities must not create a packet or consume loss allowance."

private def insertions (head : Nat) : List Nat → List (List Nat)
  | [] => [[head]]
  | first :: rest => (head :: first :: rest) :: (insertions head rest).map (first :: ·)

private def orders : List Nat → List (List Nat)
  | [] => [[]]
  | head :: rest => (orders rest).flatMap (insertions head)

private def reorderedTests : IO Unit := do
  let first ← load (copy base 0)
  let second ← load (copy first.state 0)
  let permutations := orders [0, 1, 2, 3]
  ensure (permutations.length == 24) "Exercise every packet resolution order."
  for order in permutations do
    let mut state := second.state
    let mut pending := [0, 1, 2, 3]
    let mut history : List Nat := []
    let mut losses := 0
    for id in order do
      let disposition := if id == 0 then Disposition.assigned else if id == 2 then .dropped else .delivered
      let result ← load (resolve state id disposition)
      pending := pending.filter (· != id)
      history := history ++ [id]
      losses := losses + if id == 2 then 1 else 0
      let expected : List UInt8 := if id == 1 then [4, 5] else [1, 2, 3]
      ensure (result.item.id == id && result.item.value.payload.bytes == expected &&
          result.state.pending.map (·.id) == pending && result.state.resolutions.map (·.item.id) == history &&
          result.state.dropped == losses && result.state.nextID == 4 &&
          result.state.pending.length + result.state.resolutions.length == 4)
        "Reordering must preserve exact payloads, actual dispositions, and packet counts."
      ensure (absent (resolve result.state id .dropped))
        "A delivery, assignment, or drop must prevent repeated consumption."
      state := result.state
    ensure (state.pending.isEmpty && state.count .assigned == 1 && state.count .delivered == 2 && state.dropped == 1)
      "Each order must account for the same explicit actions."

def run : IO Unit := do
  originalTests
  reorderedTests

end NetlibTest.PacketCustody
