import Netlib.Theory.Outstanding

namespace NetlibTest.Outstanding

open Netlib.Theory.Outstanding

private structure Payload where
  tagged : Bool
  operation : Nat → Nat

private def payload (tagged : Bool) (number : Nat) : Payload := ⟨tagged, fun input => number + input⟩

private def tagged (value : Payload) : Bool := value.tagged

private def initial : State Payload := State.initial

private def base : State Payload :=
  enqueue (enqueue (enqueue (enqueue initial (payload true 11)) (payload false 22)) (payload true 33)) (payload false 44)

example (state : State α) : state.check = true ↔ state.Valid := State.check_correct state
example (state : State α) (value : α) (valid : state.Valid) : (enqueue state value).Valid := enqueue_valid state value valid
example {α : Type} {before : State α} {id : Nat} (result : Completed before id) (valid : before.Valid) : result.state.Valid := result.valid valid
example {α : Type} {before : State α} {id : Nat} (result : Completed before id) (valid : before.Valid) : complete result.state id = .error .notPending :=
  result.no_repeat valid
example (state : State α) (property : α → Bool) (valid : state.Valid) :
    ∃ final, Trace property state final 0 (count state property) ∧ final.Valid ∧ count final property = 0 :=
  drain_exists state property valid

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load (result : Except Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error.describe)

private def absent (result : Except Error α) : Bool :=
  match result with
  | .error .notPending => true
  | .ok _ => false

private def insertions (head : Nat) : List Nat → List (List Nat)
  | [] => [[head]]
  | first :: rest => (head :: first :: rest) :: (insertions head rest).map (first :: ·)

private def orders : List Nat → List (List Nat)
  | [] => [[]]
  | head :: rest => (orders rest).flatMap (insertions head)

private def permutationTests : IO Unit := do
  let permutations := orders [0, 1, 2, 3]
  ensure (permutations.length == 24) "Exercise every completion order for four independent identities."
  for order in permutations do
    let mut state := base
    let mut pending := [0, 1, 2, 3]
    let mut retired : List Nat := []
    for id in order do
      let result ← load (complete state id)
      let expected := [11, 22, 33, 44][id]!
      pending := pending.filter (· != id)
      retired := retired ++ [id]
      ensure (result.item.id == id && result.item.value.operation 10 == expected + 10 &&
        result.state.pending.map (·.id) == pending && result.state.completed.map (·.id) == retired &&
        result.state.nextID == 4 && result.state.check)
        "Completion must retire the actual payload and preserve allocation and completion chronology in any order."
      let expectedCount := (pending.filter (fun id => id == 0 || id == 2)).length
      ensure (count result.state tagged == expectedCount &&
        count result.state tagged + completedCount result.state tagged == 2)
        "Tagged work must conserve its admitted count across arbitrary completion order."
      ensure (absent (complete result.state id)) "A completed identity must never complete twice."
      state := result.state
    ensure (state.pending.isEmpty && state.completed.map (·.id) == order && count state tagged == 0)
      "A finite completion schedule must drain every admitted item without a FIFO requirement."

private def interleavedTests : IO Unit := do
  let first ← load (complete base 2)
  ensure (first.item.value.operation 0 == 33 && count first.state tagged == 1)
    "Completing a later tagged identity must retire exactly that original item."
  let admitted := enqueue first.state (payload false 55)
  ensure (admitted.nextID == 5 && (newItem first.state (payload false 55)).id == 4 &&
    admitted.pending.map (·.id) == [0, 1, 3, 4] && count admitted tagged == 1)
    "Fresh untagged admissions must preserve the old tagged drain count and never reuse completed IDs."
  let unrelated ← load (complete admitted 1)
  ensure (count unrelated.state tagged == 1 && unrelated.state.completed.map (·.id) == [2, 1])
    "An unrelated completion must preserve the tagged count and append actual chronology."
  let drained ← load (complete unrelated.state 0)
  ensure (count drained.state tagged == 0 && drained.state.pending.map (·.id) == [3, 4] &&
    drained.state.completed.map (·.id) == [2, 1, 0])
    "Tagged work can drain while newer untagged work remains pending."
  ensure (absent (complete drained.state 2) && absent (complete drained.state 99) && absent (complete drained.state 5))
    "Completed, unknown, and future identities must fail without selecting arbitrary payloads."
  let resumed := enqueue drained.state (payload true 66)
  ensure (resumed.nextID == 6 && count resumed tagged == 1 && resumed.pending.map (·.id) == [3, 4, 5])
    "A new tagged admission must invalidate an earlier zero-count drain condition."
  let duplicate : State Payload := ⟨1, [⟨0, payload false 1⟩, ⟨0, payload true 2⟩], []⟩
  let future : State Payload := ⟨2, [⟨2, payload false 1⟩], []⟩
  let repeated : State Payload := ⟨1, [⟨0, payload false 1⟩], [⟨0, payload true 2⟩]⟩
  ensure (!duplicate.check && !future.check && !repeated.check)
    "Validation must reject duplicate IDs, unallocated IDs, and IDs shared by pending and completed work."

def run : IO Unit := do
  ensure (initial.check && base.check && base.nextID == 4 && count base tagged == 2)
    "Admission must preserve valid identity allocation without payload equality."
  permutationTests
  interleavedTests

end NetlibTest.Outstanding
