import Netlib.Theory.TimedReaction

namespace NetlibTest.TimedReaction

open Netlib.Theory
abbrev Work := TimedReaction.State String Nat Nat

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load : Except TimedReaction.Error α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError s!"Unexpected timed reaction error: {repr reason}.")

private def stopped (result : Except TimedReaction.Error α) (expected : TimedReaction.Error) : IO Unit :=
  match result with
  | .error actual => ensure (actual == expected) "The timed reaction error differs."
  | .ok _ => throw (IO.userError "The timed reaction passed an unsupported boundary.")

private def covers (demand output : Nat) : Bool := decide (demand ≤ output)

private def bounds : IO Unit := do
  let initial : Work := TimedReaction.initial "receiver"
  let first := TimedReaction.issue initial 0 400 499
  let second := TimedReaction.issue first 100 800 499
  ensure (TimedReaction.credit second == 2 && second.nextID == 2 && second.nextDischarge == 0 &&
      second.pending.map (·.id) == [0, 1] && TimedReaction.pendingDue second == some 499)
    "Coalescing must retain both actual cause identities and the oldest due time."
  stopped (TimedReaction.complete second 500 800 covers) .deadline
  stopped (TimedReaction.complete second 99 800 covers) .clock
  stopped (TimedReaction.complete second 499 799 covers) .coverage
  let completed ← load (TimedReaction.complete second 499 800 covers)
  letI : Decidable completed.Valid := by unfold TimedReaction.State.Valid; infer_instance
  ensure (TimedReaction.credit completed == 0 && completed.pending.isEmpty && completed.nextID == 2 &&
      completed.nextDischarge == 1 && completed.completed.map (·.time) == [499] &&
      completed.completed.map (·.output) == [800] &&
      (completed.completed.flatMap (·.causes)).map (·.id) == [0, 1] && decide completed.Valid)
    "One exact output must retire all covered cause credit and retain its time and identity."
  stopped (TimedReaction.complete completed 499 800 covers) .noCredit
  let immediate := TimedReaction.issue first 100 800 0
  ensure (TimedReaction.pendingDue immediate == some 100) "An immediate cause must strengthen the old deadline."
  let _ ← load (TimedReaction.complete immediate 100 800 covers)
  stopped (TimedReaction.checkTime immediate 101) .deadline
  let independent : TimedReaction.Observation Nat Nat := ⟨20, none, some (.independent, 0)⟩
  let idle ← load (TimedReaction.observe initial independent covers)
  ensure (idle == initial) "An independent output must not invent a response cause or discharge."
  stopped (TimedReaction.observe initial ⟨20, none, some (.response, 0)⟩ covers) .noCredit
  let denied ← load (TimedReaction.observe first ⟨100, none, none⟩ covers)
  ensure (denied == first) "A response without actual output must retain its cause and deadline."

structure Device where
  work : Work
  now : Nat
  received : Nat
  permitted : Bool
  deriving Repr, BEq, DecidableEq

inductive Event where
  | receive (count : Nat)
  | immediate (count : Nat)
  | tick (now : Nat)
  | reply
  | piggyback
  | permission (permitted : Bool)
  deriving Repr, BEq, DecidableEq

structure Result where
  state : Device
  request : Option (Nat × Nat)
  output : Option Nat
  kind : TimedReaction.OutputKind
  error : Option TimedReaction.Error
  deriving Repr, BEq, DecidableEq

def execute (before : Device) (event : Event) : Result :=
  let now := match event with | .tick now => now | _ => before.now
  let received := match event with | .receive count | .immediate count => before.received + count | _ => before.received
  let request := match event with
    | .receive _ => some (received, 499)
    | .immediate _ => some (received, 0)
    | _ => none
  let output := match event with
    | .reply | .piggyback | .immediate _ => if before.permitted then some received else none
    | _ => none
  let kind := match event with | .piggyback => .independent | _ => TimedReaction.OutputKind.response
  let permitted := match event with | .permission value => value | _ => before.permitted
  match TimedReaction.observe before.work ⟨now, request, output.map (kind, ·)⟩ covers with
  | .error reason => ⟨before, none, none, .independent, some reason⟩
  | .ok work => ⟨⟨work, now, received, permitted⟩, request, output, kind, none⟩

def adapter : TimedReaction.Adapter Device Event Result String Nat Nat :=
  ⟨execute, (·.state), (·.work), (·.now), (fun _ _ result => result.request), (·.output),
    (fun _ _ result => result.kind), covers⟩

def seed : Device := ⟨TimedReaction.initial "receiver", 0, 0, true⟩

def arrival : TimedReaction.CheckedStep adapter :=
  ⟨seed, .receive 400, execute seed (.receive 400), 10, rfl, by rfl⟩

def clock : TimedReaction.CheckedStep adapter :=
  ⟨arrival.after, .tick 100, execute arrival.after (.tick 100), 11, rfl, by rfl⟩

def coalesced : TimedReaction.CheckedStep adapter :=
  ⟨clock.after, .receive 400, execute clock.after (.receive 400), 12, rfl, by rfl⟩

def response : TimedReaction.CheckedStep adapter :=
  ⟨coalesced.after, .piggyback, execute coalesced.after .piggyback, 13, rfl, by rfl⟩

def immediate : TimedReaction.CheckedStep adapter :=
  ⟨seed, .immediate 300, execute seed (.immediate 300), 20, rfl, by rfl⟩

theorem checked_history : TimedReaction.History adapter seed [arrival, clock, coalesced, response] response.after :=
  .cons arrival (.cons clock (.cons coalesced (.cons response (.nil _))))

theorem actual_causal_response :
    Nonempty (TimedReaction.CausalWitness adapter [arrival, clock, coalesced, response]
      ⟨0, "receiver", 100, 800, response.before.work.pending⟩ ⟨0, "receiver", 0, 499, 400⟩) := by
  apply checked_history.causal_witness "receiver" rfl
  · exact List.mem_cons_self
  · exact List.mem_cons_self

theorem immediate_causal_response :
    Nonempty (TimedReaction.CausalWitness adapter [immediate]
      ⟨0, "receiver", 0, 300, [⟨0, "receiver", 0, 0, 300⟩]⟩ ⟨0, "receiver", 0, 0, 300⟩) := by
  apply (TimedReaction.History.cons immediate (.nil _)).causal_witness "receiver" rfl
  · exact List.mem_cons_self
  · exact List.mem_cons_self

private def operations : IO Unit := do
  let _ := actual_causal_response
  let _ := immediate_causal_response
  ensure (response.result.output == some 800 && response.after.work.pending.isEmpty &&
      response.after.work.completed.length == 1 && TimedReaction.pendingDue coalesced.after.work == some 499)
    "The checked piggyback operation must supply the actual coalesced response."
  let denied := execute (execute arrival.after (.permission false)).state .reply
  ensure (denied.output.isNone && TimedReaction.credit denied.state.work == 1 &&
      TimedReaction.pendingDue denied.state.work == some 499)
    "A locally denied checked operation must not supply output or response credit."
  ensure ((execute arrival.after (.tick 500)).error == some .deadline)
    "An actual clock operation must not pass the pending deadline."
  ensure ((execute response.after .reply).error == some .noCredit)
    "An actual second pure response must not reuse old causes."

def run : IO Unit := do
  bounds
  operations
  IO.println "Checked timed reaction tests passed."

end NetlibTest.TimedReaction
