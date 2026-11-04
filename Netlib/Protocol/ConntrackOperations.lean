import Netlib.Protocol.ConntrackLifecycle
import Netlib.Protocol.Transition

/-!
# Ordered conntrack operations

Each packet call can use a different policy snapshot.
Deletion removes both direction keys of an associated record.
Successful operations preserve ordinary-table validity, not an arbitrary security or availability contract.
-/

namespace Netlib.Protocol.ConntrackLifecycle

open Packet

private theorem flatMap_sublist (f : α → List β) {left right : List α} (inside : left.Sublist right) :
    (left.flatMap f).Sublist (right.flatMap f) := by
  induction inside with
  | slnil => exact .slnil
  | cons value _ ih =>
    exact ih.trans (List.sublist_append_right (f value) _)
  | cons_cons value _ ih => exact ih.append_left (f value)

def State.erase (state : State) (zone : Nat) (packet : Header) : State :=
  ⟨state.records.filter fun record => decide
    (record.entry.flow.key .original ≠ (zone, packet) ∧ record.entry.flow.key .reply ≠ (zone, packet))⟩

theorem State.erase_valid (state : State) (zone : Nat) (packet : Header) (valid : state.Valid) :
    (state.erase zone packet).Valid := by
  have subrecords : (state.erase zone packet).records.Sublist state.records := List.filter_sublist
  have subflows := subrecords.map (fun record => record.entry.flow)
  have subslots := flatMap_sublist (fun entry : FlowNAT.Entry =>
    [FlowNAT.Hit.mk entry .original, FlowNAT.Hit.mk entry .reply]) subflows
  have subkeys := subslots.map FlowNAT.Hit.key
  constructor
  · constructor
    · intro entry member
      exact valid.1.1 entry (subflows.subset member)
    · exact valid.1.2.sublist subkeys
  · intro record member
    exact valid.2 record (subrecords.subset member)

theorem State.erase_lookup (state : State) (zone : Nat) (packet : Header) :
    (state.erase zone packet).model.lookup zone packet = none := by
  cases found : (state.erase zone packet).model.lookup zone packet with
  | none => rfl
  | some hit =>
    obtain ⟨member, key⟩ := FlowNAT.Snapshot.lookup_sound _ _ _ _ found
    obtain ⟨record, member, same⟩ := List.mem_map.mp member
    have different := of_decide_eq_true (List.mem_filter.mp member).2
    cases direction : hit.direction with
    | original => exact False.elim (different.1 (by simpa [FlowNAT.Hit.key, same, direction] using key))
    | reply => exact False.elim (different.2 (by simpa [FlowNAT.Hit.key, same, direction] using key))

namespace Operations

inductive Event where
  | packet (call : Call)
  | erase (zone : Nat) (packet : Header)

structure Result where
  state : State
  valid : state.Valid
  packet : Option Outcome

def step (state : State) : Event → Except Error Result
  | .packet call => do
    let outcome ← ConntrackLifecycle.step call.pipeline state call.input
    return ⟨outcome.state, outcome.valid, some outcome⟩
  | .erase zone packet => do
    if zone ≥ 65536 then throw .invalidZone
    if valid : state.check = true then
      return ⟨state.erase zone packet,
        state.erase_valid zone packet ((State.check_correct _).mp valid), none⟩
    else throw .invalidState

def transition : Transition State Event where
  step before event after := ∃ result, step before event = .ok result ∧ result.state = after

theorem invariant : transition.Invariant State.Valid := by
  intro before event after _ edge
  obtain ⟨result, _, rfl⟩ := edge
  exact result.valid

inductive ExecutionTrace : State → List Event → List Result → State → Prop
  | nil (state : State) : ExecutionTrace state [] [] state
  | cons {before final : State} {event : Event} {events : List Event}
      {result : Result} {results : List Result}
      (accepted : step before event = .ok result)
      (rest : ExecutionTrace result.state events results final) :
      ExecutionTrace before (event :: events) (result :: results) final

theorem ExecutionTrace.toTransition {before final : State} {events : List Event} {results : List Result}
    (trace : ExecutionTrace before events results final) : transition.Trace before events final := by
  induction trace with
  | nil => exact .nil _
  | cons accepted _ ih => exact .cons ⟨_, accepted, rfl⟩ ih

structure Execution (initial : State) (events : List Event) where
  final : State
  results : List Result
  covered : results.length = events.length
  trace : ExecutionTrace initial events results final

def execute (initial : State) : (events : List Event) → Except Error (Execution initial events)
  | [] => .ok ⟨initial, [], rfl, .nil initial⟩
  | event :: events => do
    match accepted : step initial event with
    | .error error => throw error
    | .ok result =>
      let rest ← execute result.state events
      return ⟨rest.final, result :: rest.results, by simp only [List.length_cons, rest.covered],
        .cons accepted rest.trace⟩

theorem Execution.final_valid (execution : Execution initial events) (valid : initial.Valid) :
    execution.final.Valid := invariant.trace valid execution.trace.toTransition

end Operations
end Netlib.Protocol.ConntrackLifecycle
