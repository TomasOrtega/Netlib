import Netlib.Check.CampusRevocationModel

/-!
# Indexed states in one campus revocation replay

Cuts retain the stored effects and the original queue history.
Indices beyond the recorded steps retain the final state.
-/

namespace Netlib.Check.CampusRevocationModel

variable {input : Input} {budget : Nat}
variable {initial middle final : State} {steps later : List (Step input budget)}
variable {events following : List Event}

def stateAt (initial : State) : List (Step input budget) → Nat → State
  | [], _ => initial
  | _ :: _, 0 => initial
  | head :: tail, slot + 1 => stateAt head.effect.state tail slot

def eventAt (steps : List (Step input budget)) (slot : Nat) : Event :=
  match steps[slot]? with
  | none => .idle
  | some head => head.event

@[simp] theorem stateAt_zero (initial : State) (steps : List (Step input budget)) :
    stateAt initial steps 0 = initial := by cases steps <;> rfl

theorem stateAt_offset (initial : State) (steps : List (Step input budget)) (start offset : Nat) :
    stateAt (stateAt initial steps start) (steps.drop start) offset =
      stateAt initial steps (start + offset) := by
  induction steps generalizing initial start with
  | nil => simp only [List.drop_nil, stateAt]
  | cons head tail ih =>
    cases start with
    | zero => simp only [List.drop_zero, stateAt_zero, Nat.zero_add]
    | succ start => simpa only [List.drop_succ_cons, stateAt, Nat.succ_add] using ih head.effect.state start

theorem stateAt_beyond (initial : State) (steps : List (Step input budget)) (slot : Nat)
    (after : steps.length ≤ slot) : stateAt initial steps slot = stateAt initial steps steps.length := by
  induction steps generalizing initial slot with
  | nil => rfl
  | cons head tail ih =>
    cases slot with
    | zero => simp only [List.length_cons] at after; omega
    | succ slot =>
      have within : tail.length ≤ slot := by simpa only [List.length_cons, Nat.add_one_le_add_one_iff] using after
      simpa only [List.length_cons, stateAt] using ih head.effect.state slot within

theorem stateAt_take (initial : State) (steps : List (Step input budget)) (count slot : Nat) (within : slot ≤ count) :
    stateAt initial (steps.take count) slot = stateAt initial steps slot := by
  induction steps generalizing initial count slot with
  | nil => simp only [List.take_nil]
  | cons head tail ih =>
    cases count with
    | zero =>
      have zero : slot = 0 := by omega
      subst slot
      simp only [stateAt_zero]
    | succ count =>
      cases slot with
      | zero => simp only [stateAt_zero]
      | succ slot =>
        have smaller : slot ≤ count := by omega
        simpa only [List.take_succ_cons, stateAt] using ih head.effect.state count slot smaller

theorem Trace.at (trace : Trace input budget initial steps final) (slot : Nat) (within : slot < steps.length) :
    ∃ head, steps[slot]? = some head ∧ head.before = stateAt initial steps slot ∧
      head.event = eventAt steps slot ∧ head.effect.state = stateAt initial steps (slot + 1) := by
  induction trace generalizing slot with
  | nil => simp at within
  | cons head rest ih =>
    cases slot with
    | zero => exact ⟨head, rfl, rfl, rfl, by simp [stateAt]⟩
    | succ slot =>
      have smaller : slot < _ := Nat.lt_of_succ_lt_succ within
      obtain ⟨actual, found, before, event, after⟩ := ih slot smaller
      exact ⟨actual, found, before, event, after⟩

theorem Trace.at_step (trace : Trace input budget initial steps final) {slot : Nat} {head : Step input budget}
    (found : steps[slot]? = some head) :
    head.before = stateAt initial steps slot ∧ head.event = eventAt steps slot ∧
      head.effect.state = stateAt initial steps (slot + 1) := by
  obtain ⟨actual, selected, before, event, after⟩ := trace.at slot (List.getElem?_eq_some_iff.mp found).1
  have same : actual = head := Option.some.inj (selected.symm.trans found)
  subst actual
  exact ⟨before, event, after⟩

theorem Trace.last_state (trace : Trace input budget initial steps final) :
    stateAt initial steps steps.length = final := by
  induction trace with
  | nil => rfl
  | cons head rest ih => simpa only [List.length_cons, stateAt] using ih

theorem Trace.stateAt_of_length_le (trace : Trace input budget initial steps final)
    (slot : Nat) (after : steps.length ≤ slot) : stateAt initial steps slot = final := by
  rw [stateAt_beyond initial steps slot after, trace.last_state]

theorem Trace.take (trace : Trace input budget initial steps final) (count : Nat) (within : count ≤ steps.length) :
    Trace input budget initial (steps.take count) (stateAt initial steps count) := by
  induction trace generalizing count with
  | nil =>
    have zero : count = 0 := by simp only [List.length_nil] at within; omega
    subst count
    exact .nil _
  | cons head rest ih =>
    cases count with
    | zero => exact .nil _
    | succ count =>
      have smaller : count ≤ _ := Nat.le_of_succ_le_succ within
      simpa only [List.take_succ_cons, stateAt] using Trace.cons head (ih count smaller)

theorem Trace.drop (trace : Trace input budget initial steps final) (count : Nat) :
    Trace input budget (stateAt initial steps count) (steps.drop count) final := by
  induction trace generalizing count with
  | nil => simp only [List.drop_nil, stateAt]; exact .nil _
  | cons head rest ih =>
    cases count with
    | zero => exact .cons head rest
    | succ count => simpa only [List.drop_succ_cons, stateAt] using ih count

theorem Trace.split (trace : Trace input budget initial steps final) (count : Nat) (within : count ≤ steps.length) :
    Trace input budget initial (steps.take count) (stateAt initial steps count) ∧
      Trace input budget (stateAt initial steps count) (steps.drop count) final :=
  ⟨trace.take count within, trace.drop count⟩

theorem Trace.append (trace : Trace input budget initial steps middle) (tail : Trace input budget middle later final) :
    Trace input budget initial (steps ++ later) final := by
  induction trace with
  | nil => exact tail
  | cons head rest ih => exact .cons head (ih tail)

theorem Trace.safe (trace : Trace input budget initial steps final) (safe : initial.Safe input) : final.Safe input := by
  induction trace with
  | nil => exact safe
  | cons head rest ih => exact ih head.effect.safe

theorem Trace.stateAt_safe (trace : Trace input budget initial steps final) (safe : initial.Safe input)
    (slot : Nat) (within : slot ≤ steps.length) : (stateAt initial steps slot).Safe input :=
  (trace.take slot within).safe safe

def ticks (steps : List (Step input budget)) : List (Theory.Queue.Tick Datagram) :=
  steps.map (·.effect.payload.tick)

def arrivals (steps : List (Step input budget)) : List Datagram :=
  steps.flatMap (·.effect.payload.arrivals)

def served (steps : List (Step input budget)) : List Datagram :=
  steps.flatMap (·.effect.served)

theorem Trace.queue_run (trace : Trace input budget initial steps final) :
    final.queue = Theory.Queue.run initial.queue (ticks steps) := by
  induction trace with
  | nil => rfl
  | cons head rest ih => rw [ih]; rfl

theorem Trace.queue_at (trace : Trace input budget initial steps final) (slot : Nat) (within : slot ≤ steps.length) :
    (stateAt initial steps slot).queue = Theory.Queue.run initial.queue (ticks (steps.take slot)) :=
  (trace.take slot within).queue_run

theorem Trace.conservation (trace : Trace input budget initial steps final) :
    final.queue.delivered ++ final.queue.pending = initial.queue.delivered ++ initial.queue.pending ++ arrivals steps := by
  rw [trace.queue_run]
  simpa only [ticks, arrivals, List.flatMap_map, Function.comp_def, Payload.tick] using
    Theory.Queue.run_conservation initial.queue (ticks steps)

theorem Trace.delivered (trace : Trace input budget initial steps final) :
    final.queue.delivered = initial.queue.delivered ++ served steps := by
  induction trace with
  | nil => simp [served]
  | cons head rest ih =>
    rw [ih]
    change (Theory.Queue.advance head.before.queue head.effect.payload.tick).delivered ++ served _ = _
    rw [Theory.Queue.advance, Theory.Queue.delivered_append]
    simp only [served, List.flatMap_cons, Effect.served, List.append_assoc]

theorem Trace.served_pending (trace : Trace input budget initial steps final) :
    served steps ++ final.queue.pending = initial.queue.pending ++ arrivals steps := by
  have conserved := trace.conservation
  rw [trace.delivered] at conserved
  simp only [List.append_assoc] at conserved
  exact List.append_cancel_left conserved

theorem Run.covered_length (execution : Run input budget initial events) : execution.steps.length = events.length := by
  simpa only [List.length_map] using congrArg List.length execution.covered

theorem Run.source_at (execution : Run input budget initial events) {slot : Nat} {head : Step input budget}
    (found : execution.steps[slot]? = some head) : events[slot]? = some head.event := by
  rw [← execution.covered, List.getElem?_map, found]
  rfl

def Run.cut (execution : Run input budget initial events) (count : Nat) (within : count ≤ execution.steps.length) :
    Run input budget initial (events.take count) where
  final := stateAt initial execution.steps count
  steps := execution.steps.take count
  trace := execution.trace.take count within
  covered := by rw [List.map_take, execution.covered]

def Run.suffix (execution : Run input budget initial events) (count : Nat) :
    Run input budget (stateAt initial execution.steps count) (events.drop count) where
  final := execution.final
  steps := execution.steps.drop count
  trace := execution.trace.drop count
  covered := by rw [List.map_drop, execution.covered]

def Report.cut (report : Report input budget events) (count : Nat) (within : count ≤ report.steps.length) :
    Report input budget (events.take count) := Run.cut report count within

end Netlib.Check.CampusRevocationModel
