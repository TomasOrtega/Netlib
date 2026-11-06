import Netlib.Check.CampusTCPSchedule

/-!
# Exact slices of stored campus steps

Slices retain the actual states and operations.
Unevaluated events after a stopped trace add no stored slots.
-/

namespace Netlib.Check.CampusTCPTraceSlices

open CampusTCPModel

namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

variable {input : Input} {initial final : State input}
variable {events remaining : List Event} {steps : List (Step input)}

def slice (steps : List (Step input)) (start count : Nat) : List (Step input) :=
  (steps.drop start).take count

theorem slice_length (steps : List (Step input)) (within : start + count ≤ steps.length) :
    (slice steps start count).length = count := by
  simp only [slice, List.length_take, List.length_drop]
  exact Nat.min_eq_left (by omega)

theorem stateAt_drop (initial : State input) (steps : List (Step input)) (start slot : Nat) :
    S.stateAt (S.stateAt initial steps start) (steps.drop start) slot = S.stateAt initial steps (start + slot) := by
  induction steps generalizing initial start with
  | nil => simp only [List.drop_nil, S.stateAt]
  | cons head rest ih =>
    cases start with
    | zero => simp only [List.drop_zero, CampusTCPSchedule.stateAt_zero, Nat.zero_add]
    | succ start =>
      simpa only [List.drop_succ_cons, S.stateAt, Nat.succ_add] using ih head.result.state start

theorem stateAt_take (initial : State input) (steps : List (Step input)) (inside : slot ≤ count) :
    S.stateAt initial (steps.take count) slot = S.stateAt initial steps slot := by
  induction steps generalizing initial slot count with
  | nil => simp only [List.take_nil, S.stateAt]
  | cons head rest ih =>
    cases count with
    | zero =>
      have zero : slot = 0 := by omega
      subst slot
      rfl
    | succ count =>
      cases slot with
      | zero => rfl
      | succ slot => exact ih head.result.state (by omega)

theorem stateAt_slice (initial : State input) (steps : List (Step input)) (inside : slot ≤ count) :
    S.stateAt (S.stateAt initial steps start) (slice steps start count) slot = S.stateAt initial steps (start + slot) := by
  rw [slice, stateAt_take _ _ inside, stateAt_drop]

theorem getElem?_slice (steps : List (Step input)) (inside : slot < count) :
    (slice steps start count)[slot]? = steps[start + slot]? := by
  rw [slice, List.getElem?_take_of_lt inside, List.getElem?_drop]

theorem eventAt_drop (steps : List (Step input)) (start slot : Nat) :
    S.eventAt (steps.drop start) slot = S.eventAt steps (start + slot) := by
  simp only [S.eventAt, List.getElem?_drop]

theorem eventAt_slice (steps : List (Step input)) (inside : slot < count) :
    S.eventAt (slice steps start count) slot = S.eventAt steps (start + slot) := by
  unfold S.eventAt
  rw [getElem?_slice _ inside]

theorem Trace.take (trace : Trace input initial events steps final remaining) (within : count ≤ steps.length) :
    Trace input initial ((steps.take count).map (·.event)) (steps.take count) (S.stateAt initial steps count) [] :=
  CampusTCPSchedule.Trace.take trace count within

theorem Trace.drop (trace : Trace input initial events steps final remaining) (within : start ≤ steps.length) :
    Trace input (S.stateAt initial steps start) ((steps.drop start).map (·.event)) (steps.drop start) final [] := by
  induction trace generalizing start with
  | done state =>
    have zero : start = 0 := by simp only [List.length_nil] at within; omega
    subst start
    exact .done state
  | stop head blocked tail =>
    cases start with
    | zero => exact .stop head blocked []
    | succ start =>
      have zero : start = 0 := by simp only [List.length_cons, List.length_nil] at within; omega
      subst start
      exact .done head.result.state
  | next head accepted rest ih =>
    cases start with
    | zero =>
      exact .next head accepted (by
        simpa only [List.drop_zero, CampusTCPSchedule.stateAt_zero] using ih (start := 0) (Nat.zero_le _))
    | succ start =>
      simpa only [List.drop_succ_cons, S.stateAt] using ih (start := start) (Nat.le_of_succ_le_succ within)

theorem Trace.slice (trace : Trace input initial events steps final remaining) (within : start + count ≤ steps.length) :
    Trace input (S.stateAt initial steps start) ((slice steps start count).map (·.event)) (slice steps start count)
      (S.stateAt initial steps (start + count)) [] := by
  have tail := Trace.drop trace (by omega : start ≤ steps.length)
  have length : count ≤ (steps.drop start).length := by rw [List.length_drop]; omega
  have selected := CampusTCPSchedule.Trace.take tail count length
  simpa only [CampusTCPTraceSlices.slice, stateAt_drop] using selected

end Netlib.Check.CampusTCPTraceSlices
