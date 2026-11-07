import Netlib.Check.CampusRevocationControl
import Netlib.Check.CampusRevocationRank
import Netlib.Check.CampusRevocationTrace

/-!
# Completion search over recorded campus states

The search accepts an actual early completion cut.
It never requires an unrecorded state beyond the finite trace.
-/

namespace Netlib.Check.CampusRevocationControl

open CampusRevocationModel CampusRevocationTargets

def deadline (report : Report input budget events) (cut bound : Nat) : Nat :=
  cut + slots (stateAt input.initial report.steps cut).queue.pending.length bound

def completed (targets : Targets input after) (state : State) : Bool :=
  ready targets state && state.queue.pending.isEmpty

theorem completed_correct (targets : Targets input after) (state : State) :
    completed targets state = true ↔ ready targets state = true ∧ state.queue.pending = [] := by
  simp only [completed, Bool.and_eq_true, List.isEmpty_iff]

def findCompletion (report : Report input budget events) (cut : Nat)
    (targets : Targets input after) (bound : Nat) : Option Nat :=
  (List.range (min (deadline report cut bound) report.steps.length + 1)).find? fun slot =>
    decide (cut ≤ slot) && completed targets (stateAt input.initial report.steps slot)

theorem findCompletion_facts (report : Report input budget events) (cut : Nat)
    (targets : Targets input after) (bound completion : Nat)
    (found : findCompletion report cut targets bound = some completion) :
    cut ≤ completion ∧ completion ≤ deadline report cut bound ∧ completion ≤ report.steps.length ∧
      ready targets (stateAt input.initial report.steps completion) = true ∧
      (stateAt input.initial report.steps completion).queue.pending = [] := by
  have member := List.mem_of_find?_eq_some found
  have within : completion < min (deadline report cut bound) report.steps.length + 1 := List.mem_range.mp member
  have upper : completion ≤ min (deadline report cut bound) report.steps.length := by omega
  have selected : cut ≤ completion ∧ completed targets (stateAt input.initial report.steps completion) = true := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using List.find?_some found
  exact ⟨selected.1, Nat.le_trans upper (Nat.min_le_left _ _),
    Nat.le_trans upper (Nat.min_le_right _ _), (completed_correct _ _).mp selected.2⟩

theorem findCompletion_exists (report : Report input budget events) (cut : Nat)
    (targets : Targets input after) (bound slot : Nat)
    (afterCut : cut ≤ slot) (beforeDeadline : slot ≤ deadline report cut bound)
    (recorded : slot ≤ report.steps.length)
    (installed : ready targets (stateAt input.initial report.steps slot) = true)
    (empty : (stateAt input.initial report.steps slot).queue.pending = []) :
    ∃ completion, findCompletion report cut targets bound = some completion := by
  cases found : findCompletion report cut targets bound with
  | some completion => exact ⟨completion, rfl⟩
  | none =>
    have absent := List.find?_eq_none.mp found
    have member : slot ∈ List.range (min (deadline report cut bound) report.steps.length + 1) :=
      List.mem_range.mpr (by omega)
    have selected : (decide (cut ≤ slot) && completed targets (stateAt input.initial report.steps slot)) = true := by
      simp [afterCut, completed, installed, empty]
    exact False.elim (absent slot member selected)

end Netlib.Check.CampusRevocationControl
