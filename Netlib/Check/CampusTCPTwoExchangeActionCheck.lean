import Netlib.Check.CampusTCPTwoExchangeMonitor

/-!
# One-pass whole-exchange action checks

The stored step results supply each next state.
The check equals the original slot-based check for every input list.
-/

namespace Netlib.Check.CampusTCPTwoExchangeActionCheck

open CampusTCPModel

namespace M
export CampusTCPTwoExchangeMonitor (Config Monitor observe monitorAt Allowed allowed)
end M
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

variable {input : Input}

def actions (config : M.Config) (initial : State input) (monitor : M.Monitor) : List (Step input) → Bool
  | [] => true
  | actual :: rest =>
    if M.allowed config initial monitor actual.event then
      actions config actual.result.state (M.observe config monitor actual) rest
    else false

theorem actions_cons (config : M.Config) (initial : State input) (monitor : M.Monitor)
    (actual : Step input) (rest : List (Step input)) :
    actions config initial monitor (actual :: rest) = (M.allowed config initial monitor actual.event &&
      actions config actual.result.state (M.observe config monitor actual) rest) := by
  cases checked : M.allowed config initial monitor actual.event <;> simp only [actions, checked,
    Bool.false_eq_true, ite_false, ite_true, Bool.false_and, Bool.true_and]

theorem actions_correct (config : M.Config) (initial : State input) (monitor : M.Monitor) (steps : List (Step input)) :
    actions config initial monitor steps = true ↔
      ∀ slot, slot < steps.length → M.Allowed config (S.stateAt initial steps slot)
        (M.monitorAt config monitor steps slot) (S.eventAt steps slot) := by
  induction steps generalizing initial monitor with
  | nil =>
    constructor
    · intro _ slot inside
      cases Nat.not_lt_zero slot inside
    · intro _
      rfl
  | cons actual rest ih =>
    rw [actions_cons]
    simp only [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨first, later⟩ slot inside
      cases slot with
      | zero => exact first
      | succ slot => exact later slot (Nat.lt_of_succ_lt_succ inside)
    · intro checked
      refine ⟨checked 0 (Nat.zero_lt_succ _), ?_⟩
      intro slot inside
      exact checked (slot + 1) (Nat.succ_lt_succ inside)

theorem actions_eq (config : M.Config) (initial : State input) (monitor : M.Monitor) (steps : List (Step input)) :
    actions config initial monitor steps = CampusTCPTwoExchangeMonitor.actions config initial monitor steps := by
  apply Bool.eq_iff_iff.mpr
  exact (actions_correct config initial monitor steps).trans
    (CampusTCPTwoExchangeMonitor.actions_correct config initial monitor steps).symm

end Netlib.Check.CampusTCPTwoExchangeActionCheck
