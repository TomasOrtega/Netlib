import Netlib.Check.CampusTCPRecoveryRoundMonitor

/-!
# Service bounds on stored round schedules

The check examines the demands and actions in evaluated slots.
It does not assume that a packet operation succeeds.
-/

namespace Netlib.Check.CampusTCPRecoveryRoundServiceBound

open CampusTCPModel
namespace R
export CampusTCPRecoveryRoundMonitor (Config Monitor Demand nextDemand monitorAt serves allowed)
end R
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

variable {input : Input}

def pendingAt (config : R.Config) (initial : State input) (monitor : R.Monitor)
    (steps : List (Step input)) (slot : Nat) : Option R.Demand :=
  R.nextDemand config (S.stateAt initial steps slot) (R.monitorAt config monitor steps slot)

def Serviced (config : R.Config) (initial : State input) (monitor : R.Monitor)
    (steps : List (Step input)) (bound : Nat) : Prop :=
  ∀ start, start + bound ≤ steps.length → ∀ demand,
    pendingAt config initial monitor steps start = some demand →
    (∀ offset, offset < bound → pendingAt config initial monitor steps (start + offset) = some demand) →
    ∃ offset, offset < bound ∧ R.serves demand (S.eventAt steps (start + offset)) = true

def check (config : R.Config) (initial : State input) (monitor : R.Monitor)
    (steps : List (Step input)) (bound : Nat) : Bool :=
  (List.range (steps.length + 1)).all fun start =>
    if start + bound ≤ steps.length then
      match pendingAt config initial monitor steps start with
      | none => true
      | some demand =>
        if (List.range bound).all (fun offset => decide (pendingAt config initial monitor steps (start + offset) = some demand)) then
          (List.range bound).any (fun offset => R.serves demand (S.eventAt steps (start + offset)))
        else true
    else true

theorem check_correct (config : R.Config) (initial : State input) (monitor : R.Monitor)
    (steps : List (Step input)) (bound : Nat) :
    check config initial monitor steps bound = true ↔ Serviced config initial monitor steps bound := by
  constructor
  · intro checked start within demand pending persistent
    have member : start ∈ List.range (steps.length + 1) := List.mem_range.mpr (by omega)
    have selected := List.all_eq_true.mp checked start member
    have retained : (List.range bound).all (fun offset => decide
        (pendingAt config initial monitor steps (start + offset) = some demand)) = true := by
      apply List.all_eq_true.mpr
      intro offset inside
      exact decide_eq_true (persistent offset (List.mem_range.mp inside))
    simp only [within, ↓reduceIte, pending, retained] at selected
    obtain ⟨offset, inside, action⟩ := List.any_eq_true.mp selected
    exact ⟨offset, List.mem_range.mp inside, action⟩
  · intro serviced
    apply List.all_eq_true.mpr
    intro start member
    by_cases within : start + bound ≤ steps.length
    · simp only [within, ↓reduceIte]
      cases pending : pendingAt config initial monitor steps start with
      | none => rfl
      | some demand =>
        simp only
        split
        · rename_i retained
          have persistent : ∀ offset, offset < bound →
              pendingAt config initial monitor steps (start + offset) = some demand := by
            intro offset inside
            exact of_decide_eq_true (List.all_eq_true.mp retained offset (List.mem_range.mpr inside))
          obtain ⟨offset, inside, action⟩ := serviced start within demand pending persistent
          exact List.any_eq_true.mpr ⟨offset, List.mem_range.mpr inside, action⟩
        · rfl
    · simp only [within, ↓reduceIte]


def actions (config : R.Config) (initial : State input) (monitor : R.Monitor) (steps : List (Step input)) : Bool :=
  (List.range steps.length).all fun slot => R.allowed config (S.stateAt initial steps slot)
    (R.monitorAt config monitor steps slot) (S.eventAt steps slot)

theorem actions_correct (config : R.Config) (initial : State input) (monitor : R.Monitor) (steps : List (Step input)) :
    actions config initial monitor steps = true ↔
      ∀ slot, slot < steps.length → CampusTCPRecoveryRoundMonitor.Allowed config (S.stateAt initial steps slot)
        (R.monitorAt config monitor steps slot) (S.eventAt steps slot) := by
  simp only [actions, List.all_eq_true, List.mem_range, CampusTCPRecoveryRoundMonitor.Allowed]

end Netlib.Check.CampusTCPRecoveryRoundServiceBound
