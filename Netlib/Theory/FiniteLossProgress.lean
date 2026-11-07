import Netlib.Theory.BoundedServiceRestriction

/-!
# Completion under a finite loss allowance

Each extension either retains an earlier completion or has no additional loss.
-/

namespace Netlib.Theory.FiniteLossProgress

def horizon (base : Nat) (extension : Nat → Nat) : Nat → Nat
  | 0 => base
  | count + 1 => horizon base extension count + extension (horizon base extension count)

theorem base_le_horizon (base : Nat) (extension : Nat → Nat) (count : Nat) :
    base ≤ horizon base extension count := by
  induction count with
  | zero => exact Nat.le_refl _
  | succ count ih => exact Nat.le_trans ih (Nat.le_add_right _ _)

theorem completion (base length : Nat) (extension losses : Nat → Nat) (closed : Nat → Prop)
    (lossMonotone : ∀ first last, first ≤ last → last ≤ length → losses first ≤ losses last)
    (closedMonotone : ∀ first last, first ≤ last → last ≤ length → closed first → closed last)
    (zeroLoss : base ≤ length → losses base = 0 → closed base)
    (afterBase : ∀ start, base ≤ start → start + extension start ≤ length →
      losses (start + extension start) = losses start → closed (start + extension start)) :
    ∀ allowance, horizon base extension allowance ≤ length → losses (horizon base extension allowance) ≤ allowance →
      closed (horizon base extension allowance) := by
  intro allowance
  induction allowance with
  | zero =>
    intro within bound
    exact zeroLoss within (Nat.eq_zero_of_le_zero bound)
  | succ allowance ih =>
    intro within bound
    change horizon base extension allowance + extension (horizon base extension allowance) ≤ length at within
    change losses (horizon base extension allowance + extension (horizon base extension allowance)) ≤ allowance + 1 at bound
    have order : horizon base extension allowance ≤
        horizon base extension allowance + extension (horizon base extension allowance) := Nat.le_add_right _ _
    have priorWithin := Nat.le_trans order within
    by_cases earlier : losses (horizon base extension allowance) ≤ allowance
    · exact closedMonotone _ _ order within (ih priorWithin earlier)
    · have counted := lossMonotone _ _ order within
      apply afterBase _ (base_le_horizon base extension allowance) within
      omega

theorem completion_of_total (base length allowance : Nat) (extension losses : Nat → Nat) (closed : Nat → Prop)
    (lossMonotone : ∀ first last, first ≤ last → last ≤ length → losses first ≤ losses last)
    (closedMonotone : ∀ first last, first ≤ last → last ≤ length → closed first → closed last)
    (zeroLoss : base ≤ length → losses base = 0 → closed base)
    (afterBase : ∀ start, base ≤ start → start + extension start ≤ length →
      losses (start + extension start) = losses start → closed (start + extension start))
    (within : horizon base extension allowance ≤ length) (total : losses length ≤ allowance) :
    closed (horizon base extension allowance) := by
  apply completion base length extension losses closed lossMonotone closedMonotone zeroLoss afterBase allowance within
  exact Nat.le_trans (lossMonotone _ _ within (Nat.le_refl _)) total

end Netlib.Theory.FiniteLossProgress
