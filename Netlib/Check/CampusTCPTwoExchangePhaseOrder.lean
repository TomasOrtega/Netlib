import Netlib.Check.CampusTCPTwoExchangeAccounting
import Netlib.Check.CampusTCPTwoExchangeProjection

/-!
# Healthy phase order on the actual exchange trace

The current selector can only stay in its phase or enter the next phase.
Once done, every later healthy stored prefix stays done.
-/

namespace Netlib.Check.CampusTCPTwoExchangePhaseOrder

open CampusTCPModel
open CampusTCPTwoExchangeMonitor

local notation "Config" => CampusTCPTwoExchangeMonitor.Config

variable {input : Input} {config : Config} {monitor : Monitor}

def Follows : Mode → Mode → Prop
  | .forward, after => after = .forward ∨ after = .needWrite
  | .needWrite, after => after = .needWrite ∨ after = .reverse
  | .reverse, after => after = .reverse ∨ after = .done
  | .done, after => after = .done
  | .invalid, _ => False

theorem observe_phase (actual : Step input) (healthy : (observe config monitor actual).mode ≠ .invalid) :
    Follows monitor.mode (observe config monitor actual).mode := by
  obtain ⟨_, supported, passed, checked⟩ := CampusTCPTwoExchangeAccounting.observe_checked config monitor actual healthy
  change allowed config actual.before monitor actual.event = true at checked
  have guard : (actual.result.supported && actual.result.passed && allowed config actual.before monitor actual.event) = true := by
    simp only [supported, passed, checked, Bool.and_self]
  rw [CampusTCPTwoExchangeMonitor.observe, ite_eq_left guard] at healthy ⊢
  cases mode : monitor.mode <;> simp only [mode, Follows] at healthy ⊢
  case forward =>
    split at healthy
    · exact False.elim (healthy rfl)
    · rename_i valid
      rw [ite_eq_right valid]
      split
      · exact Or.inr rfl
      · exact Or.inl mode
  case needWrite =>
    cases event : actual.event <;> simp only [event] at healthy ⊢
    all_goals first
      | exact False.elim (healthy rfl)
      | exact Or.inl mode
      | exact Or.inr trivial
  case reverse =>
    split at healthy
    · exact False.elim (healthy rfl)
    · rename_i valid
      rw [ite_eq_right valid]
      split
      · exact Or.inr rfl
      · exact Or.inl mode
  case done => exact mode
  case invalid => exact False.elim (healthy rfl)

theorem observe_done (mode : monitor.mode = .done) (actual : Step input)
    (healthy : (observe config monitor actual).mode ≠ .invalid) : (observe config monitor actual).mode = .done := by
  have next := observe_phase actual healthy
  simpa only [mode, Follows] using next

variable {initial final : State input} {events remaining : List Event} {steps : List (Step input)}
variable {phase : Mode} {slot first last : Nat}

theorem first_exit_next (trace : Trace input initial events steps final remaining) (start : monitor.mode = phase)
    (within : slot ≤ steps.length) (exited : (monitorAt config monitor steps slot).mode ≠ phase)
    (prior : ∀ index, index < slot → (monitorAt config monitor steps index).mode = phase)
    (healthy : (monitorAt config monitor steps slot).mode ≠ .invalid) :
    0 < slot ∧ Follows phase (monitorAt config monitor steps slot).mode := by
  cases slot with
  | zero =>
    rw [monitorAt_zero] at exited
    exact False.elim (exited start)
  | succ slot =>
    obtain ⟨actual, found, _, _, _⟩ := CampusTCPSchedule.Trace.at trace slot (by omega)
    have next := observe_phase actual (by
      rw [← monitorAt_next config monitor steps found]
      exact healthy)
    rw [prior slot (by omega), ← monitorAt_next config monitor steps found] at next
    exact ⟨by omega, next⟩

theorem forward_first_exit (trace : Trace input initial events steps final remaining) (start : monitor.mode = .forward)
    (within : slot ≤ steps.length) (exited : (monitorAt config monitor steps slot).mode ≠ .forward)
    (prior : ∀ index, index < slot → (monitorAt config monitor steps index).mode = .forward)
    (healthy : (monitorAt config monitor steps slot).mode ≠ .invalid) :
    0 < slot ∧ (monitorAt config monitor steps slot).mode = .needWrite := by
  obtain ⟨positive, next⟩ := first_exit_next trace start within exited prior healthy
  exact ⟨positive, next.resolve_left exited⟩

theorem write_first_exit (trace : Trace input initial events steps final remaining) (start : monitor.mode = .needWrite)
    (within : slot ≤ steps.length) (exited : (monitorAt config monitor steps slot).mode ≠ .needWrite)
    (prior : ∀ index, index < slot → (monitorAt config monitor steps index).mode = .needWrite)
    (healthy : (monitorAt config monitor steps slot).mode ≠ .invalid) :
    0 < slot ∧ (monitorAt config monitor steps slot).mode = .reverse := by
  obtain ⟨positive, next⟩ := first_exit_next trace start within exited prior healthy
  exact ⟨positive, next.resolve_left exited⟩

theorem reverse_first_exit (trace : Trace input initial events steps final remaining) (start : monitor.mode = .reverse)
    (within : slot ≤ steps.length) (exited : (monitorAt config monitor steps slot).mode ≠ .reverse)
    (prior : ∀ index, index < slot → (monitorAt config monitor steps index).mode = .reverse)
    (healthy : (monitorAt config monitor steps slot).mode ≠ .invalid) :
    0 < slot ∧ (monitorAt config monitor steps slot).mode = .done := by
  obtain ⟨positive, next⟩ := first_exit_next trace start within exited prior healthy
  exact ⟨positive, next.resolve_left exited⟩

theorem fold_from (config : Config) (monitor : Monitor) (steps : List (Step input)) (slot : Nat) :
    (steps.drop slot).foldl (observe config) (monitorAt config monitor steps slot) = steps.foldl (observe config) monitor := by
  induction steps generalizing monitor slot with
  | nil => simp only [List.drop_nil, List.foldl_nil, monitorAt]
  | cons actual rest ih =>
    cases slot with
    | zero => simp only [List.drop_zero, monitorAt_zero]
    | succ slot => simpa only [List.drop_succ_cons, List.foldl_cons, monitorAt] using ih (observe config monitor actual) slot

theorem monitorAt_healthy (healthy : (steps.foldl (observe config) monitor).mode ≠ .invalid) (slot : Nat) :
    (monitorAt config monitor steps slot).mode ≠ .invalid := by
  apply CampusTCPTwoExchangeAccounting.fold_healthy config _ (steps.drop slot)
  rw [fold_from]
  exact healthy

theorem monitorAt_healthy_before (within : last ≤ steps.length) (before : first ≤ last)
    (healthy : (monitorAt config monitor steps last).mode ≠ .invalid) :
    (monitorAt config monitor steps first).mode ≠ .invalid := by
  have length : (steps.take last).length = last := by rw [List.length_take, Nat.min_eq_left within]
  have folded : ((steps.take last).foldl (observe config) monitor).mode ≠ .invalid := by
    rw [← monitorAt_length, length, CampusTCPTwoExchangeProjection.exchange_monitorAt_take _ _ _ (Nat.le_refl _)]
    exact healthy
  have current := monitorAt_healthy folded first
  rw [CampusTCPTwoExchangeProjection.exchange_monitorAt_take _ _ _ before] at current
  exact current

theorem done_persistent (trace : Trace input initial events steps final remaining) (ordered : first ≤ last)
    (within : last ≤ steps.length) (done : (monitorAt config monitor steps first).mode = .done)
    (healthy : (monitorAt config monitor steps last).mode ≠ .invalid) :
    (monitorAt config monitor steps last).mode = .done := by
  have onward : ∀ offset, first + offset ≤ last → (monitorAt config monitor steps (first + offset)).mode = .done := by
    intro offset
    induction offset with
    | zero => intro _; simpa only [Nat.add_zero] using done
    | succ offset ih =>
      intro current
      obtain ⟨actual, found, _, _, _⟩ := CampusTCPSchedule.Trace.at trace (first + offset) (by omega)
      have next := observe_done (ih (by omega)) actual (by
        rw [← monitorAt_next config monitor steps found]
        exact monitorAt_healthy_before within (by omega) healthy)
      simpa only [Nat.add_succ, monitorAt_next config monitor steps found] using next
  have current := onward (last - first) (by omega)
  simpa only [Nat.add_sub_of_le ordered] using current

theorem done_persistent_of_fold_healthy (trace : Trace input initial events steps final remaining)
    (ordered : first ≤ last) (within : last ≤ steps.length) (done : (monitorAt config monitor steps first).mode = .done)
    (healthy : (steps.foldl (observe config) monitor).mode ≠ .invalid) :
    (monitorAt config monitor steps last).mode = .done :=
  done_persistent trace ordered within done (monitorAt_healthy healthy last)

end Netlib.Check.CampusTCPTwoExchangePhaseOrder
