import Netlib.Check.CampusTCPTwoExchangeMonitor
import Netlib.Check.CampusTCPTwoExchangeLoss

/-!
# Whole-exchange counters from the recorded steps

A healthy final fold checks each preceding actual step.
The counters retain every selected drop and timeout in that fold.
-/

namespace Netlib.Check.CampusTCPTwoExchangeAccounting

open CampusTCPModel (Input Step)
open CampusTCPTwoExchangeMonitor
open CampusTCPTwoProgressLossHistory (dropID)
open CampusTCPTwoExchangeLoss (isTimeoutOutput)

local notation "Config" => CampusTCPTwoExchangeMonitor.Config

variable {input : Input}

theorem observe_invalid (config : Config) (monitor : Monitor) (actual : Step input)
    (invalid : monitor.mode = .invalid) : observe config monitor actual = monitor := by
  simp only [observe, allowed, invalid, Bool.and_false, Bool.false_eq_true, ite_false, Monitor.invalid]
  cases monitor
  cases invalid
  rfl

theorem observe_checked (config : Config) (monitor : Monitor) (actual : Step input)
    (healthy : (observe config monitor actual).mode ≠ .invalid) :
    monitor.mode ≠ .invalid ∧ actual.result.supported = true ∧ actual.result.passed = true ∧
      Allowed config actual.before monitor actual.event := by
  have before : monitor.mode ≠ .invalid := by
    intro invalid
    rw [observe_invalid config monitor actual invalid] at healthy
    exact healthy invalid
  refine ⟨before, ?_⟩
  unfold observe at healthy
  split at healthy
  · rename_i checked
    simp only [Bool.and_eq_true] at checked
    exact ⟨checked.1.1, checked.1.2, checked.2⟩
  · exact False.elim (healthy rfl)

theorem fold_invalid (config : Config) (monitor : Monitor) (steps : List (Step input))
    (invalid : monitor.mode = .invalid) : steps.foldl (observe config) monitor = monitor := by
  induction steps with
  | nil => rfl
  | cons actual rest ih =>
    rw [List.foldl_cons, observe_invalid config monitor actual invalid]
    exact ih

theorem fold_healthy (config : Config) (monitor : Monitor) (steps : List (Step input))
    (healthy : (steps.foldl (observe config) monitor).mode ≠ .invalid) : monitor.mode ≠ .invalid := by
  intro invalid
  rw [fold_invalid config monitor steps invalid] at healthy
  exact healthy invalid

private theorem recorded_counters (monitor : Monitor) (actual : Step input) :
    (match actual.event with | .dropPacket id => monitor.drops ++ [id] | _ => monitor.drops) =
        monitor.drops ++ (dropID actual).toList ∧
      (match actual.event with | .timeout _ true => monitor.timeouts + 1 | _ => monitor.timeouts) =
        monitor.timeouts + (if isTimeoutOutput actual then 1 else 0) ∧
      monitor.slots + 1 = monitor.slots + 1 := by
  cases event : actual.event <;> simp [dropID, isTimeoutOutput, event]
  case timeout actor policy => cases policy <;> simp

theorem observe_counters (config : Config) (monitor : Monitor) (actual : Step input)
    (healthy : (observe config monitor actual).mode ≠ .invalid) :
    (observe config monitor actual).drops = monitor.drops ++ (dropID actual).toList ∧
      (observe config monitor actual).timeouts = monitor.timeouts + (if isTimeoutOutput actual then 1 else 0) ∧
      (observe config monitor actual).slots = monitor.slots + 1 := by
  obtain ⟨_, supported, passed, checked⟩ := observe_checked config monitor actual healthy
  change allowed config actual.before monitor actual.event = true at checked
  have guard : (actual.result.supported && actual.result.passed && allowed config actual.before monitor actual.event) = true := by
    simp only [supported, passed, checked, Bool.and_self]
  rw [observe, ite_eq_left guard] at healthy ⊢
  cases mode : monitor.mode <;> simp only [mode] at healthy ⊢
  case forward =>
    split at healthy
    · exact False.elim (healthy rfl)
    · rename_i valid
      rw [ite_eq_right valid]
      split <;> exact recorded_counters monitor actual
  case needWrite =>
    cases event : actual.event <;> simp only [event] at healthy ⊢
    all_goals first
      | exact False.elim (healthy rfl)
      | exact recorded_counters monitor actual
  case reverse =>
    split at healthy
    · exact False.elim (healthy rfl)
    · rename_i valid
      rw [ite_eq_right valid]
      split <;> exact recorded_counters monitor actual
  case done => exact recorded_counters monitor actual
  case invalid => exact False.elim (healthy rfl)

theorem fold_passed (config : Config) (monitor : Monitor) (steps : List (Step input))
    (healthy : (steps.foldl (observe config) monitor).mode ≠ .invalid) :
    monitor.mode ≠ .invalid ∧ ∀ actual ∈ steps, actual.result.supported = true ∧ actual.result.passed = true := by
  induction steps generalizing monitor with
  | nil => exact ⟨healthy, by simp⟩
  | cons actual rest ih =>
    obtain ⟨next, tail⟩ := ih (observe config monitor actual) healthy
    obtain ⟨before, supported, passed, _⟩ := observe_checked config monitor actual next
    refine ⟨before, ?_⟩
    intro chosen member
    rcases List.mem_cons.mp member with same | later
    · subst chosen
      exact ⟨supported, passed⟩
    · exact tail chosen later

theorem fold_accounting (config : Config) (monitor : Monitor) (steps : List (Step input))
    (healthy : (steps.foldl (observe config) monitor).mode ≠ .invalid) :
    (steps.foldl (observe config) monitor).drops = monitor.drops ++ steps.filterMap dropID ∧
      (steps.foldl (observe config) monitor).timeouts = monitor.timeouts + (steps.filter isTimeoutOutput).length ∧
      (steps.foldl (observe config) monitor).slots = monitor.slots + steps.length := by
  induction steps generalizing monitor with
  | nil => simp
  | cons actual rest ih =>
    have nextHealthy := fold_healthy config (observe config monitor actual) rest healthy
    have counters := observe_counters config monitor actual nextHealthy
    have tail := ih (observe config monitor actual) healthy
    refine ⟨?_, ?_, ?_⟩
    · calc
        ((actual :: rest).foldl (observe config) monitor).drops =
            (observe config monitor actual).drops ++ rest.filterMap dropID := tail.1
        _ = (monitor.drops ++ (dropID actual).toList) ++ rest.filterMap dropID := by rw [counters.1]
        _ = monitor.drops ++ (actual :: rest).filterMap dropID := by
          cases selected : dropID actual <;> simp [selected, List.append_assoc]
    · calc
        ((actual :: rest).foldl (observe config) monitor).timeouts =
            (observe config monitor actual).timeouts + (rest.filter isTimeoutOutput).length := tail.2.1
        _ = monitor.timeouts + (if isTimeoutOutput actual then 1 else 0) + (rest.filter isTimeoutOutput).length := by rw [counters.2.1]
        _ = monitor.timeouts + ((actual :: rest).filter isTimeoutOutput).length := by
          cases selected : isTimeoutOutput actual <;> simp [selected] <;> omega
    · calc
        ((actual :: rest).foldl (observe config) monitor).slots = (observe config monitor actual).slots + rest.length := tail.2.2
        _ = monitor.slots + (actual :: rest).length := by rw [counters.2.2, List.length_cons]; omega

theorem initial_accounting (config : Config) (steps : List (Step input))
    (healthy : (steps.foldl (observe config) .initial).mode ≠ .invalid) :
    (steps.foldl (observe config) .initial).drops = steps.filterMap dropID ∧
      (steps.foldl (observe config) .initial).timeouts = (steps.filter isTimeoutOutput).length ∧
      (steps.foldl (observe config) .initial).slots = steps.length := by
  simpa only [Monitor.initial, List.nil_append, Nat.zero_add] using fold_accounting config .initial steps healthy

end Netlib.Check.CampusTCPTwoExchangeAccounting
