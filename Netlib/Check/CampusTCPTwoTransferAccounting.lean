import Netlib.Check.CampusTCPTwoTransferMonitor
import Netlib.Check.CampusTCPTwoExchangeAccounting

/-!
# Global counters across the actual transfer

Control slots retain both local loss logs and the timeout count.
Healthy folds count the same stored drops, timeout outputs, and slots.
-/

namespace Netlib.Check.CampusTCPTwoTransferAccounting

open CampusTCPModel (Input Step)
open CampusTCPTwoTransferMonitor
open CampusTCPTwoProgressLossHistory (dropID)
open CampusTCPTwoExchangeLoss (isTimeoutOutput)

local notation "Config" => CampusTCPTwoTransferMonitor.Config

variable {input : Input}

theorem observe_invalid (config : Config) (monitor : Monitor) (actual : Step input)
    (invalid : monitor.mode = .invalid) : observe config monitor actual = monitor := by
  have rejected : allowed config actual.before monitor actual.event = false := by simp [allowed, invalid]
  simp only [observe, rejected, Bool.and_false, Bool.false_eq_true, ite_false, Monitor.invalid]
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

private theorem control_quiet (config : Config) (control : Control) (actual : Step input)
    (served : control.serves config actual.event = true) :
    dropID actual = none ∧ isTimeoutOutput actual = false := by
  cases control <;> cases event : actual.event <;>
    simp_all [Control.serves, dropID, isTimeoutOutput]

private theorem ordinary_counters (config : Config) (monitor : Monitor) (actual : Step input)
    (healthy : (ordinary config monitor actual).mode ≠ .invalid) :
    (ordinary config monitor actual).exchange.drops = monitor.exchange.drops ++ (dropID actual).toList ∧
      (ordinary config monitor actual).exchange.timeouts = monitor.exchange.timeouts + (if isTimeoutOutput actual then 1 else 0) ∧
      (ordinary config monitor actual).exchange.slots = monitor.exchange.slots + 1 := by
  dsimp only [ordinary] at healthy ⊢
  split at healthy
  · exact False.elim (healthy rfl)
  · rename_i valid
    have next : (CampusTCPTwoExchangeMonitor.observe (config.at actual.before) monitor.exchange actual).mode ≠ .invalid := by
      intro invalid
      simp only [invalid, decide_true, not_true_eq_false] at valid
    rw [ite_eq_right valid]
    exact CampusTCPTwoExchangeAccounting.observe_counters (config.at actual.before) monitor.exchange actual next

private theorem drain_quiet (ticket : Nat) (actual : Step input)
    (served : drainServes ticket actual.event = true) :
    dropID actual = none ∧ isTimeoutOutput actual = false := by
  cases event : actual.event <;> simp_all [drainServes, dropID, isTimeoutOutput]

private theorem drain_counters (config : Config) (monitor : Monitor) (actual : Step input) (ticket : Nat)
    (healthy : (observeDrain config monitor actual ticket).mode ≠ .invalid) :
    (observeDrain config monitor actual ticket).exchange.drops = monitor.exchange.drops ∧
      (observeDrain config monitor actual ticket).exchange.timeouts = monitor.exchange.timeouts ∧
      (observeDrain config monitor actual ticket).exchange.slots = monitor.exchange.slots + 1 := by
  cases present : actual.result.service <;> simp only [observeDrain, present] at healthy ⊢
  · exact False.elim (healthy rfl)
  · repeat' first
      | (solve | exact False.elim (healthy rfl))
      | (split at healthy)
    all_goals simp_all
    all_goals repeat' (split <;> simp_all)

theorem observe_counters (config : Config) (monitor : Monitor) (actual : Step input)
    (healthy : (observe config monitor actual).mode ≠ .invalid) :
    (observe config monitor actual).exchange.drops = monitor.exchange.drops ++ (dropID actual).toList ∧
      (observe config monitor actual).exchange.timeouts = monitor.exchange.timeouts + (if isTimeoutOutput actual then 1 else 0) ∧
      (observe config monitor actual).exchange.slots = monitor.exchange.slots + 1 := by
  obtain ⟨valid, supported, passed, checked⟩ := observe_checked config monitor actual healthy
  change allowed config actual.before monitor actual.event = true at checked
  have guard : (actual.result.supported && actual.result.passed && allowed config actual.before monitor actual.event) = true := by
    simp only [supported, passed, checked, Bool.and_self]
  rw [observe, ite_eq_left guard] at healthy ⊢
  cases drain : drainTicket actual.before monitor with
  | some ticket =>
    simp only [drain] at healthy ⊢
    cases event : actual.event <;> simp only [event] at healthy ⊢
    all_goals first
      | exact ordinary_counters config monitor actual healthy
      | (
        have served : drainServes ticket actual.event = true := by
          simpa [allowed, valid, drain, event] using checked
        obtain ⟨drop, timeout⟩ := drain_quiet ticket actual served
        simpa only [drop, timeout, Option.toList_none, List.append_nil, Bool.false_eq_true,
          ite_false, Nat.add_zero] using drain_counters config monitor actual ticket healthy)
  | none =>
    simp only [drain] at healthy ⊢
    cases selected : controlDemand monitor with
    | none =>
      simp only [selected] at healthy ⊢
      exact ordinary_counters config monitor actual healthy
    | some control =>
      simp only [selected] at healthy ⊢
      cases event : actual.event <;> simp only [event] at healthy ⊢
      all_goals first
        | exact ordinary_counters config monitor actual healthy
        | (
          have served : control.serves config actual.event = true := by
            simpa [allowed, valid, drain, selected, event] using checked
          obtain ⟨drop, timeout⟩ := control_quiet config control actual served
          simp [drop, timeout])

theorem fold_accounting (config : Config) (monitor : Monitor) (steps : List (Step input))
    (healthy : (steps.foldl (observe config) monitor).mode ≠ .invalid) :
    (steps.foldl (observe config) monitor).exchange.drops = monitor.exchange.drops ++ steps.filterMap dropID ∧
      (steps.foldl (observe config) monitor).exchange.timeouts = monitor.exchange.timeouts + (steps.filter isTimeoutOutput).length ∧
      (steps.foldl (observe config) monitor).exchange.slots = monitor.exchange.slots + steps.length := by
  induction steps generalizing monitor with
  | nil => simp
  | cons actual rest ih =>
    have nextHealthy := fold_healthy config (observe config monitor actual) rest healthy
    have counters := observe_counters config monitor actual nextHealthy
    have tail := ih (observe config monitor actual) healthy
    refine ⟨?_, ?_, ?_⟩
    · calc
        ((actual :: rest).foldl (observe config) monitor).exchange.drops =
            (observe config monitor actual).exchange.drops ++ rest.filterMap dropID := tail.1
        _ = (monitor.exchange.drops ++ (dropID actual).toList) ++ rest.filterMap dropID := by rw [counters.1]
        _ = monitor.exchange.drops ++ (actual :: rest).filterMap dropID := by
          cases selected : dropID actual <;> simp [selected, List.append_assoc]
    · calc
        ((actual :: rest).foldl (observe config) monitor).exchange.timeouts =
            (observe config monitor actual).exchange.timeouts + (rest.filter isTimeoutOutput).length := tail.2.1
        _ = monitor.exchange.timeouts + (if isTimeoutOutput actual then 1 else 0) + (rest.filter isTimeoutOutput).length := by rw [counters.2.1]
        _ = monitor.exchange.timeouts + ((actual :: rest).filter isTimeoutOutput).length := by
          cases selected : isTimeoutOutput actual <;> simp [selected] <;> omega
    · calc
        ((actual :: rest).foldl (observe config) monitor).exchange.slots =
            (observe config monitor actual).exchange.slots + rest.length := tail.2.2
        _ = monitor.exchange.slots + (actual :: rest).length := by rw [counters.2.2, List.length_cons]; omega

theorem initial_accounting (config : Config) (steps : List (Step input))
    (healthy : (steps.foldl (observe config) .initial).mode ≠ .invalid) :
    (steps.foldl (observe config) .initial).exchange.drops = steps.filterMap dropID ∧
      (steps.foldl (observe config) .initial).exchange.timeouts = (steps.filter isTimeoutOutput).length ∧
      (steps.foldl (observe config) .initial).exchange.slots = steps.length := by
  simpa only [Monitor.initial, CampusTCPTwoExchangeMonitor.Monitor.initial, List.nil_append, Nat.zero_add] using
    fold_accounting config .initial steps healthy

end Netlib.Check.CampusTCPTwoTransferAccounting
