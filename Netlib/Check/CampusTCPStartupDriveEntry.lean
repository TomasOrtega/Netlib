import Netlib.Check.CampusTCPStartupOpening

/-!
# The first actual startup drive cut

A failed preparation or OPEN check makes the next startup action invalid.
The next stored slot and one whole Actions check exclude that failure.
-/

namespace Netlib.Check.CampusTCPStartupDriveEntry

open CampusTCPModel

namespace E
export CampusTCPStartupTransferExecution (initial monitorAt actions actions_correct observe)
end E
namespace P
export CampusTCPStartupMonitor (Monitor initial observe allowed)
end P
namespace O
export CampusTCPStartupOpening (earlyMode)
end O

variable {input : Input} {events : List Event} {whole : Report input events}
variable {config : CampusTCPStartupTransferMonitor.Config} {slot : Nat}

private theorem initial_mode (config : CampusTCPStartupTransferMonitor.Config) :
    (P.initial config).mode = O.earlyMode config 0 := by
  cases preparation : config.startup.preparation with
  | nil => simp only [P.initial, preparation, List.isEmpty_nil, ↓reduceIte, O.earlyMode,
      List.length_nil, Nat.lt_irrefl, ↓reduceIte]
  | cons head rest => simp only [P.initial, preparation, List.isEmpty_cons, Bool.false_eq_true,
      ↓reduceIte, O.earlyMode, List.length_cons, Nat.zero_lt_succ, ↓reduceIte]

private theorem early_not_data : O.earlyMode config slot ≠ .data := by
  unfold O.earlyMode
  split
  · intro impossible; cases impossible
  · split <;> intro impossible <;> cases impossible

theorem mode_at (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (available : config.startup.preparation.length + 1 < whole.steps.length)
    (early : slot ≤ config.startup.preparation.length + 1) :
    ∃ monitor, E.monitorAt config (E.initial config) whole.steps slot = .startup monitor ∧
      monitor.mode = O.earlyMode config slot := by
  induction slot with
  | zero => exact ⟨P.initial config, by simp only [CampusTCPStartupTransferSuffix.monitorAt_zero, E.initial], initial_mode config⟩
  | succ slot ih =>
    obtain ⟨monitor, ending, mode⟩ := ih (by omega)
    obtain ⟨actual, found, before, event, after⟩ := CampusTCPSchedule.Trace.at whole.trace slot (by omega)
    have next := CampusTCPStartupEntry.monitorAt_next config (E.initial config) whole.steps found
    rw [ending] at next
    have checked : (actual.result.supported && actual.result.passed && P.allowed config actual.before monitor actual.event) = true := by
      by_cases accepted : (actual.result.supported && actual.result.passed && P.allowed config actual.before monitor actual.event) = true
      · exact accepted
      · have invalid : E.monitorAt config (E.initial config) whole.steps (slot + 1) = .startup ⟨.invalid, none⟩ := by
          rw [next]
          simp only [E.observe, P.observe, accepted, Bool.false_eq_true, ↓reduceIte, reduceCtorEq]
        have forbidden := (E.actions_correct _ _ _ _).mp actions (slot + 1) (by omega)
        rw [invalid] at forbidden
        change false = true at forbidden
        cases forbidden
    have nextMode : (P.observe config monitor actual).mode = O.earlyMode config (slot + 1) := by
      by_cases preparing : slot < config.startup.preparation.length
      · have current : monitor.mode = .preparation slot := by simpa only [O.earlyMode, preparing, ↓reduceIte] using mode
        simp only [P.observe, checked, current, ↓reduceIte]
        by_cases nextEarly : slot + 1 < config.startup.preparation.length
        · simp only [O.earlyMode, nextEarly, ↓reduceIte]
        · have boundary : slot + 1 = config.startup.preparation.length := by omega
          simp only [O.earlyMode, boundary, Nat.lt_irrefl, ↓reduceIte]
      · have boundary : slot = config.startup.preparation.length := by omega
        have current : monitor.mode = .opening := by
          rw [O.earlyMode, ite_eq_right preparing, ite_eq_left boundary] at mode
          exact mode
        have past : ¬slot + 1 < config.startup.preparation.length := by omega
        have different : slot + 1 ≠ config.startup.preparation.length := by omega
        simp only [P.observe, checked, current, ↓reduceIte, O.earlyMode, past, different]
    refine ⟨P.observe config monitor actual, ?_, nextMode⟩
    rw [next]
    simp only [E.observe, nextMode, early_not_data, ↓reduceIte]

theorem first_drive (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (available : config.startup.preparation.length + 1 < whole.steps.length) :
    ∃ monitor, E.monitorAt config (E.initial config) whole.steps (config.startup.preparation.length + 1) = .startup monitor ∧
      monitor.mode = .drive := by
  obtain ⟨monitor, ending, mode⟩ := mode_at actions available (Nat.le_refl (config.startup.preparation.length + 1))
  have later : ¬config.startup.preparation.length + 1 < config.startup.preparation.length := by omega
  have different : config.startup.preparation.length + 1 ≠ config.startup.preparation.length := by omega
  exact ⟨monitor, ending, by simpa only [O.earlyMode, later, different, ↓reduceIte] using mode⟩

end Netlib.Check.CampusTCPStartupDriveEntry
