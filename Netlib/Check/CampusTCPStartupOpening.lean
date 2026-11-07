import Netlib.Check.CampusTCPStartupEntry

/-!
# The actual OPEN before any current drive cut

The preparation occupies its literal slots. A drive observation therefore
retains the OPEN at the next fixed index in the same stored report.
-/

namespace Netlib.Check.CampusTCPStartupOpening

open CampusTCPModel

namespace E
export CampusTCPStartupTransferExecution (initial monitorAt actions actions_correct)
end E
namespace P
export CampusTCPStartupMonitor (Monitor Mode initial observe allowed nextDemand)
end P
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

variable {input : Input} {events : List Event} {whole : Report input events}
variable {config : CampusTCPStartupTransferMonitor.Config} {monitor : P.Monitor} {count slot : Nat}

def earlyMode (config : CampusTCPStartupTransferMonitor.Config) (slot : Nat) : P.Mode :=
  if slot < config.startup.preparation.length then .preparation slot
  else if slot = config.startup.preparation.length then .opening else .drive

private theorem checked_cold (prior : P.Monitor) (actual : Step input)
    (cold : CampusTCPStartupProfile.ColdMode (P.observe config prior actual).mode) :
    (actual.result.supported && actual.result.passed && P.allowed config actual.before prior actual.event) = true := by
  by_cases checked : (actual.result.supported && actual.result.passed && P.allowed config actual.before prior actual.event) = true
  · exact checked
  · simp only [P.observe, checked, Bool.false_eq_true, ↓reduceIte, CampusTCPStartupProfile.ColdMode] at cold

private theorem initial_mode (config : CampusTCPStartupTransferMonitor.Config) :
    (P.initial config).mode = earlyMode config 0 := by
  cases preparation : config.startup.preparation with
  | nil => simp only [P.initial, preparation, List.isEmpty_nil, ↓reduceIte, earlyMode, List.length_nil,
      Nat.lt_irrefl, ↓reduceIte]
  | cons head rest => simp only [P.initial, preparation, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
      earlyMode, List.length_cons, Nat.zero_lt_succ, ↓reduceIte]

theorem mode_at (within : count ≤ whole.steps.length)
    (ending : E.monitorAt config (E.initial config) whole.steps count = .startup monitor)
    (drive : monitor.mode = .drive) (before : slot ≤ count) :
    ∃ prior, E.monitorAt config (E.initial config) whole.steps slot = .startup prior ∧ prior.mode = earlyMode config slot := by
  induction slot with
  | zero => exact ⟨P.initial config, by simp only [CampusTCPStartupTransferSuffix.monitorAt_zero, E.initial], initial_mode config⟩
  | succ slot ih =>
    obtain ⟨prior, priorAt, priorMode⟩ := ih (by omega)
    obtain ⟨after, afterAt, afterCold⟩ := CampusTCPStartupProfileFacts.monitorAt_cold_past ending (by rw [drive]; trivial) before
    obtain ⟨actual, found, state, event, next⟩ := CampusTCPSchedule.Trace.at whole.trace slot (by omega)
    have observed := CampusTCPStartupEntry.monitorAt_next config (E.initial config) whole.steps found
    rw [priorAt] at observed
    have same := CampusTCPStartupEntry.observe_startup_eq prior actual after (observed.symm.trans afterAt)
    have cold : CampusTCPStartupProfile.ColdMode (P.observe config prior actual).mode := by rw [same]; exact afterCold
    have checked := checked_cold prior actual cold
    refine ⟨after, afterAt, ?_⟩
    rw [← same]
    by_cases preparing : slot < config.startup.preparation.length
    · have mode : prior.mode = .preparation slot := by simpa only [earlyMode, preparing, ↓reduceIte] using priorMode
      simp only [P.observe, checked, mode, ↓reduceIte]
      by_cases later : slot + 1 < config.startup.preparation.length
      · simp only [earlyMode, later, ↓reduceIte]
      · have boundary : slot + 1 = config.startup.preparation.length := by omega
        simp only [earlyMode, boundary, Nat.lt_irrefl, ↓reduceIte]
    · by_cases opening : slot = config.startup.preparation.length
      · have mode : prior.mode = .opening := by
          rw [earlyMode, ite_eq_right preparing, ite_eq_left opening] at priorMode
          exact priorMode
        have past : ¬slot + 1 < config.startup.preparation.length := by omega
        have different : slot + 1 ≠ config.startup.preparation.length := by omega
        simp only [P.observe, checked, mode, ↓reduceIte, earlyMode, past, different]
      · have mode : prior.mode = .drive := by simpa only [earlyMode, preparing, opening, ↓reduceIte] using priorMode
        have unfinished : actual.event ≠ .finishStartup := by
          intro finished
          have accepted : (actual.result.supported && actual.result.passed && P.allowed config actual.before prior .finishStartup) = true := by
            simpa only [finished] using checked
          simp only [P.observe, mode, finished, accepted, ↓reduceIte, CampusTCPStartupProfile.ColdMode] at cold
        have past : ¬slot + 1 < config.startup.preparation.length := by omega
        have different : slot + 1 ≠ config.startup.preparation.length := by omega
        simp only [P.observe, checked, mode, unfinished, ↓reduceIte, earlyMode, past, different]

theorem preparation_before (within : count ≤ whole.steps.length)
    (ending : E.monitorAt config (E.initial config) whole.steps count = .startup monitor)
    (drive : monitor.mode = .drive) : config.startup.preparation.length < count := by
  obtain ⟨prior, priorAt, mode⟩ := mode_at within ending drive (Nat.le_refl count)
  have same : prior = monitor := CampusTCPStartupTransferExecution.Monitor.startup.inj (priorAt.symm.trans ending)
  rw [same, drive, earlyMode] at mode
  split at mode
  · cases mode
  · split at mode
    · cases mode
    · omega

theorem drive_at (within : count ≤ whole.steps.length)
    (ending : E.monitorAt config (E.initial config) whole.steps count = .startup monitor)
    (drive : monitor.mode = .drive) (afterOpen : config.startup.preparation.length < slot) (before : slot ≤ count) :
    ∃ prior, E.monitorAt config (E.initial config) whole.steps slot = .startup prior ∧ prior.mode = .drive := by
  obtain ⟨prior, priorAt, mode⟩ := mode_at within ending drive before
  have notBefore : ¬slot < config.startup.preparation.length := by omega
  have notEqual : slot ≠ config.startup.preparation.length := by omega
  exact ⟨prior, priorAt, by simpa only [earlyMode, notBefore, notEqual, ↓reduceIte] using mode⟩

theorem preparation_event (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (within : count ≤ whole.steps.length)
    (ending : E.monitorAt config (E.initial config) whole.steps count = .startup monitor)
    (drive : monitor.mode = .drive) (early : slot < config.startup.preparation.length)
    (actual : Step input) (found : whole.steps[slot]? = some actual) :
    CampusTCPStartupProfile.PreparationEvent actual.event := by
  have bound := preparation_before within ending drive
  obtain ⟨prior, priorAt, priorMode⟩ := mode_at within ending drive (by omega : slot ≤ count)
  have fields : prior.mode = .preparation slot := by simpa only [earlyMode, early, ↓reduceIte] using priorMode
  have permitted := (E.actions_correct _ _ _ _).mp actions slot (by omega)
  obtain ⟨selected, selectedAt, before, event, after⟩ := CampusTCPSchedule.Trace.at whole.trace slot (by omega)
  have same : selected = actual := Option.some.inj (selectedAt.symm.trans found)
  subst selected
  rw [priorAt] at permitted
  apply CampusTCPStartupProfile.preparation_allowed prep fields
  simpa only [← before, ← event, CampusTCPStartupTransferExecution.allowed] using permitted

theorem opening_event (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (within : count ≤ whole.steps.length)
    (ending : E.monitorAt config (E.initial config) whole.steps count = .startup monitor)
    (drive : monitor.mode = .drive) :
    ∃ actual : Step input, whole.steps[config.startup.preparation.length]? = some actual ∧
      actual.before = S.stateAt input.initial whole.steps config.startup.preparation.length ∧
      actual.event = .openRecovering config.startup.remote true ∧
      actual.result.state = S.stateAt input.initial whole.steps (config.startup.preparation.length + 1) := by
  have available := preparation_before within ending drive
  obtain ⟨prior, priorAt, priorMode⟩ := mode_at within ending drive (by omega : config.startup.preparation.length ≤ count)
  have opening : prior.mode = .opening := by simpa only [earlyMode, Nat.lt_irrefl, ↓reduceIte] using priorMode
  obtain ⟨actual, found, state, event, after⟩ := CampusTCPSchedule.Trace.at whole.trace config.startup.preparation.length (by omega)
  have permitted := (E.actions_correct _ _ _ _).mp actions config.startup.preparation.length (by omega)
  rw [priorAt] at permitted
  have localAllowed : P.allowed config actual.before prior actual.event = true := by simpa only [← state, ← event, CampusTCPStartupTransferExecution.allowed] using permitted
  simp only [P.allowed, opening, P.nextDemand] at localAllowed
  exact ⟨actual, found, state, (Option.some.inj (of_decide_eq_true localAllowed)).symm, after⟩

end Netlib.Check.CampusTCPStartupOpening
