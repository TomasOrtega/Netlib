import Netlib.Check.CampusTCPStartupDriveStepEnabled
import Netlib.Check.CampusTCPStartupCriticalDemandAt

/-!
# Actual drive prefixes before startup completes

Completion records an existing whole-report slot. Until that slot appears,
actual allowed steps retain drive mode and its protected work.
-/

namespace Netlib.Check.CampusTCPStartupDriveUntilComplete

open Packet Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupServiceEnabled (PathsAligned)
open CampusTCPRecoveryStartupReceiveFields (PassiveTarget)

namespace E
export CampusTCPStartupTransferExecution (initial monitorAt actions actions_correct)
end E
namespace P
export CampusTCPStartupMonitor (Monitor allowed observe)
end P
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S
namespace R
export CampusTCPStartupSelection (phaseRank)
end R

variable {input : Input} {events : List CampusTCPModel.Event} {whole : Report input events}
variable {config : CampusTCPStartupTransferMonitor.Config}

def Completed (whole : Report input events) (count : Nat) : Prop :=
  ∃ slot, slot ≤ count ∧ R.phaseRank (S.stateAt input.initial whole.steps slot) = 4

theorem Completed.mono (completed : Completed whole first) (order : first ≤ last) : Completed whole last := by
  obtain ⟨slot, within, phase⟩ := completed
  exact ⟨slot, Nat.le_trans within order, phase⟩

theorem Completed.of_phase (phase : R.phaseRank (S.stateAt input.initial whole.steps count) = 4) : Completed whole count :=
  ⟨count, Nat.le_refl count, phase⟩

theorem incomplete (unfinished : ¬Completed whole count) (before : slot ≤ count) :
    R.phaseRank (S.stateAt input.initial whole.steps slot) ≠ 4 :=
  fun phase => unfinished ⟨slot, before, phase⟩

variable (profile : CampusTCPStartupNative.Profile (input.contextFor .primary)
  (beforeService input (S.stateAt input.initial whole.steps config.startup.preparation.length) .primary)
  input.zone (Handshake.outbound input.active config.startup.remote))

theorem step (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (paths : PathsAligned config profile) (valid : input.passive.Valid) (target : PassiveTarget profile.entry input.passive)
    (within : slot < whole.steps.length) (monitor : P.Monitor)
    (ending : E.monitorAt config (E.initial config) whole.steps slot = .startup monitor) (drive : monitor.mode = .drive)
    (incomplete : R.phaseRank (S.stateAt input.initial whole.steps slot) ≠ 4)
    (actual : Step input) (found : whole.steps[slot]? = some actual) :
    actual.result.supported = true ∧ actual.result.passed = true ∧
      E.monitorAt config (E.initial config) whole.steps (slot + 1) = .startup (P.observe config monitor actual) ∧
      (P.observe config monitor actual).mode = .drive ∧
      (P.observe config monitor actual).protection = CampusTCPStartupMonitor.advanceProtection config monitor actual := by
  obtain ⟨selected, selectedAt, before, event, after⟩ := CampusTCPSchedule.Trace.at whole.trace slot within
  have same : selected = actual := Option.some.inj (selectedAt.symm.trans found)
  subst selected
  have permitted := (E.actions_correct _ _ _ _).mp actions slot within
  rw [ending] at permitted
  have allowed : P.allowed config actual.before monitor actual.event = true := by
    simpa only [CampusTCPStartupTransferExecution.allowed, ← before, ← event] using permitted
  have unfinished : actual.event ≠ .finishStartup := by
    intro finished
    have demand : CampusTCPStartupSelection.demand config actual.before monitor.protection = some .finishStartup := by
      simpa only [P.allowed, drive, finished, CampusTCPStartupSelection.allowed, decide_eq_true_eq] using allowed
    have phase := CampusTCPStartupCriticalDemand.finish_complete demand
    exact incomplete (by rw [← before]; exact phase)
  obtain ⟨supported, passed, observed, mode⟩ := CampusTCPStartupDriveStepEnabled.nonfinish profile prep actions
    (Nat.le_of_lt within) ending drive paths valid target actual before allowed unfinished
  have next := CampusTCPStartupEntry.monitorAt_next config (E.initial config) whole.steps found
  refine ⟨supported, passed, ?_, mode, ?_⟩
  · rw [next, ending]
    exact observed
  · simp only [P.observe, supported, passed, allowed, Bool.and_self, ↓reduceIte, drive, unfinished]

theorem drive_at (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (paths : PathsAligned config profile) (valid : input.passive.Valid) (target : PassiveTarget profile.entry input.passive)
    (start : Nat) (initialMonitor : P.Monitor)
    (starting : E.monitorAt config (E.initial config) whole.steps start = .startup initialMonitor)
    (startMode : initialMonitor.mode = .drive) (order : start ≤ count) (within : count ≤ whole.steps.length)
    (unfinished : ¬Completed whole count) :
    ∃ monitor, E.monitorAt config (E.initial config) whole.steps count = .startup monitor ∧ monitor.mode = .drive := by
  have propagate : ∀ offset, start + offset ≤ whole.steps.length → ¬Completed whole (start + offset) →
      ∃ monitor, E.monitorAt config (E.initial config) whole.steps (start + offset) = .startup monitor ∧ monitor.mode = .drive := by
    intro offset
    induction offset with
    | zero =>
      intro available unfinished
      exact ⟨initialMonitor, by simpa only [Nat.add_zero] using starting, startMode⟩
    | succ offset ih =>
      intro available unfinished
      obtain ⟨monitor, ending, drive⟩ := ih (by omega) (fun completed => unfinished (completed.mono (by omega)))
      obtain ⟨actual, found, before, event, after⟩ := CampusTCPSchedule.Trace.at whole.trace (start + offset) (by omega)
      obtain ⟨supported, passed, next, mode, protection⟩ := step profile prep actions paths valid target
        (by omega : start + offset < whole.steps.length) monitor ending drive
        (incomplete unfinished (by omega)) actual found
      exact ⟨P.observe config monitor actual, by simpa only [Nat.add_assoc] using next, mode⟩
  have sum : start + (count - start) = count := Nat.add_sub_of_le order
  simpa only [sum] using propagate (count - start) (by omega) (by simpa only [sum] using unfinished)

include profile in
theorem phases (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (within : count ≤ whole.steps.length) (monitor : P.Monitor)
    (ending : E.monitorAt config (E.initial config) whole.steps count = .startup monitor) (drive : monitor.mode = .drive)
    (unfinished : ¬Completed whole count) :
    R.phaseRank (S.stateAt input.initial whole.steps count) = 1 ∨
      R.phaseRank (S.stateAt input.initial whole.steps count) = 2 ∨
      R.phaseRank (S.stateAt input.initial whole.steps count) = 3 := by
  obtain ⟨located⟩ := CampusTCPStartupCurrentAt.at_drive profile prep actions within ending drive
  have nonidle := CampusTCPStartupCriticalDemandAt.at_nonidle located actions ending drive
  exact CampusTCPStartupCriticalDemandAt.incomplete_phases located.value.connected nonidle (incomplete unfinished (Nat.le_refl count))

include profile in
theorem positive_rank (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (within : count ≤ whole.steps.length) (monitor : P.Monitor)
    (ending : E.monitorAt config (E.initial config) whole.steps count = .startup monitor) (drive : monitor.mode = .drive)
    (unfinished : ¬Completed whole count) :
    0 < CampusTCPStartupCriticalRank.rank config.transfer.quantum (S.stateAt input.initial whole.steps count) monitor.protection := by
  obtain ⟨located⟩ := CampusTCPStartupCurrentAt.at_drive profile prep actions within ending drive
  exact CampusTCPStartupCriticalDemandAt.at_positive located actions ending drive prep (incomplete unfinished (Nat.le_refl count))

end Netlib.Check.CampusTCPStartupDriveUntilComplete
