import Netlib.Check.CampusTCPStartupDriveJobsEnabled

/-!
# Supported actual steps during startup drive

Current native facts come from the same whole prefix. The observed mode
leaves drive only when the actual event finishes startup.
-/

namespace Netlib.Check.CampusTCPStartupDriveStepEnabled

open Packet Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupServiceEnabled (PathsAligned)
open CampusTCPRecoveryStartupReceiveFields (PassiveTarget)

namespace E
export CampusTCPStartupTransferExecution (initial monitorAt actions observe)
end E
namespace P
export CampusTCPStartupMonitor (Monitor observe allowed)
end P
namespace S
export CampusTCPStartupSelection (allowed jobAllowed)
end S

variable {input : Input} {events : List CampusTCPModel.Event} {whole : Report input events}
variable {config : CampusTCPStartupTransferMonitor.Config} {monitor : P.Monitor} {count : Nat}

private theorem recovery_flags (connected : before.connection = .recovering current)
    (computed : runRecovery input before event = .ok effect) : effect.supported = true ∧ effect.passed = true := by
  simp only [runRecovery, connected] at computed
  split at computed
  · cases computed
  · rename_i result evaluated
    cases result with
    | mk state decision output receipt application =>
      cases output <;> simp only [pure, Except.pure, Except.ok.injEq] at computed
      all_goals subst effect; exact ⟨rfl, rfl⟩

private theorem finish_flags (connected : before.connection = .recovering current)
    (computed : finishStartup input before = .ok effect) : effect.supported = true ∧ effect.passed = true := by
  unfold finishStartup at computed
  rw [connected] at computed
  repeat' first
    | (solve | cases computed; exact ⟨rfl, rfl⟩)
    | (solve | simp_all only [reduceCtorEq])
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

private theorem Step.control_flags (actual : Step input) (connected : actual.before.connection = .recovering current)
    (control : (∃ actor millis, actual.event = .startupClock actor millis) ∨
      (∃ actor generation policy, actual.event = .startupTimeout actor generation policy) ∨ actual.event = .finishStartup) :
    actual.result.supported = true ∧ actual.result.passed = true := by
  obtain ⟨effect, custody, computed, final⟩ := actual.processed
  have flags : effect.supported = true ∧ effect.passed = true := by
    rcases control with ⟨actor, millis, event⟩ | ⟨actor, generation, policy, event⟩ | event
    · rw [event] at computed
      exact recovery_flags connected computed
    · rw [event] at computed
      exact recovery_flags connected computed
    · rw [event] at computed
      exact finish_flags connected computed
  simpa only [final] using flags

private theorem Step.drop_flags {packetID : Nat} (actual : Step input) (event : actual.event = .dropPacket packetID) :
    actual.result.supported = true ∧ actual.result.passed = true := by
  obtain ⟨effect, custody, computed, final⟩ := actual.processed
  simp only [processCore, event, pure, Except.pure, Except.ok.injEq] at computed
  subst effect
  exact ⟨by rw [final], by rw [final]⟩

variable (profile : CampusTCPStartupNative.Profile (input.contextFor .primary)
  (beforeService input (CampusTCPSchedule.stateAt input.initial whole.steps config.startup.preparation.length) .primary)
  input.zone (Handshake.outbound input.active config.startup.remote))

theorem supported_passed (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (within : count ≤ whole.steps.length)
    (ending : E.monitorAt config (E.initial config) whole.steps count = .startup monitor) (drive : monitor.mode = .drive)
    (paths : PathsAligned config profile) (valid : input.passive.Valid)
    (target : PassiveTarget profile.entry input.passive)
    (actual : Step input) (before : actual.before = CampusTCPSchedule.stateAt input.initial whole.steps count)
    (allowed : P.allowed config actual.before monitor actual.event = true) :
    actual.result.supported = true ∧ actual.result.passed = true := by
  obtain ⟨located⟩ := CampusTCPStartupCurrentAt.at_drive profile prep actions within ending drive
  have connected : actual.before.connection = .recovering located.current := by rw [before]; exact located.value.connected
  have permitted : S.allowed config actual.before monitor.protection actual.event = true := by simpa only [P.allowed, drive] using allowed
  have jobs (selected : S.jobAllowed config actual.before actual.event = true) :
      actual.result.supported = true ∧ actual.result.passed = true := by
    obtain ⟨current, job, member, ⟨result⟩⟩ := CampusTCPStartupDriveJobsEnabled.allowed_step profile prep actions within ending drive
      paths valid target actual before selected
    exact ⟨result.supported, result.passed⟩
  cases event : actual.event with
  | startupClock actor millis => exact Step.control_flags actual connected (Or.inl ⟨actor, millis, event⟩)
  | startupTimeout actor generation policy => exact Step.control_flags actual connected (Or.inr (Or.inl ⟨actor, generation, policy, event⟩))
  | finishStartup => exact Step.control_flags actual connected (Or.inr (Or.inr event))
  | dropPacket id => exact Step.drop_flags actual event
  | _ => exact jobs (by simpa only [S.allowed, event] using permitted)

theorem observed_mode (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (within : count ≤ whole.steps.length)
    (ending : E.monitorAt config (E.initial config) whole.steps count = .startup monitor) (drive : monitor.mode = .drive)
    (paths : PathsAligned config profile) (valid : input.passive.Valid)
    (target : PassiveTarget profile.entry input.passive)
    (actual : Step input) (before : actual.before = CampusTCPSchedule.stateAt input.initial whole.steps count)
    (allowed : P.allowed config actual.before monitor actual.event = true) :
    (P.observe config monitor actual).mode =
      if actual.event = .finishStartup then .setup .clientRecovery else .drive := by
  obtain ⟨supported, passed⟩ := supported_passed profile prep actions within ending drive paths valid target actual before allowed
  simp only [P.observe, supported, passed, allowed, Bool.and_self, ↓reduceIte, drive]
  split <;> rfl

theorem nonfinish (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (within : count ≤ whole.steps.length)
    (ending : E.monitorAt config (E.initial config) whole.steps count = .startup monitor) (drive : monitor.mode = .drive)
    (paths : PathsAligned config profile) (valid : input.passive.Valid)
    (target : PassiveTarget profile.entry input.passive)
    (actual : Step input) (before : actual.before = CampusTCPSchedule.stateAt input.initial whole.steps count)
    (allowed : P.allowed config actual.before monitor actual.event = true) (unfinished : actual.event ≠ .finishStartup) :
    actual.result.supported = true ∧ actual.result.passed = true ∧
      E.observe config (.startup monitor) actual = .startup (P.observe config monitor actual) ∧
        (P.observe config monitor actual).mode = .drive := by
  have flags := supported_passed profile prep actions within ending drive paths valid target actual before allowed
  have mode := observed_mode profile prep actions within ending drive paths valid target actual before allowed
  rw [ite_eq_right unfinished] at mode
  exact ⟨flags.1, flags.2, by simp only [E.observe, mode, reduceCtorEq, ↓reduceIte], mode⟩

end Netlib.Check.CampusTCPStartupDriveStepEnabled
