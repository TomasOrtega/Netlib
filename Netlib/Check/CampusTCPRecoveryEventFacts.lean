import Netlib.Check.CampusTCPRecoveryReceipts

/-!
# Actual recovery events in the campus model

The recorded control step comes from this campus operation.
Its event stamp remains distinct from output and service positions.
-/

namespace Netlib.Check.CampusTCPRecoveryEventFacts

open CampusTCPModel CampusTCPRecoveryReceipts

variable {input : Input} {before : State input} {effect : Effect input}
variable {control : C.Step input.active input.passive}

private def Events (event : Event) (effect : Effect input) : Prop :=
  ∀ control, effect.recovery = some control → RecoveryEvent event control.event

private theorem recovery_fields (computed : runRecovery input before event = .ok effect)
    (recorded : effect.recovery = some control) : before.connection = .recovering control.before ∧ control.event = event := by
  unfold runRecovery at computed
  split at computed
  · cases computed; cases recorded
  · cases computed; cases recorded
  · split at computed
    · cases computed
    · rename_i current connected result evaluated
      cases result with
      | mk state decision output receipt application =>
        cases output <;> simp only [pure, Except.pure, Except.ok.injEq] at computed
        all_goals subst effect; cases recorded; exact ⟨by assumption, rfl⟩

private theorem recovery_events (relation : RecoveryEvent joint event)
    (computed : runRecovery input before event = .ok effect) : Events joint effect := by
  intro control recorded
  rw [(recovery_fields computed recorded).2]
  exact relation

private theorem startup_events (computed : startup input before event = .ok effect) : Events joint effect := by
  unfold startup at computed
  repeat' first
    | (solve | cases computed; intro control recorded; cases recorded)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem application_events (computed : applyApplication input before actor event = .ok effect) : Events joint effect := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; intro control recorded; cases recorded)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

private theorem open_events (computed : openRecovering input before remote policy = .ok effect) :
    Events (.openRecovering remote policy) effect := by
  unfold openRecovering at computed
  repeat' first
    | (solve | exact recovery_events (.opened remote policy) computed)
    | (solve | cases computed; intro control recorded; cases recorded)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem finish_events (computed : finishStartup input before = .ok effect) : Events joint effect := by
  unfold finishStartup at computed
  repeat' first
    | (solve | cases computed; intro control recorded; cases recorded)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem enableAck_events (computed : enableAck input before actor = .ok effect) : Events joint effect := by
  unfold enableAck at computed
  repeat' first
    | (solve | exact application_events computed)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem enableStartup_events (computed : enableStartupRecovery input before actor = .ok effect) : Events joint effect := by
  unfold enableStartupRecovery at computed
  split at computed
  · cases computed; intro control recorded; cases recorded
  · exact application_events computed

private theorem process_events (computed : processCore input before joint = .ok effect) : Events joint effect := by
  cases joint with
  | «open» remote policy => exact startup_events computed
  | openRecovering remote policy => exact open_events computed
  | startupClock actor millis => exact recovery_events (.clock actor millis) computed
  | startupTimeout actor generation policy => exact recovery_events (.timeout actor generation policy) computed
  | finishStartup => exact finish_events computed
  | write actor bytes | send actor count policy | read actor count | emitAck actor policy
  | enableRecovery actor | advanceClock actor millis | timeout actor policy | dispatchAck actor policy =>
    exact application_events computed
  | enableAck actor => exact enableAck_events computed
  | enableStartupRecovery actor => exact enableStartup_events computed
  | copyPacket id | dropPacket id => cases computed; intro control recorded; cases recorded
  | authentication index =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed; intro control recorded; cases recorded)
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | install id | stage id | installGuard id | installAt gateway id | stageAt gateway id | installGuardAt gateway id =>
    simp only [processCore, installConfiguration, stageAttachment, installIngress] at computed
    repeat' first
      | (solve | cases computed; intro control recorded; cases recorded)
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | pause | stageCheckpoint | installCheckpoint ns | switchRoute actor gateway | fencePrimary | resume =>
    simp only [processCore, transferControl] at computed
    repeat' first
      | (solve | cases computed; intro control recorded; cases recorded)
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | assign index ingress | serve id observed =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed; intro control recorded; cases recorded)
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | deliver index bytes policy =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed; intro control recorded; cases recorded)
      | (solve | cases computed)
      | (solve | cases computed; have fields := startup_events (input := input) (before := before) (joint := .deliver index bytes policy) (by assumption); exact fields)
      | (solve | cases computed; have fields := application_events (input := input) (before := before) (joint := .deliver index bytes policy) (by assumption); exact fields)
      | (solve | cases computed; have fields := recovery_events (input := input) (before := before) (.delivered index _ bytes policy) (by assumption); exact fields)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

theorem Step.recovery_event (actual : Step input) (recorded : actual.result.recovery = some control) :
    RecoveryEvent actual.event control.event := by
  obtain ⟨effect, custody, computed, result⟩ := actual.processed
  exact process_events computed control (by simpa only [result] using recorded)

theorem Step.recovery_clock_before (actual : Step input) (recorded : actual.result.recovery = some control)
    (event : actual.event = .startupClock actor millis) : actual.before.connection = .recovering control.before := by
  obtain ⟨effect, custody, computed, result⟩ := actual.processed
  have present : effect.recovery = some control := by simpa only [result] using recorded
  rw [event] at computed
  exact (recovery_fields computed present).1

end Netlib.Check.CampusTCPRecoveryEventFacts
