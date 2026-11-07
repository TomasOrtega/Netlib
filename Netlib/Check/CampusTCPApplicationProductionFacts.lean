import Netlib.Check.CampusTCPModel

/-!
# Actual application productions

An application packet names the same local operation recorded by its campus step.
-/

namespace Netlib.Check.CampusTCPApplicationProductionFacts

open CampusTCPModel

variable {input : Input}

private def Recorded (effect : Effect input) : Prop :=
  ∀ actor actual output origin, effect.output = some (.application actor actual output origin) → effect.application = some (actor, actual)

private theorem startup_recorded (computed : startup input before event = .ok effect) : Recorded effect := by
  unfold startup at computed
  split at computed
  · cases computed
    intro actor actual output origin selected
    cases selected
  · cases computed
    intro actor actual output origin selected
    cases selected
  · split at computed
    · cases computed
    · rename_i result evaluated
      cases result with
      | mk state decision decoded output delivery =>
        cases output <;> simp only [pure, Except.pure, Except.ok.injEq] at computed
        all_goals
          subst effect
          intro actor actual output origin selected
          cases selected

private theorem application_recorded (computed : applyApplication input before actor event = .ok effect) : Recorded effect := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; intro actor actual output origin selected; cases selected <;> rfl)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

private theorem recovery_recorded (computed : runRecovery input before event = .ok effect) : Recorded effect := by
  unfold runRecovery at computed
  split at computed
  · cases computed
    intro actor actual output origin selected
    cases selected
  · cases computed
    intro actor actual output origin selected
    cases selected
  · split at computed
    · cases computed
    · rename_i current connected result evaluated
      cases result with
      | mk state decision output receipt application =>
        cases output <;> simp only [pure, Except.pure, Except.ok.injEq] at computed
        all_goals
          subst effect
          intro actor actual output origin selected
          cases selected

private theorem openRecovery_recorded (computed : openRecovering input before remote policy = .ok effect) : Recorded effect := by
  unfold openRecovering at computed
  repeat' first
    | (solve | exact recovery_recorded computed)
    | (solve | cases computed; intro actor actual output origin selected; cases selected)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem finish_recorded (computed : finishStartup input before = .ok effect) : Recorded effect := by
  unfold finishStartup at computed
  repeat' first
    | (solve | cases computed; intro actor actual output origin selected; cases selected)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem enableAck_recorded (computed : enableAck input before actor = .ok effect) : Recorded effect := by
  unfold enableAck at computed
  repeat' first
    | (solve | exact application_recorded computed)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem enableStartup_recorded (computed : enableStartupRecovery input before actor = .ok effect) : Recorded effect := by
  unfold enableStartupRecovery at computed
  split at computed
  · cases computed
    intro actor actual output origin selected
    cases selected
  · exact application_recorded computed

private theorem process_recorded (computed : processCore input before event = .ok effect) : Recorded effect := by
  cases event with
  | «open» remote policy => exact startup_recorded computed
  | openRecovering remote policy => exact openRecovery_recorded computed
  | startupClock actor millis | startupTimeout actor generation policy => exact recovery_recorded computed
  | finishStartup => exact finish_recorded computed
  | write actor bytes | send actor count policy | read actor count | emitAck actor policy
  | enableRecovery actor | advanceClock actor millis | timeout actor policy | dispatchAck actor policy =>
    exact application_recorded computed
  | enableAck actor => exact enableAck_recorded computed
  | enableStartupRecovery actor => exact enableStartup_recorded computed
  | copyPacket id | dropPacket id =>
    cases computed
    intro actor actual output origin selected
    cases selected
  | authentication index =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed; intro actor actual output origin selected; cases selected)
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | install id | stage id | installGuard id | installAt gateway id | stageAt gateway id | installGuardAt gateway id =>
    simp only [processCore, installConfiguration, stageAttachment, installIngress] at computed
    repeat' first
      | (solve | cases computed; intro actor actual output origin selected; cases selected)
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | pause | stageCheckpoint | installCheckpoint ns | switchRoute actor gateway | fencePrimary | resume =>
    simp only [processCore, transferControl] at computed
    repeat' first
      | (solve | cases computed; intro actor actual output origin selected; cases selected)
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | assign index ingress | serve id observed =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed; intro actor actual output origin selected; cases selected)
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | deliver index bytes policy =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed; have fields := startup_recorded (input := input) (before := before) (by assumption); exact fields)
      | (solve | cases computed; have fields := application_recorded (input := input) (before := before) (by assumption); exact fields)
      | (solve | cases computed; have fields := recovery_recorded (input := input) (before := before) (by assumption); exact fields)
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

theorem Step.application_output_recorded (joint : Step input) (actor : Actor) (actual : T.Step)
    (output : Protocol.TCP.EstablishedReceive.Input) (origin : T.OutputOrigin actual output)
    (selected : joint.result.output = some (.application actor actual output origin)) :
    joint.result.application = some (actor, actual) := by
  obtain ⟨effect, custody, computed, result⟩ := joint.processed
  have emitted : effect.output = some (.application actor actual output origin) := by simpa only [result] using selected
  simpa only [result] using process_recorded computed actor actual output origin emitted

end Netlib.Check.CampusTCPApplicationProductionFacts
