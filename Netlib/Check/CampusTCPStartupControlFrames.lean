import Netlib.Check.CampusTCPStartupPrimaryServices

/-!
# Transfer-control fields during cold startup

Startup and preparation retain the actual pause, seal, fence, and install
fields. The current primary is available before any transfer controls.
-/

namespace Netlib.Check.CampusTCPStartupControlFrames

open CampusTCPModel CampusTCPRecoveryStartupCold

variable {input : Input} {before : State input} {effect : Effect input}
variable {gateway : Gateway} {id : String}

def controls (state : State input) :=
  (state.assignmentPaused, state.primarySealed, state.primaryFenced, state.installation.isSome)

private theorem install_controls (computed : installConfiguration input before gateway id = .ok effect) :
    controls effect.state = controls before := by
  unfold installConfiguration at computed
  repeat' first
    | (solve | cases computed; cases gateway <;> rfl)
    | cases computed
    | split at computed
    | dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed

private theorem stage_controls (computed : stageAttachment input before gateway id = .ok effect) :
    controls effect.state = controls before := by
  unfold stageAttachment at computed
  repeat' first
    | (solve | cases computed; cases gateway <;> rfl)
    | cases computed
    | split at computed
    | dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed

private theorem guard_controls (computed : installIngress input before gateway id = .ok effect) :
    controls effect.state = controls before := by
  unfold installIngress at computed
  repeat' first
    | (solve | cases computed; cases gateway <;> rfl)
    | cases computed
    | split at computed
    | dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed

private theorem authentication_controls (computed : processCore input before (.authentication index) = .ok effect) :
    controls effect.state = controls before := by
  simp only [processCore] at computed
  repeat' first
    | (solve | cases computed; rfl)
    | cases computed
    | split at computed
    | dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed

theorem Step.cold_controls (actual : Step input) (cold : ColdEvent actual.event) :
    controls actual.result.state = controls actual.before := by
  by_cases transport : CampusTCPRoundEnvironment.TransportOnly actual.event
  · have same := CampusTCPRoundEnvironment.Step.environment actual transport
    exact (congrArg (fun value : CampusTCPRoundEnvironment.Environment =>
      (value.assignmentPaused, value.primarySealed, value.primaryFenced, value.installed)) same).symm
  obtain ⟨effect, custody, computed, final⟩ := actual.processed
  have frame : controls effect.state = controls actual.before := by
    cases event : actual.event with
    | authentication index => rw [event] at computed; exact authentication_controls computed
    | install id | installAt gateway id => rw [event] at computed; exact install_controls computed
    | stage id | stageAt gateway id => rw [event] at computed; exact stage_controls computed
    | installGuard id | installGuardAt gateway id => rw [event] at computed; exact guard_controls computed
    | _ => simp only [event, ColdEvent, CampusTCPRoundEnvironment.TransportOnly, not_true_eq_false] at cold transport
  simpa only [final, controls] using frame

theorem Trace.cold_controls (trace : Trace input initial events steps final remaining)
    (cold : ∀ actual ∈ steps, ColdEvent actual.event) : controls final = controls initial := by
  induction trace with
  | done => rfl
  | stop head blocked rest => exact Step.cold_controls head (cold head List.mem_cons_self)
  | next head supported rest ih =>
    exact (ih (fun actual member => cold actual (List.mem_cons_of_mem head member))).trans
      (Step.cold_controls head (cold head List.mem_cons_self))

theorem Report.control_fields (report : Report input events) (cold : ColdProfile report) :
    report.final.assignmentPaused = false ∧ report.final.primarySealed = false ∧
      report.final.primaryFenced = false ∧ report.final.installation = none := by
  have same := Trace.cold_controls report.trace cold
  have paused := congrArg Prod.fst same
  have sealed := congrArg (fun value => value.2.1) same
  have fenced := congrArg (fun value => value.2.2.1) same
  have installed := congrArg (fun value => value.2.2.2) same
  refine ⟨paused, sealed, fenced, ?_⟩
  cases present : report.final.installation with
  | none => rfl
  | some value => simp only [controls, present, Option.isSome_some, Input.initial, Option.isSome_none] at installed; cases installed

end Netlib.Check.CampusTCPStartupControlFrames
