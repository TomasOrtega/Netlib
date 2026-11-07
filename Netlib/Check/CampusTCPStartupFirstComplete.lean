import Netlib.Check.CampusTCPStartupDriveUntilComplete
import Netlib.Check.CampusTCPStartupDriveEntry

/-!
# The first actual completed startup cut is still in drive mode

Preparation and the real OPEN exclude an earlier completed cut.
-/

namespace Netlib.Check.CampusTCPStartupFirstComplete

open Packet Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupServiceEnabled (PathsAligned)
open CampusTCPRecoveryStartupReceiveFields (PassiveTarget)

namespace E
export CampusTCPStartupTransferExecution (initial monitorAt actions)
end E
namespace P
export CampusTCPStartupMonitor (Monitor observe)
end P
namespace S
export CampusTCPSchedule (stateAt)
end S
namespace R
export CampusTCPStartupSelection (phaseRank)
end R
namespace U
export CampusTCPStartupDriveUntilComplete (Completed incomplete step drive_at)
end U

variable {input : Input} {events : List CampusTCPModel.Event} {whole : Report input events}
variable {config : CampusTCPStartupTransferMonitor.Config}
variable {id : String}

private theorem install_connection (computed : installConfiguration input before gateway id = .ok effect) :
    effect.state.connection = before.connection := by
  unfold installConfiguration at computed
  repeat' first
    | (solve | cases computed; cases gateway <;> rfl)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

private theorem stage_connection (computed : stageAttachment input before gateway id = .ok effect) :
    effect.state.connection = before.connection := by
  unfold stageAttachment at computed
  repeat' first
    | (solve | cases computed; cases gateway <;> rfl)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

private theorem guard_connection (computed : installIngress input before gateway id = .ok effect) :
    effect.state.connection = before.connection := by
  unfold installIngress at computed
  repeat' first
    | (solve | cases computed; cases gateway <;> rfl)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

private theorem Step.preparation_connection (actual : Step input)
    (preparation : CampusTCPStartupProfile.PreparationEvent actual.event) :
    actual.result.state.connection = actual.before.connection := by
  obtain ⟨effect, custody, computed, final⟩ := actual.processed
  have frame : effect.state.connection = actual.before.connection := by
    cases event : actual.event with
    | authentication index =>
      simp only [processCore, event] at computed
      repeat' first
        | (solve | cases computed; rfl)
        | (solve | cases computed)
        | (split at computed)
        | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
    | install id | installAt gateway id => rw [event] at computed; exact install_connection computed
    | stage id | stageAt gateway id => rw [event] at computed; exact stage_connection computed
    | installGuard id | installGuardAt gateway id => rw [event] at computed; exact guard_connection computed
    | _ => simp only [event, CampusTCPStartupProfile.PreparationEvent] at preparation
  simpa only [final] using frame

private theorem Trace.preparation_connection (trace : Trace input before events steps after remaining)
    (preparation : ∀ actual ∈ steps, CampusTCPStartupProfile.PreparationEvent actual.event) :
    after.connection = before.connection := by
  induction trace with
  | done => rfl
  | stop head blocked rest => exact Step.preparation_connection head (preparation head List.mem_cons_self)
  | next head supported rest ih =>
    exact (ih (fun actual member => preparation actual (List.mem_cons_of_mem head member))).trans
      (Step.preparation_connection head (preparation head List.mem_cons_self))

private theorem preparation_state (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (available : config.startup.preparation.length + 1 < whole.steps.length)
    (early : slot ≤ config.startup.preparation.length) :
    (S.stateAt input.initial whole.steps slot).connection = input.initial.connection := by
  obtain ⟨monitor, ending, drive⟩ := CampusTCPStartupDriveEntry.first_drive actions available
  have preparations : ∀ actual ∈ whole.steps.take slot, CampusTCPStartupProfile.PreparationEvent actual.event := by
    intro actual member
    obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
    have bound := (List.getElem?_eq_some_iff.mp found).1
    have inside : index < slot := by rw [List.length_take] at bound; omega
    have actualAt : whole.steps[index]? = some actual := by
      simpa only [List.getElem?_take_of_lt inside] using found
    exact CampusTCPStartupOpening.preparation_event prep actions (by omega) ending drive (by omega) actual actualAt
  exact Trace.preparation_connection (CampusTCPSchedule.Trace.take whole.trace slot (by omega)) preparations

theorem first_phase (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (available : config.startup.preparation.length + 1 < whole.steps.length) :
    R.phaseRank (S.stateAt input.initial whole.steps (config.startup.preparation.length + 1)) = 1 := by
  obtain ⟨monitor, ending, drive⟩ := CampusTCPStartupDriveEntry.first_drive actions available
  have prepared := preparation_state prep actions available (Nat.le_refl config.startup.preparation.length)
  have idle : (S.stateAt input.initial whole.steps config.startup.preparation.length).connection = .startup .idle rfl := prepared
  obtain ⟨actual, _, before, event, after⟩ := CampusTCPStartupOpening.opening_event actions (by omega) ending drive
  obtain ⟨opened⟩ := CampusTCPRecoveryStartupOpened.Step.opened actual (by rw [before]; exact idle) event
  rw [← after]
  simp only [R.phaseRank, opened.after, opened.phase]

theorem first_unfinished (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (available : config.startup.preparation.length + 1 < whole.steps.length) :
    ¬U.Completed whole (config.startup.preparation.length + 1) := by
  rintro ⟨slot, bound, complete⟩
  by_cases early : slot ≤ config.startup.preparation.length
  · have idle := preparation_state prep actions available early
    have zero : R.phaseRank (S.stateAt input.initial whole.steps slot) = 0 := by rw [R.phaseRank, idle]; rfl
    omega
  · have same : slot = config.startup.preparation.length + 1 := by omega
    have phase := first_phase prep actions available
    rw [same] at complete
    omega

structure Found (config : CampusTCPStartupTransferMonitor.Config) (whole : Report input events) (deadline : Nat) where
  slot : Nat
  bound : slot ≤ deadline
  within : slot ≤ whole.steps.length
  afterOpening : config.startup.preparation.length + 1 < slot
  monitor : P.Monitor
  ending : E.monitorAt config (E.initial config) whole.steps slot = .startup monitor
  drive : monitor.mode = .drive
  phase : R.phaseRank (S.stateAt input.initial whole.steps slot) = 4

variable (profile : CampusTCPStartupNative.Profile (input.contextFor .primary)
  (beforeService input (S.stateAt input.initial whole.steps config.startup.preparation.length) .primary)
  input.zone (Handshake.outbound input.active config.startup.remote))

private theorem from_start (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (paths : PathsAligned config profile) (valid : input.passive.Valid) (target : PassiveTarget profile.entry input.passive)
    (initialMonitor : P.Monitor)
    (starting : E.monitorAt config (E.initial config) whole.steps (config.startup.preparation.length + 1) = .startup initialMonitor)
    (startMode : initialMonitor.mode = .drive)
    (unfinished : ¬U.Completed whole (config.startup.preparation.length + 1))
    (within : deadline ≤ whole.steps.length) (completed : U.Completed whole deadline) :
    Nonempty (Found config whole deadline) := by
  have search : ∀ deadline, deadline ≤ whole.steps.length → U.Completed whole deadline → Nonempty (Found config whole deadline) := by
    intro deadline
    induction deadline with
    | zero =>
      intro _ complete
      exact False.elim (unfinished (complete.mono (Nat.zero_le _)))
    | succ last ih =>
      intro available complete
      by_cases previous : U.Completed whole last
      · obtain ⟨found⟩ := ih (by omega) previous
        exact ⟨⟨found.slot, Nat.le_trans found.bound (Nat.le_succ last), found.within, found.afterOpening, found.monitor, found.ending, found.drive, found.phase⟩⟩
      · have order : config.startup.preparation.length + 1 ≤ last := by
          by_cases later : config.startup.preparation.length + 1 ≤ last
          · exact later
          · exact False.elim (unfinished (complete.mono (by omega)))
        obtain ⟨monitor, ending, drive⟩ := U.drive_at profile prep actions paths valid target
          (config.startup.preparation.length + 1) initialMonitor starting startMode order (by omega) previous
        obtain ⟨actual, selected, _, _, _⟩ := CampusTCPSchedule.Trace.at whole.trace last (by omega)
        obtain ⟨_, _, next, mode, _⟩ := U.step profile prep actions paths valid target (by omega) monitor ending drive
          (U.incomplete previous (Nat.le_refl last)) actual selected
        have phase : R.phaseRank (S.stateAt input.initial whole.steps (last + 1)) = 4 := by
          obtain ⟨slot, bound, phase⟩ := complete
          have current : slot = last + 1 := by
            by_cases same : slot = last + 1
            · exact same
            · exact False.elim (previous ⟨slot, by omega, phase⟩)
          simpa only [current] using phase
        exact ⟨⟨last + 1, Nat.le_refl _, available, by omega, P.observe config monitor actual, next, mode, phase⟩⟩
  exact search deadline within completed

theorem locate (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (paths : PathsAligned config profile) (valid : input.passive.Valid) (target : PassiveTarget profile.entry input.passive)
    (available : config.startup.preparation.length + 1 < whole.steps.length)
    (within : deadline ≤ whole.steps.length) (completed : U.Completed whole deadline) :
    Nonempty (Found config whole deadline) := by
  obtain ⟨monitor, starting, mode⟩ := CampusTCPStartupDriveEntry.first_drive actions available
  exact from_start profile prep actions paths valid target monitor starting mode
    (first_unfinished prep actions available) within completed

theorem Found.located (found : Found config whole deadline) (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true) :
    Nonempty (CampusTCPStartupCurrentAt.At whole config found.slot found.within profile) :=
  CampusTCPStartupCurrentAt.at_drive profile prep actions found.within found.ending found.drive

end Netlib.Check.CampusTCPStartupFirstComplete
