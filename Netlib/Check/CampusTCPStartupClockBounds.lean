import Netlib.Check.CampusTCPRecoveryEventFacts
import Netlib.Check.CampusTCPStartupTimerBounds
import Netlib.Check.CampusTCPSchedule
import Netlib.Check.TCPHandshakeRecoveryClockBoundsFacts

/-!
# Startup clocks from actual campus clock inputs

The report retains the same control projection and archive.
Each bounded clock input adds at most one quantum to its endpoint clock.
-/

namespace Netlib.Check.CampusTCPStartupClockBounds

open Protocol.TCP CampusTCPModel

namespace R
export TCPHandshakeRecovery (ClockGuard)
end R

variable {input : Input} {events : List Event} {report : Report input events}
variable {current : C.State input.active input.passive} {archive : RecoveryArchive input.active input.passive}

def ClockGuard (quantum : Nat) (state : State input) (event : Event) : Prop :=
  match state.connection, event with
  | .recovering current, .startupClock actor millis => millis ≤ (current.timer actor.recoverySide).now + quantum
  | _, _ => True

def Actions (quantum : Nat) (steps : List (Step input)) : Prop :=
  ∀ actual ∈ steps, ClockGuard quantum actual.before actual.event

theorem Actions.take (actions : Actions quantum steps) (count : Nat) : Actions quantum (steps.take count) :=
  fun actual member => actions actual (List.mem_of_mem_take member)

theorem Trace.actions_iff (trace : Trace input initial events steps final remaining) :
    Actions quantum steps ↔ ∀ slot, slot < steps.length →
      ClockGuard quantum (CampusTCPSchedule.stateAt initial steps slot) (CampusTCPSchedule.eventAt steps slot) := by
  constructor
  · intro actions slot within
    obtain ⟨actual, selected, before, event, after⟩ := CampusTCPSchedule.Trace.at trace slot within
    simpa only [← before, ← event] using actions actual (List.mem_of_getElem? selected)
  · intro guards actual member
    obtain ⟨slot, selected⟩ := List.mem_iff_getElem?.mp member
    have within := (List.getElem?_eq_some_iff.mp selected).1
    obtain ⟨same, found, before, event, after⟩ := CampusTCPSchedule.Trace.at trace slot within
    have equal : same = actual := Option.some.inj (found.symm.trans selected)
    subst same
    simpa only [← before, ← event] using guards slot within

private theorem clock_event (relation : CampusTCPRecoveryReceipts.RecoveryEvent event (.advanceClock side millis)) :
    ∃ actor, event = .startupClock actor millis ∧ actor.recoverySide = side := by
  cases relation with
  | clock actor millis => exact ⟨actor, rfl, rfl⟩

theorem Step.projected_clock_guard (actual : Step input) (control : C.Step input.active input.passive)
    (recorded : actual.result.recovery = some control) (guard : ClockGuard quantum actual.before actual.event) :
    R.ClockGuard control.before control.event quantum := by
  cases event : control.event with
  | activeOpen remote policy | receive source bytes path policy | timeout actor generation policy => trivial
  | advanceClock side millis =>
    have relation := CampusTCPRecoveryEventFacts.Step.recovery_event actual recorded
    rw [event] at relation
    obtain ⟨actor, selected, sideEq⟩ := clock_event relation
    have connected := CampusTCPRecoveryEventFacts.Step.recovery_clock_before actual recorded selected
    change millis ≤ (control.before.timer side).now + quantum
    rw [← sideEq]
    simpa only [ClockGuard, selected, connected] using guard

theorem Report.projected_clock_guards (report : Report input events) (actions : Actions quantum report.steps) :
    ∀ control ∈ report.steps.filterMap (·.result.recovery), R.ClockGuard control.before control.event quantum := by
  intro control member
  obtain ⟨actual, stored, recorded⟩ := List.mem_filterMap.mp member
  exact Step.projected_clock_guard actual control recorded (actions actual stored)

theorem Report.recovering_clock_le (report : Report input events) (actions : Actions quantum report.steps)
    (connected : report.final.connection = .recovering current) (actor : Actor) :
    (current.timer actor.recoverySide).now ≤ quantum * report.steps.length := by
  have bounded := (CampusTCPRecoveryStartupOrigins.Report.recovery_trace report connected).initial_clock_le
    (Report.projected_clock_guards report actions) actor.recoverySide
  exact Nat.le_trans bounded (Nat.mul_le_mul_left quantum (List.length_filterMap_le _ _))

theorem Report.archive_clock_le (report : Report input events) (actions : Actions quantum report.steps)
    (present : report.final.recoveryArchive = some archive) (actor : Actor) :
    (archive.current.timer actor.recoverySide).now ≤ quantum * report.steps.length := by
  have bounded := (CampusTCPRecoveryStartupOrigins.Report.archive_trace report present).initial_clock_le
    (Report.projected_clock_guards report actions) actor.recoverySide
  exact Nat.le_trans bounded (Nat.mul_le_mul_left quantum (List.length_filterMap_le _ _))

theorem Report.recovering_clock_at (report : Report input events) (actions : Actions quantum report.steps)
    (within : slot ≤ report.steps.length)
    (connected : (CampusTCPSchedule.stateAt input.initial report.steps slot).connection = .recovering current) (actor : Actor) :
    (current.timer actor.recoverySide).now ≤ quantum * slot := by
  have bounded := Report.recovering_clock_le (CampusTCPSchedule.Report.cut report slot within) (actions.take slot) connected actor
  simpa only [CampusTCPSchedule.Report.cut, List.length_take, Nat.min_eq_left within] using bounded

theorem Report.archive_clock_at (report : Report input events) (actions : Actions quantum report.steps)
    (within : slot ≤ report.steps.length)
    (present : (CampusTCPSchedule.stateAt input.initial report.steps slot).recoveryArchive = some archive) (actor : Actor) :
    (archive.current.timer actor.recoverySide).now ≤ quantum * slot := by
  have bounded := Report.archive_clock_le (CampusTCPSchedule.Report.cut report slot within) (actions.take slot) present actor
  simpa only [CampusTCPSchedule.Report.cut, List.length_take, Nat.min_eq_left within] using bounded

theorem Report.recovering_interval (report : Report input events) (actions : Actions quantum report.steps)
    (connected : report.final.connection = .recovering current) (actor : Actor) :
    (current.timer actor.recoverySide).rto ≤ HandshakeTimer.clockEnvelope (quantum * report.steps.length) := by
  exact Nat.le_trans
    ((CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connected).timer_interval actor.recoverySide)
    (HandshakeTimer.clockEnvelope_mono (Report.recovering_clock_le report actions connected actor))

theorem Report.archive_handoff_bounds (report : Report input events) (actions : Actions quantum report.steps)
    (present : report.final.recoveryArchive = some archive) (actor : Actor) :
    (archive.data actor).now ≤ quantum * report.steps.length ∧
      (archive.data actor).rto ≤ max 3000 (HandshakeTimer.clockEnvelope (quantum * report.steps.length)) ∧
      ((archive.data actor).estimator = none ∨ ∃ sample, sample ≤ quantum * report.steps.length ∧
        (archive.data actor).estimator = some (RTO.observe none sample)) := by
  obtain ⟨clock, interval, estimator⟩ := CampusTCPStartupTimerBounds.Report.archive_handoff_bounds report present actor
  have bounded : (archive.data actor).now ≤ quantum * report.steps.length := by
    rw [clock]
    exact Report.archive_clock_le report actions present actor
  refine ⟨bounded, Nat.le_trans interval (Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans
    (HandshakeTimer.clockEnvelope_mono bounded) (Nat.le_max_right _ _)⟩), ?_⟩
  rcases estimator with absent | ⟨sample, before, selected⟩
  · exact Or.inl absent
  · exact Or.inr ⟨sample, Nat.le_trans before bounded, selected⟩

end Netlib.Check.CampusTCPStartupClockBounds
