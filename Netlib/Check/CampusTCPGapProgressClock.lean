import Netlib.Check.CampusTCPGapProgressPhaseBase
import Netlib.Check.CampusTCPGapProgressMonitor

/-!
# Actual guarded clock moves for held-gap progress

Each clock result belongs to the same stored report.
The monitor retains its current packet and operation references.
-/

namespace Netlib.Check.CampusTCPGapProgressClock

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundGuards
open CampusTCPRound (Cut)
open CampusTCPGapProgressPhaseBase (Anchor Move At)
namespace M
export CampusTCPGapProgressMonitor (Config Monitor clockAllowed observe senderRecovery)
end M

variable {input : Input} {complete : H.Completed input.active input.passive}
  {initial current : Cut input complete} {config : M.Config} {monitor : M.Monitor}
  {actor : Actor} {millis : Nat} {actual : Step input}

theorem clock_allowed_fields (config : M.Config) (current : Cut input complete) (actor : Actor) (millis : Nat)
    (allowed : M.clockAllowed config current.report.final (.advanceClock actor millis) = true) :
    ∃ recovery, (endpoint current.endpoints actor).recovery = some recovery ∧ recovery.now ≤ millis ∧
      millis ≤ (endpoint current.endpoints actor).now + config.quantum ∧
      Endpoint.AckTimeReady (endpoint current.endpoints actor) millis := by
  have guarded := allowed
  simp only [M.clockAllowed, CampusTCPRecoveryRoundMonitor.clockAllowed, current.connection, Bool.and_eq_true] at guarded
  obtain ⟨⟨present, checked⟩, timeChecked⟩ := guarded
  have range := of_decide_eq_true checked
  obtain ⟨recovery, runtime⟩ := Option.isSome_iff_exists.mp present
  refine ⟨recovery, runtime, ?_, range.2, of_decide_eq_true timeChecked⟩
  simpa only [Endpoint.State.now, runtime, Option.map_some, Option.getD_some] using range.1

structure Clocked (initial current : Cut input complete) (config : M.Config) (monitor : M.Monitor)
    (actor : Actor) (millis : Nat) (actual : Step input) where
  move : Move current actual
  event : actual.event = .advanceClock actor millis
  value : CampusTCPTimedClock.ClockStep current.report.final complete current.endpoints actor millis
  actualEq : value.actual = actual
  endpoints : move.after.endpoints = value.after
  placement : At current move.after
  anchor : Anchor initial move.after
  observed : M.observe config monitor actual = monitor

theorem clock_at (anchor : Anchor initial current) (config : M.Config) (monitor : M.Monitor)
    (actor : Actor) (millis : Nat)
    (allowed : M.clockAllowed config current.report.final (.advanceClock actor millis) = true) :
    ∃ actual : Step input, Nonempty (Clocked initial current config monitor actor millis actual) := by
  obtain ⟨recovery, runtime, monotone, _, timely⟩ := clock_allowed_fields config current actor millis allowed
  obtain ⟨value⟩ := CampusTCPTimedClock.Report.clock_enabled current.report complete current.endpoints current.connection
    actor millis (anchor.guards actor).recoveryCoherent (anchor.guards actor).prepared recovery runtime monotone timely
  let report := value.report current.report rfl current.supported current.finished
  let after : Cut input complete := ⟨_, report, value.report_supported current.report rfl current.supported current.finished,
    rfl, value.after, by change value.actual.result.state.connection = _; rw [value.stateEq]⟩
  let move : Move current value.actual := ⟨after, value.beforeEq, value.supported, value.passed, rfl, rfl⟩
  let placement : At current after := ⟨move.retained, value.frame current.connection,
    [value.actual], rfl, by
      intro selected member
      have same := List.mem_singleton.mp member
      exact ⟨actor, millis, same ▸ value.eventEq⟩⟩
  have guards : Guards after.endpoints := by
    intro receiver
    by_cases selected : receiver = actor
    · subst receiver
      refine ⟨value.selectedCoherent, value.selectedPrepared, ?_⟩
      change (endpoint value.after actor).recovery.isSome = true
      rw [value.selected, Endpoint.clockState, runtime]
      rfl
    · have peer : receiver = actor.other := by cases receiver <;> cases actor <;> simp_all [Actor.other]
      change Guarded (endpoint value.after receiver)
      rw [peer, value.peer]
      exact anchor.guards actor.other
  let nextAnchor : Anchor initial after := ⟨guards, anchor.retained.trans move.retained,
    anchor.environment.trans placement.frame.environment.symm⟩
  refine ⟨value.actual, ⟨⟨move, value.eventEq, value, rfl, rfl, placement, nextAnchor, ?_⟩⟩⟩
  simp only [M.observe, value.supported, value.passed, Bool.and_self, value.eventEq, ite_true]

theorem Step.clock (actual : Step input) (anchor : Anchor initial current) (config : M.Config) (monitor : M.Monitor)
    (actor : Actor) (millis : Nat) (before : actual.before = current.report.final)
    (event : actual.event = .advanceClock actor millis)
    (allowed : M.clockAllowed config current.report.final (.advanceClock actor millis) = true) :
    Nonempty (Clocked initial current config monitor actor millis actual) := by
  obtain ⟨selected, ⟨clocked⟩⟩ := clock_at anchor config monitor actor millis allowed
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event selected actual
    (clocked.move.beforeEq.trans before.symm) (clocked.event.trans event.symm)
  exact ⟨same ▸ clocked⟩

theorem Clocked.selected (clocked : Clocked initial current config monitor actor millis actual) :
    endpoint clocked.move.after.endpoints actor = Endpoint.clockState (endpoint current.endpoints actor) millis := by
  rw [clocked.endpoints]
  exact clocked.value.selected

theorem Clocked.peer (clocked : Clocked initial current config monitor actor millis actual) :
    endpoint clocked.move.after.endpoints actor.other = endpoint current.endpoints actor.other := by
  rw [clocked.endpoints]
  exact clocked.value.peer

theorem Clocked.sender_recovery (clocked : Clocked initial current config monitor actor millis actual)
    (sender : config.sender = actor) (runtime : (endpoint current.endpoints actor).recovery = some recovery) :
    M.senderRecovery config clocked.move.after.report.final = some { recovery with now := millis } := by
  simp only [M.senderRecovery, clocked.move.after.connection, sender]
  rw [clocked.selected, Endpoint.clockState, runtime]
  rfl

end Netlib.Check.CampusTCPGapProgressClock
