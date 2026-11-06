import Netlib.Check.CampusTCPRecoveryRoundEvidenceClock
import Netlib.Check.CampusTCPRecoveryRoundDemand
import Netlib.Check.CampusTCPRecoveryRoundRank

/-!
# Actual clock service in the recovery round

The clock guard supplies current time and ACK-ledger conditions.
A waiting sender tick advances toward its stored recovery deadline.
-/

namespace Netlib.Check.CampusTCPRecoveryRoundEvidence

noncomputable section

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPRecoveryRoundPhaseBase (At Anchor)

namespace M
export CampusTCPRecoveryRoundMonitor (Monitor clockAllowed observe clientRecovery)
end M

variable {input : Input} {events : List Event} {report : Report input events}
  {complete : H.Completed input.active input.passive} {request : Request input}
  {initial : Initial report complete request} {native : NativeEnv initial} {quantum : Nat}
  {current : Cut input complete} {monitor : M.Monitor} {actor : Actor} {millis : Nat} {actual : Step input}
  {sentAt retries : Nat} {released : Bool}

structure Clocked (initial : Initial report complete request) (native : NativeEnv initial) (quantum : Nat)
    (current : Cut input complete) (monitor : M.Monitor) (actor : Actor) (millis : Nat) (actual : Step input) where
  move : Move current actual
  event : actual.event = .advanceClock actor millis
  value : CampusTCPTimedClock.ClockStep current.report.final complete current.endpoints actor millis
  actualEq : value.actual = actual
  endpoints : move.after.endpoints = value.after
  placement : At current move.after
  anchor : Anchor initial move.after
  evidence : Evidence initial native quantum move.after monitor
  observed : M.observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) monitor actual = monitor

theorem clock_allowed_fields (current : Cut input complete) (actor : Actor) (millis : Nat)
    (allowed : M.clockAllowed (CampusTCPRecoveryRoundPhaseBase.config initial native quantum)
      current.report.final (.advanceClock actor millis) = true) :
    ∃ recovery, (endpoint current.endpoints actor).recovery = some recovery ∧ recovery.now ≤ millis ∧
      millis ≤ (endpoint current.endpoints actor).now + quantum ∧ Endpoint.AckTimeReady (endpoint current.endpoints actor) millis := by
  have guarded := allowed
  simp only [M.clockAllowed, current.connection, Bool.and_eq_true] at guarded
  obtain ⟨⟨present, rangeChecked⟩, timeChecked⟩ := guarded
  have range := of_decide_eq_true rangeChecked
  have timely := of_decide_eq_true timeChecked
  obtain ⟨recovery, runtime⟩ := Option.isSome_iff_exists.mp present
  refine ⟨recovery, runtime, ?_, range.2, timely⟩
  simpa only [Endpoint.State.now, runtime, Option.map_some, Option.getD_some] using range.1

theorem clock_at (evidence : Evidence initial native quantum current monitor) (actor : Actor) (millis : Nat)
    (allowed : M.clockAllowed (CampusTCPRecoveryRoundPhaseBase.config initial native quantum)
      current.report.final (.advanceClock actor millis) = true) :
    ∃ actual : Step input, Nonempty (Clocked initial native quantum current monitor actor millis actual) := by
  obtain ⟨recovery, runtime, monotone, _, timely⟩ := clock_allowed_fields current actor millis allowed
  have old := evidence.anchor
  obtain ⟨value⟩ := CampusTCPTimedClock.Report.clock_enabled current.report complete current.endpoints current.connection
    actor millis (old.guards actor).recoveryCoherent (old.guards actor).prepared recovery runtime monotone timely
  let report := value.report current.report rfl current.supported current.finished
  let after : Cut input complete := ⟨_, report, value.report_supported current.report rfl current.supported current.finished,
    rfl, value.after, by change value.actual.result.state.connection = _; rw [value.stateEq]⟩
  let move : Move current value.actual := ⟨after, value.beforeEq, value.supported, value.passed, rfl, rfl⟩
  let placement : At current after := ⟨move.retained, value.frame current.connection,
    [value.actual], rfl, by
      intro actual member
      have same := List.mem_singleton.mp member
      exact ⟨actor, millis, same ▸ value.eventEq⟩⟩
  have guards : CampusTCPRoundGuards.Guards after.endpoints := by
    intro receiver
    by_cases selected : receiver = actor
    · subst receiver
      refine ⟨value.selectedCoherent, value.selectedPrepared, ?_⟩
      change (endpoint value.after actor).recovery.isSome = true
      rw [value.selected, Endpoint.clockState, runtime]
      rfl
    · have peer : receiver = actor.other := by cases receiver <;> cases actor <;> simp_all [Actor.other]
      change CampusTCPRoundGuards.Guarded (endpoint value.after receiver)
      rw [peer, value.peer]
      exact old.guards actor.other
  let anchor : Anchor initial after := ⟨guards, old.retained.trans move.retained,
    old.environment.trans placement.frame.environment.symm⟩
  refine ⟨value.actual, ⟨⟨move, value.eventEq, value, rfl, rfl, placement, anchor,
    evidence.clock placement anchor, ?_⟩⟩⟩
  exact CampusTCPRecoveryRoundMonitorFacts.observe_clock _ _ _ value.supported value.passed actor millis value.eventEq

theorem Step.clock (actual : Step input) (evidence : Evidence initial native quantum current monitor)
    (actor : Actor) (millis : Nat) (before : actual.before = current.report.final)
    (event : actual.event = .advanceClock actor millis)
    (allowed : M.clockAllowed (CampusTCPRecoveryRoundPhaseBase.config initial native quantum)
      current.report.final (.advanceClock actor millis) = true) :
    Nonempty (Clocked initial native quantum current monitor actor millis actual) := by
  obtain ⟨chosen, ⟨clocked⟩⟩ := clock_at evidence actor millis allowed
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event chosen actual
    (clocked.move.beforeEq.trans before.symm) (clocked.event.trans event.symm)
  exact ⟨same ▸ clocked⟩

theorem Clocked.selected (clocked : Clocked initial native quantum current monitor actor millis actual) :
    endpoint clocked.move.after.endpoints actor = Endpoint.clockState (endpoint current.endpoints actor) millis := by
  rw [clocked.endpoints]
  exact clocked.value.selected

theorem Clocked.peer (clocked : Clocked initial native quantum current monitor actor millis actual) :
    endpoint clocked.move.after.endpoints actor.other = endpoint current.endpoints actor.other := by
  rw [clocked.endpoints]
  exact clocked.value.peer

theorem Clocked.client_recovery (clocked : Clocked initial native quantum current monitor .client millis actual)
    (runtime : (endpoint current.endpoints .client).recovery = some recovery) :
    M.clientRecovery clocked.move.after.report.final = some { recovery with now := millis } := by
  simp only [M.clientRecovery, clocked.move.after.connection]
  rw [clocked.selected, Endpoint.clockState, runtime]
  rfl

def Waiting.tickTarget (record : Waiting initial current monitor sentAt retries released) (quantum : Nat) : Nat :=
  min (record.live.sender.recovery.now + quantum) (record.live.sender.entry.lastAt + record.live.sender.recovery.rto)

theorem Waiting.tick_allowed (record : Waiting initial current monitor sentAt retries released)
    (native : NativeEnv initial) (quantum : Nat)
    (early : record.live.sender.recovery.now < record.live.sender.entry.lastAt + record.live.sender.recovery.rto) :
    M.clockAllowed (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final
      (.advanceClock .client (record.tickTarget quantum)) = true := by
  have monotone : record.live.sender.recovery.now ≤ record.tickTarget quantum := by
    unfold Waiting.tickTarget
    omega
  have upper : record.tickTarget quantum ≤ record.live.sender.recovery.now + quantum := Nat.min_le_left _ _
  have timely := record.live.sender.ack_time_ready (record.tickTarget quantum)
  simp only [M.clockAllowed, current.connection, record.live.sender.runtime, Option.isSome_some,
    Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, timely⟩
  simpa only [Endpoint.State.now, record.live.sender.runtime, Option.map_some, Option.getD_some] using ⟨monotone, upper⟩

structure Ticked (record : Waiting initial current monitor sentAt retries released) (native : NativeEnv initial)
    (quantum : Nat) (actual : Step input) where
  clocked : Clocked initial native quantum current monitor .client (record.tickTarget quantum) actual
  next : Waiting initial clocked.move.after monitor sentAt retries released
  recovery : M.clientRecovery clocked.move.after.report.final =
    some { record.live.sender.recovery with now := record.tickTarget quantum }
  decreases : monitor.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) clocked.move.after.report.final <
    monitor.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final

theorem Waiting.tick_at (record : Waiting initial current monitor sentAt retries released)
    (native : NativeEnv initial) (quantum : Nat) (positive : 0 < quantum)
    (early : record.live.sender.recovery.now < record.live.sender.entry.lastAt + record.live.sender.recovery.rto) :
    ∃ actual : Step input, Nonempty (Ticked record native quantum actual) := by
  obtain ⟨actual, ⟨clocked⟩⟩ := clock_at (.waiting record) .client (record.tickTarget quantum)
    (record.tick_allowed native quantum early)
  have updated := clocked.client_recovery record.live.sender.runtime
  refine ⟨actual, ⟨⟨clocked, record.clock clocked.placement clocked.anchor, updated, ?_⟩⟩⟩
  exact CampusTCPRecoveryRoundMonitor.rank_tick (CampusTCPRecoveryRoundPhaseBase.config initial native quantum)
    positive current.report.final clocked.move.after.report.final monitor record.waiting record.live.sender.recovery
    record.recovery record.live.sender.deadline early updated

end

end Netlib.Check.CampusTCPRecoveryRoundEvidence
