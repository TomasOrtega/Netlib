import Netlib.Check.CampusTCPRoundPhaseBase
import Netlib.Check.CampusTCPTimedClock
import Netlib.Check.CampusTCPRecoveryRoundMonitor

/-!
# Actual current cuts in a timed recovery round

Clock suffixes retain each old operation at its actual time.
Current endpoint clocks use their new runtimes.
-/

namespace Netlib.Check.CampusTCPRecoveryRoundPhaseBase

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRound (Cut)
open CampusTCPRoundGuards

open CampusTCPRoundPhaseBase (Move)

variable {input : Input} {events : List Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}
variable {initial : Initial report complete request} {native : NativeEnv initial}

def config (initial : Initial report complete request) (native : NativeEnv initial) (quantum : Nat) :
    CampusTCPRecoveryRoundMonitor.Config :=
  ⟨CampusTCPRoundPhaseBase.config initial native, quantum⟩

structure At (anchor current : Cut input complete) : Prop where
  retained : anchor.report.steps <+: current.report.steps
  frame : CampusTCPTimedClock.Frame anchor.report.final anchor.endpoints current.report.final current.endpoints
  clocks : ∃ extra, current.report.steps = anchor.report.steps ++ extra ∧
    ∀ actual ∈ extra, ∃ actor now, actual.event = .advanceClock actor now

theorem At.refl (cut : Cut input complete) : At cut cut :=
  ⟨List.prefix_refl _, CampusTCPTimedClock.Frame.refl _ _ cut.connection, [], by simp, by simp⟩

theorem At.trans (first : At left middle) (second : At middle right) : At left right :=
  ⟨first.retained.trans second.retained, first.frame.trans second.frame, by
    obtain ⟨before, earlier, firstClocks⟩ := first.clocks
    obtain ⟨after, later, lastClocks⟩ := second.clocks
    refine ⟨before ++ after, ?_, ?_⟩
    · rw [later, earlier, List.append_assoc]
    · intro actual member
      rcases List.mem_append.mp member with old | next
      · exact firstClocks actual old
      · exact lastClocks actual next⟩

theorem At.member (placement : At anchor current) (member : actual ∈ anchor.report.steps) : actual ∈ current.report.steps :=
  placement.retained.subset member

theorem Guarded.clock (guarded : Guarded before) (frame : Endpoint.ClockFrame before after)
    (timely : Endpoint.AckTimeReady before after.now) : Guarded after := by
  have same : after.recovery.isSome = before.recovery.isSome := by
    rw [frame.recovery]
    cases before.recovery <;> rfl
  exact ⟨frame.recovery_coherent guarded.recoveryCoherent,
    frame.ack_prepared guarded.prepared timely, same.trans guarded.runtime⟩

theorem At.clock {anchor current : Cut input complete} (placement : At anchor current) (actual : Step input)
    (before : actual.before = current.report.final) (actor : Actor) (millis : Nat)
    (event : actual.event = .advanceClock actor millis) (guards : Guards current.endpoints)
    (recovery : Recovery.State) (runtime : (endpoint current.endpoints actor).recovery = some recovery)
    (monotone : recovery.now ≤ millis)
    (timely : Endpoint.AckTimeReady (endpoint current.endpoints actor) millis) :
    ∃ move : Move current actual, At anchor move.after ∧ Guards move.after.endpoints := by
  obtain ⟨appended⟩ := CampusTCPTimedClock.Report.append_clock current.report current.supported current.finished
    complete current.endpoints current.connection actual before actor millis event
    (guards actor).recoveryCoherent (guards actor).prepared recovery runtime monotone timely
  let next : Cut input complete := ⟨_, appended.next, appended.supported, appended.finished,
    appended.clock.after, appended.frame.afterConnection⟩
  have supported : actual.result.supported = true := appended.actualEq ▸ appended.clock.supported
  have passed : actual.result.passed = true := appended.actualEq ▸ appended.clock.passed
  let move : Move current actual := ⟨next, before, supported, passed, appended.history, appended.final⟩
  refine ⟨move, ⟨placement.retained.trans move.retained, placement.frame.trans appended.frame, ?_⟩, ?_⟩
  · obtain ⟨extra, history, clocks⟩ := placement.clocks
    refine ⟨extra ++ [actual], ?_, ?_⟩
    · rw [move.history, history, List.append_assoc]
    · intro selected member
      rcases List.mem_append.mp member with old | fresh
      · exact clocks selected old
      · have same : selected = actual := List.mem_singleton.mp fresh
        exact ⟨actor, millis, same ▸ event⟩
  · intro receiver
    by_cases selected : receiver = actor
    · subst receiver
      refine ⟨appended.clock.selectedCoherent, appended.clock.selectedPrepared, ?_⟩
      rw [appended.clock.selected, Endpoint.clockState, runtime]
      rfl
    · have peer : receiver = actor.other := by cases receiver <;> cases actor <;> simp_all [Actor.other]
      change Guarded (endpoint appended.clock.after receiver)
      rw [peer, appended.clock.peer]
      exact guards actor.other

structure Anchor (initial : Initial report complete request) (cut : Cut input complete) : Prop where
  guards : Guards cut.endpoints
  retained : initial.start.next.report.steps <+: cut.report.steps
  environment : CampusTCPRoundEnvironment.environment initial.state =
    CampusTCPRoundEnvironment.environment cut.report.final

theorem Anchor.ofInitial (initial : Initial report complete request) : Anchor initial (Cut.ofPrepared initial.start) :=
  ⟨PreparedStart.guards initial.start, List.prefix_refl _, rfl⟩

theorem Anchor.clock (anchor : Anchor initial current) (actual : Step input)
    (before : actual.before = current.report.final) (actor : Actor) (millis : Nat)
    (event : actual.event = .advanceClock actor millis)
    (recovery : Recovery.State) (runtime : (endpoint current.endpoints actor).recovery = some recovery)
    (monotone : recovery.now ≤ millis)
    (timely : Endpoint.AckTimeReady (endpoint current.endpoints actor) millis) :
    ∃ move : Move current actual, At current move.after ∧ Anchor initial move.after := by
  obtain ⟨move, placement, guards⟩ := (At.refl current).clock actual before actor millis event anchor.guards
    recovery runtime monotone timely
  exact ⟨move, placement, guards, anchor.retained.trans move.retained,
    anchor.environment.trans placement.frame.environment.symm⟩

end Netlib.Check.CampusTCPRecoveryRoundPhaseBase
