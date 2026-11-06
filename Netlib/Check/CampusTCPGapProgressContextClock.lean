import Netlib.Check.CampusTCPGapProgressClock
import Netlib.Check.CampusTCPGapProgressEvidenceClock
import Netlib.Check.CampusTCPGapProgressDemand
import Netlib.Check.CampusTCPGapProgressRank

/-!
# Current phase evidence through actual clock service

A full waiting tick advances the actual sender timer.
The stored packet references and selected loss log stay fixed.
-/

namespace Netlib.Check.CampusTCPGapProgressEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPGapProgressStart (GapInitial NativeEnv)
open CampusTCPGapProgressSetup (config)
namespace C
export CampusTCPGapProgressClock (Clocked clock_allowed_fields)
end C
namespace O
export CampusTCPGapProgressMonitor (clockAllowed senderRecovery)
end O

variable {input : Input} {complete : H.Completed input.active input.passive}
  {cut current : Cut input complete} {sender : Actor} {lower upper : List UInt8}
  {initial : GapInitial cut sender lower upper} {native : NativeEnv cut initial.gateway.seed.entry}
  {quantum allowance : Nat} {monitor : CampusTCPGapProgressMonitor.Monitor}
  {actor : Actor} {millis : Nat} {actual : Step input} {retries : Nat} {released : Bool}

structure Clocked (initial : GapInitial cut sender lower upper) (native : NativeEnv cut initial.gateway.seed.entry)
    (quantum allowance : Nat) (current : Cut input complete) (monitor : CampusTCPGapProgressMonitor.Monitor)
    (actor : Actor) (millis : Nat) (actual : Step input)
    extends C.Clocked cut current (config initial native quantum allowance) monitor actor millis actual where
  evidence : Evidence initial native allowance move.after monitor

theorem clock_at (evidence : Evidence initial native allowance current monitor) (quantum : Nat)
    (actor : Actor) (millis : Nat)
    (allowed : O.clockAllowed (config initial native quantum allowance) current.report.final (.advanceClock actor millis) = true) :
    ∃ actual : Step input, Nonempty (Clocked initial native quantum allowance current monitor actor millis actual) := by
  obtain ⟨actual, ⟨clocked⟩⟩ := CampusTCPGapProgressClock.clock_at evidence.anchor
    (config initial native quantum allowance) monitor actor millis allowed
  exact ⟨actual, ⟨clocked, evidence.clock clocked.placement clocked.anchor⟩⟩

theorem Step.clock (actual : Step input) (evidence : Evidence initial native allowance current monitor) (quantum : Nat)
    (actor : Actor) (millis : Nat) (before : actual.before = current.report.final)
    (event : actual.event = .advanceClock actor millis)
    (allowed : O.clockAllowed (config initial native quantum allowance) current.report.final (.advanceClock actor millis) = true) :
    Nonempty (Clocked initial native quantum allowance current monitor actor millis actual) := by
  obtain ⟨chosen, ⟨clocked⟩⟩ := clock_at evidence quantum actor millis allowed
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event chosen actual
    (clocked.move.beforeEq.trans before.symm) (clocked.event.trans event.symm)
  exact ⟨same ▸ clocked⟩

theorem Clocked.selected (clocked : Clocked initial native quantum allowance current monitor actor millis actual) :
    endpoint clocked.move.after.endpoints actor = Endpoint.clockState (endpoint current.endpoints actor) millis :=
  clocked.toClocked.selected

theorem Clocked.peer (clocked : Clocked initial native quantum allowance current monitor actor millis actual) :
    endpoint clocked.move.after.endpoints actor.other = endpoint current.endpoints actor.other := clocked.toClocked.peer

theorem Clocked.sender_recovery (clocked : Clocked initial native quantum allowance current monitor sender millis actual)
    (runtime : (endpoint current.endpoints sender).recovery = some recovery) :
    O.senderRecovery (config initial native quantum allowance) clocked.move.after.report.final = some { recovery with now := millis } :=
  clocked.toClocked.sender_recovery rfl runtime

theorem Waiting.tick_allowed (record : Waiting initial allowance current monitor retries released)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat)
    (early : record.live.senderFlight.recovery.now < record.live.senderFlight.head.lastAt + record.live.senderFlight.recovery.rto) :
    O.clockAllowed (config initial native quantum allowance) current.report.final
      (.advanceClock sender (record.tickTarget quantum)) = true := by
  have monotone : record.live.senderFlight.recovery.now ≤ record.tickTarget quantum := by
    unfold Waiting.tickTarget
    omega
  have upper : record.tickTarget quantum ≤ record.live.senderFlight.recovery.now + quantum := Nat.min_le_left _ _
  have timely := record.live.senderFlight.ack_time_ready (record.tickTarget quantum)
  simp only [O.clockAllowed, CampusTCPRecoveryRoundMonitor.clockAllowed, current.connection,
    record.live.senderFlight.runtime, Option.isSome_some, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, timely⟩
  simpa only [Endpoint.State.now, record.live.senderFlight.runtime, Option.map_some, Option.getD_some, config] using
    And.intro monotone upper

structure Ticked (record : Waiting initial allowance current monitor retries released)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat) (actual : Step input) where
  clocked : Clocked initial native quantum allowance current monitor sender (record.tickTarget quantum) actual
  next : Waiting initial allowance clocked.move.after monitor retries released
  recovery : O.senderRecovery (config initial native quantum allowance) clocked.move.after.report.final =
    some { record.live.senderFlight.recovery with now := record.tickTarget quantum }
  decreases : monitor.rank (config initial native quantum allowance) clocked.move.after.report.final <
    monitor.rank (config initial native quantum allowance) current.report.final

theorem Waiting.tick_at (record : Waiting initial allowance current monitor retries released)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat) (positive : 0 < quantum)
    (early : record.live.senderFlight.recovery.now < record.live.senderFlight.head.lastAt + record.live.senderFlight.recovery.rto) :
    ∃ actual : Step input, Nonempty (Ticked record native quantum actual) := by
  obtain ⟨actual, ⟨clocked⟩⟩ := clock_at (.waiting record) quantum sender (record.tickTarget quantum)
    (record.tick_allowed native quantum early)
  have updated := clocked.sender_recovery record.live.senderFlight.runtime
  have decrease := CampusTCPGapProgressMonitor.rank_tick (config initial native quantum allowance) positive
    current.report.final clocked.move.after.report.final monitor record.waiting record.live.senderFlight.recovery
    (record.recovery native quantum) record.live.senderFlight.deadline early updated
  let next := record.clock clocked.placement clocked.anchor
  exact ⟨actual, ⟨clocked, next, updated, decrease⟩⟩

end Netlib.Check.CampusTCPGapProgressEvidence
