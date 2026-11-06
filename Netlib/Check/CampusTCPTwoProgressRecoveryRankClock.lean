import Netlib.Check.CampusTCPTwoProgressEvidenceRecoveryRank
import Netlib.Check.CampusTCPTwoProgressEvidenceBasic

/-!
# Recovery ranks and demands through actual clocks

Clocks reduce the current wait or retain its rank.
Packet work retains its exact current demand.
-/

namespace Netlib.Check.CampusTCPTwoProgressRecoveryRankClock

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (Core)
open CampusTCPTwoProgressEvidence (Evidence)
open CampusTCPTwoProgressSetup (config)

namespace M
export CampusTCPTwoProgressMonitor (Monitor nextDemand laneDemand observe freeClock)
end M
namespace K
export CampusTCPTwoProgressRecoveryRank (rank timerSlots waitingRank)
end K
namespace G
export CampusTCPGapProgressMonitor (senderRecovery)
end G

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {sent : CampusTCPTwoProgressSender.Stage initial}
variable {received : CampusTCPTwoProgressReceiver.Stage}
variable {actual : Step input} {actor : Actor} {millis : Nat}

private theorem core_clock_slots_le (core : Core initial native quantum allowance current monitor sent received)
    (clocked : CampusTCPTwoProgressClock.Clocked cut current (config initial native quantum allowance) monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance)
      current.report.final monitor (.advanceClock actor millis)) :
    K.timerSlots (config initial native quantum allowance) clocked.move.after.report.final ≤
      K.timerSlots (config initial native quantum allowance) current.report.final := by
  rw [CampusTCPTwoProgressRecoveryRank.timerSlots_of_runtime _ _ _
      (CampusTCPTwoProgressPhaseNormalize.sender_runtime (core.clock clocked allowed)),
    CampusTCPTwoProgressRecoveryRank.timerSlots_of_runtime _ _ _
      (CampusTCPTwoProgressPhaseNormalize.sender_runtime core)]
  exact CampusTCPTwoProgressTimer.clock_slots_le (clocked.placement.frame.endpointFrame sender)
    core.live.senderFlight.runtime (core.clock clocked allowed).live.senderFlight.runtime

theorem clock_nonincrease (value : Evidence initial native quantum allowance current monitor)
    (nonoriginal : monitor.mode ≠ .originals) (bound : Nat)
    (clocked : CampusTCPTwoProgressClock.Clocked cut current (config initial native quantum allowance) monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance)
      current.report.final monitor (.advanceClock actor millis)) :
    K.rank (config initial native quantum allowance) bound allowance clocked.move.after.report.final
      (M.observe (config initial native quantum allowance) monitor actual) ≤
      K.rank (config initial native quantum allowance) bound allowance current.report.final monitor := by
  rw [clocked.observed]
  cases value with
  | written value _ => exact False.elim (nonoriginal value.mode)
  | upper _ value _ => exact False.elim (nonoriginal value.mode)
  | active core active =>
    have mode := active.mode.resolve_left nonoriginal
    rw [K.rank, K.rank, mode]
    cases waiting : monitor.waiting with
    | false => exact Nat.le_refl _
    | true => exact CampusTCPTwoProgressRecoveryRank.waiting_mono _ _ _ (core_clock_slots_le core clocked allowed)
  | ready _ ready => simp only [K.rank, ready.mode, Nat.le_refl]
  | done value => simp only [K.rank, value.mode, Nat.le_refl]

private theorem lane_frame (clocked : CampusTCPTwoProgressClock.Clocked cut current cfg monitor actor millis actual)
    (lane : CampusTCPTwoProgressMonitor.Lane) :
    M.laneDemand cfg clocked.move.after.report.final monitor lane = M.laneDemand cfg current.report.final monitor lane := by
  unfold M.laneDemand
  rw [CampusTCPGapProgressMonitorFacts.Frame.nextAction clocked.placement.frame cfg.toConfig lane.toGap]

theorem nonwaiting_pending (clocked : CampusTCPTwoProgressClock.Clocked cut current cfg monitor actor millis actual)
    (nonoriginal : monitor.mode ≠ .originals) (waiting : monitor.waiting = false) :
    M.nextDemand cfg clocked.move.after.report.final (M.observe cfg monitor actual) = M.nextDemand cfg current.report.final monitor := by
  rw [clocked.observed]
  cases mode : monitor.mode with
  | originals => exact False.elim (nonoriginal mode)
  | recovery =>
    simp only [M.nextDemand, mode]
    cases ack : monitor.ack with
    | none => simp only [waiting, Bool.false_eq_true, ite_false]; rw [lane_frame clocked monitor.retry]
    | some lane => dsimp only; rw [lane_frame clocked lane]
  | needRead | done | invalid => simp only [M.nextDemand, mode]

theorem free_waiting_runtime (core : Core initial native quantum allowance current monitor sent received)
    (clocked : CampusTCPTwoProgressClock.Clocked cut current (config initial native quantum allowance) monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance)
      current.report.final monitor (.advanceClock actor millis))
    (waiting : monitor.waiting = true)
    (free : M.freeClock (config initial native quantum allowance) current.report.final monitor (.advanceClock actor millis) = true) :
    G.senderRecovery (config initial native quantum allowance).toConfig clocked.move.after.report.final =
      G.senderRecovery (config initial native quantum allowance).toConfig current.report.final := by
  have now : (endpoint clocked.move.after.endpoints sender).now = (endpoint current.endpoints sender).now := by
    by_cases same : actor = sender
    · subst actor
      have stamp : millis = (endpoint current.endpoints sender).now := by
        have guarded := free
        have self : (sender != sender) = false := by cases sender <;> rfl
        simp only [M.freeClock, CampusTCPGapProgressMonitor.freeClock, current.connection, config, waiting,
          Bool.not_true, self, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at guarded
        exact guarded.2
      rw [clocked.selected, Endpoint.clockState_now _ _ core.live.senderFlight.runtime, stamp]
    · have other : sender = actor.other := by
        cases actor <;> cases sender <;> first | rfl | exact False.elim (same rfl)
      simpa only [other] using congrArg Endpoint.State.now clocked.peer
  rw [CampusTCPTwoProgressPhaseNormalize.sender_runtime (core.clock clocked allowed),
    CampusTCPTwoProgressPhaseNormalize.sender_runtime core]
  congr 1
  rw [CampusTCPTwoProgressPhaseState.clock_sender_recovery core clocked allowed, now]
  have time : (endpoint current.endpoints sender).now = core.live.senderFlight.recovery.now := by
    simp only [Endpoint.State.now, core.live.senderFlight.runtime, Option.map_some, Option.getD_some]
  rw [time]

theorem free_waiting_pending (core : Core initial native quantum allowance current monitor sent received)
    (clocked : CampusTCPTwoProgressClock.Clocked cut current (config initial native quantum allowance) monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance)
      current.report.final monitor (.advanceClock actor millis))
    (mode : monitor.mode = .recovery) (waiting : monitor.waiting = true) (ack : monitor.ack = none)
    (free : M.freeClock (config initial native quantum allowance) current.report.final monitor (.advanceClock actor millis) = true) :
    M.nextDemand (config initial native quantum allowance) clocked.move.after.report.final
      (M.observe (config initial native quantum allowance) monitor actual) =
      M.nextDemand (config initial native quantum allowance) current.report.final monitor := by
  rw [clocked.observed]
  simp only [M.nextDemand, mode, ack, waiting, ite_true]
  unfold CampusTCPTwoProgressMonitor.timerDemand
  rw [free_waiting_runtime core clocked allowed waiting free]

theorem free_clock_pending (value : Evidence initial native quantum allowance current monitor)
    (nonoriginal : monitor.mode ≠ .originals)
    (clocked : CampusTCPTwoProgressClock.Clocked cut current (config initial native quantum allowance) monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance)
      current.report.final monitor (.advanceClock actor millis))
    (free : M.freeClock (config initial native quantum allowance) current.report.final monitor (.advanceClock actor millis) = true) :
    M.nextDemand (config initial native quantum allowance) clocked.move.after.report.final
      (M.observe (config initial native quantum allowance) monitor actual) =
      M.nextDemand (config initial native quantum allowance) current.report.final monitor := by
  cases value with
  | written value _ => exact False.elim (nonoriginal value.mode)
  | upper _ value _ => exact False.elim (nonoriginal value.mode)
  | active core active =>
    cases waiting : monitor.waiting with
    | false => exact nonwaiting_pending clocked nonoriginal waiting
    | true => exact free_waiting_pending core clocked allowed (active.waiting_mode waiting) waiting (active.waiting waiting).1 free
  | ready _ ready => simp only [clocked.observed, M.nextDemand, ready.mode]
  | done value => simp only [clocked.observed, M.nextDemand, value.mode]

end Netlib.Check.CampusTCPTwoProgressRecoveryRankClock
