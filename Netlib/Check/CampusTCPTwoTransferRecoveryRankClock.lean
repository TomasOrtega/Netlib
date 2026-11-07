import Netlib.Check.CampusTCPTwoTransferRecoveryRank
import Netlib.Check.CampusTCPTwoTransferPhaseClock

namespace Netlib.Check.CampusTCPTwoTransferRecoveryRankClock

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferEvidence (Evidence)
open CampusTCPTwoTransferLocatedClock (Clocked)

namespace R
export CampusTCPTwoTransferRecoveryRank (rank sender_runtime sender_now)
end R
namespace K
export CampusTCPTwoProgressRecoveryRank (timerSlots)
end K
namespace M
export CampusTCPTwoProgressMonitor (nextDemand laneDemand freeClock)
end M
namespace W
export CampusTCPTwoTransferMonitor (Monitor Allowed observe nextDemand)
end W

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {sent : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}
variable {actor : Actor} {millis : Nat} {actual : Step input}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

private theorem endpoints_same (first second : Move current actual) : first.after.endpoints = second.after.endpoints := by
  have connected := congrArg State.connection (first.final.trans second.final.symm)
  rw [first.after.connection, second.after.connection] at connected
  exact eq_of_heq (Connection.application.inj connected).2

theorem clock_endpoints (exchange : monitor.exchange.mode = .forward) (clocked : Clocked core actor millis actual)
    (allowed : W.Allowed cfg current.report.final monitor (.advanceClock actor millis)) :
    endpoint clocked.move.after.endpoints actor = Endpoint.clockState (endpoint current.endpoints actor) millis ∧
      endpoint clocked.move.after.endpoints actor.other = endpoint current.endpoints actor.other := by
  have localAllowed := CampusTCPTwoTransferLocatedClock.local_allowed cfg current.report.final monitor exchange allowed
  let anchor := CampusTCPGapProgressPhaseBase.Anchor.refl current core.live.anchor.guards
  obtain ⟨base⟩ := CampusTCPTwoProgressClock.Step.clock actual anchor ((cfg).at current.report.final).forward monitor.exchange.forward
    actor millis clocked.move.beforeEq clocked.event localAllowed
  rw [endpoints_same clocked.move base.move]
  exact ⟨base.selected, base.peer⟩

theorem core_clock_slots_le (clocked : Clocked core actor millis actual) :
    K.timerSlots (cfg).exchange.forward clocked.move.after.report.final ≤
      K.timerSlots (cfg).exchange.forward current.report.final := by
  rw [CampusTCPTwoProgressRecoveryRank.timerSlots_of_runtime _ _ _ (R.sender_runtime clocked.next),
    CampusTCPTwoProgressRecoveryRank.timerSlots_of_runtime _ _ _ (R.sender_runtime core)]
  exact CampusTCPTwoProgressTimer.clock_slots_le (clocked.placement.frame.endpointFrame sender)
    core.live.senderFlight.runtime clocked.next.live.senderFlight.runtime

theorem nonincrease (value : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (nonoriginal : monitor.exchange.forward.mode ≠ .originals) (bound : Nat)
    (clocked : Clocked value.core actor millis actual) :
    R.rank cfg bound allowance clocked.move.after.report.final (W.observe cfg monitor actual) ≤
      R.rank cfg bound allowance current.report.final monitor := by
  rw [clocked.observed]
  rcases value with ⟨sent, received, core, forward, controls, scope, armed, recorded⟩
  cases forward with
  | written state => exact False.elim (nonoriginal state.mode)
  | pending state => exact False.elim (nonoriginal state.mode)
  | active active =>
    have mode := active.mode.resolve_left nonoriginal
    simp only [R.rank, CampusTCPTwoProgressRecoveryRank.rank, mode]
    cases waiting : monitor.exchange.forward.waiting with
    | false => exact Nat.le_refl _
    | true => exact CampusTCPTwoProgressRecoveryRank.waiting_mono _ _ _ (core_clock_slots_le clocked)
  | readable _ _ mode _ _ _ => simp only [R.rank, CampusTCPTwoProgressRecoveryRank.rank, mode, Nat.le_refl]

private theorem lane_frame (clocked : Clocked core actor millis actual) (packetConfig : CampusTCPTwoProgressMonitor.Config)
    (lane : CampusTCPTwoProgressMonitor.Lane) :
    M.laneDemand packetConfig clocked.move.after.report.final monitor.exchange.forward lane =
      M.laneDemand packetConfig current.report.final monitor.exchange.forward lane := by
  unfold M.laneDemand
  rw [CampusTCPGapProgressMonitorFacts.Frame.nextAction clocked.placement.frame packetConfig.toConfig lane.toGap]

private theorem nonwaiting_local (clocked : Clocked core actor millis actual) (packetConfig : CampusTCPTwoProgressMonitor.Config)
    (nonoriginal : monitor.exchange.forward.mode ≠ .originals) (waiting : monitor.exchange.forward.waiting = false) :
    M.nextDemand packetConfig clocked.move.after.report.final monitor.exchange.forward =
      M.nextDemand packetConfig current.report.final monitor.exchange.forward := by
  cases mode : monitor.exchange.forward.mode with
  | originals => exact False.elim (nonoriginal mode)
  | recovery =>
    simp only [M.nextDemand, mode]
    cases ack : monitor.exchange.forward.ack with
    | none => simp only [waiting, Bool.false_eq_true, ite_false]; rw [lane_frame clocked packetConfig monitor.exchange.forward.retry]
    | some lane => dsimp only; rw [lane_frame clocked packetConfig lane]
  | needRead | done | invalid => simp only [M.nextDemand, mode]

theorem free_waiting_runtime (exchange : monitor.exchange.mode = .forward) (clocked : Clocked core actor millis actual)
    (allowed : W.Allowed cfg current.report.final monitor (.advanceClock actor millis))
    (waiting : monitor.exchange.forward.waiting = true)
    (free : M.freeClock ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward (.advanceClock actor millis) = true) :
    CampusTCPGapProgressMonitor.senderRecovery (cfg).exchange.forward.toConfig clocked.move.after.report.final =
      CampusTCPGapProgressMonitor.senderRecovery (cfg).exchange.forward.toConfig current.report.final := by
  have endpointFields := clock_endpoints exchange clocked allowed
  have now : (endpoint clocked.move.after.endpoints sender).now = (endpoint current.endpoints sender).now := by
    by_cases same : actor = sender
    · subst actor
      have stamp : millis = (endpoint current.endpoints sender).now := by
        have guarded := free
        have self : (sender != sender) = false := by cases sender <;> rfl
        simp only [M.freeClock, CampusTCPGapProgressMonitor.freeClock, current.connection, config,
          CampusTCPTwoTransferNative.Checks.monitorConfig, CampusTCPTwoTransferMonitor.Config.at,
          CampusTCPTwoExchangeSetup.config, CampusTCPTwoProgressSetup.config, waiting,
          Bool.not_true, self, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at guarded
        exact guarded.2
      rw [endpointFields.1, Endpoint.clockState_now _ _ core.live.senderFlight.runtime, stamp]
    · have other : sender = actor.other := by cases actor <;> cases sender <;> first | rfl | exact False.elim (same rfl)
      simpa only [other] using congrArg Endpoint.State.now endpointFields.2
  rw [R.sender_runtime clocked.next, R.sender_runtime core]
  congr 1
  rw [CampusTCPTwoTransferPhaseState.clock_sender_recovery clocked, now, R.sender_now core]

private theorem lift_pending (value : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (nonoriginal : monitor.exchange.forward.mode ≠ .originals) (clocked : Clocked value.core actor millis actual)
    (same : M.nextDemand ((cfg).at current.report.final).forward clocked.move.after.report.final monitor.exchange.forward =
      M.nextDemand ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward) :
    W.nextDemand cfg clocked.move.after.report.final (W.observe cfg monitor actual) = W.nextDemand cfg current.report.final monitor := by
  have finished := value.nonoriginal_finished nonoriginal
  have configuration : (cfg).at clocked.move.after.report.final = (cfg).at current.report.final := by
    simp only [CampusTCPTwoTransferMonitor.Config.at, State.owner, clocked.placement.frame.owners]
  have drained := CampusTCPTwoTransferControlObserve.noDrain_of_non_capture current.report.final monitor (by rw [finished]; decide)
  have afterDrain := CampusTCPTwoTransferControlObserve.noDrain_of_non_capture clocked.move.after.report.final
    (W.observe cfg monitor actual) (by rw [clocked.observed]; exact (by rw [finished]; decide))
  unfold W.nextDemand
  rw [afterDrain, drained]
  simp only [clocked.observed, finished, reduceCtorEq, decide_false, Bool.false_eq_true, ite_false,
    CampusTCPTwoTransferMonitor.controlDemand, CampusTCPTwoExchangeMonitor.nextDemand,
    value.forward.exchange, configuration, same]

theorem free_pending (value : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (nonoriginal : monitor.exchange.forward.mode ≠ .originals) (clocked : Clocked value.core actor millis actual)
    (allowed : W.Allowed cfg current.report.final monitor (.advanceClock actor millis))
    (free : M.freeClock ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward (.advanceClock actor millis) = true) :
    W.nextDemand cfg clocked.move.after.report.final (W.observe cfg monitor actual) = W.nextDemand cfg current.report.final monitor := by
  apply lift_pending value nonoriginal clocked
  rcases value with ⟨sent, received, core, forward, controls, scope, armed, recorded⟩
  cases forward with
  | written state => exact False.elim (nonoriginal state.mode)
  | pending state => exact False.elim (nonoriginal state.mode)
  | active active =>
    cases waiting : monitor.exchange.forward.waiting with
    | false => exact nonwaiting_local clocked _ nonoriginal waiting
    | true =>
      simp only [M.nextDemand, active.waiting_mode waiting, (active.waiting waiting).1, waiting, ite_true]
      unfold CampusTCPTwoProgressMonitor.timerDemand
      have runtimeAfter : CampusTCPGapProgressMonitor.senderRecovery ((cfg).at current.report.final).forward.toConfig
          clocked.move.after.report.final = CampusTCPGapProgressMonitor.senderRecovery (cfg).exchange.forward.toConfig
          clocked.move.after.report.final := rfl
      rw [runtimeAfter, CampusTCPTwoTransferRecoveryRank.runtime_at,
        free_waiting_runtime active.exchange clocked allowed waiting free]
  | readable _ _ mode _ _ _ => simp only [M.nextDemand, mode]

end Netlib.Check.CampusTCPTwoTransferRecoveryRankClock
