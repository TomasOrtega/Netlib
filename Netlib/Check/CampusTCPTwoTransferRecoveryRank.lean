import Netlib.Check.CampusTCPTwoTransferEvidence
import Netlib.Check.CampusTCPTwoProgressRecoveryRank
import Netlib.Check.CampusTCPTwoProgressRecoveryBounds

namespace Netlib.Check.CampusTCPTwoTransferRecoveryRank

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferEvidence (Evidence)
open CampusTCPTwoTransferPhaseState (Active)
open CampusTCPTwoTransferWork (AckWork AckState)

namespace K
export CampusTCPTwoProgressRecoveryRank (WorkShape RankShape timerSlots)
end K
namespace M
export CampusTCPTwoProgressMonitor (Config Monitor Lane Demand nextDemand laneDemand timerDemand timerTarget)
end M
namespace W
export CampusTCPTwoTransferMonitor (Config Monitor nextDemand controlDemand drainTicket)
end W

def rank (cfg : W.Config) (bound allowance : Nat) (state : State input) (monitor : W.Monitor) : Nat :=
  CampusTCPTwoProgressRecoveryRank.rank cfg.exchange.forward bound allowance state monitor.exchange.forward

def boundSlots (cfg : W.Config) (capacity allowance : Nat) : Nat :=
  CampusTCPTwoProgressTimer.waitSlots cfg.exchange.forward.quantum (2 ^ allowance * capacity)

theorem boundSlots_positive (cfg : W.Config) (capacity allowance : Nat)
    (quantum : 0 < cfg.exchange.forward.quantum) (positive : 0 < capacity) : 0 < boundSlots cfg capacity allowance :=
  CampusTCPRecoveryRoundMonitor.waitSlots_positive quantum (Nat.mul_pos (Nat.pow_pos (by decide)) positive)

theorem runtime_at (cfg : W.Config) (state : State input) :
    CampusTCPGapProgressMonitor.senderRecovery (cfg.at state).forward.toConfig state =
      CampusTCPGapProgressMonitor.senderRecovery cfg.exchange.forward.toConfig state := rfl

theorem timerSlots_at (cfg : W.Config) (state : State input) :
    K.timerSlots (cfg.at state).forward state = K.timerSlots cfg.exchange.forward state := rfl

theorem rank_at (cfg : W.Config) (bound allowance : Nat) (state : State input) (monitor : W.Monitor) :
    CampusTCPTwoProgressRecoveryRank.rank (cfg.at state).forward bound allowance state monitor.exchange.forward =
      rank cfg bound allowance state monitor := rfl

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {sent : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

theorem sender_runtime (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received) :
    CampusTCPGapProgressMonitor.senderRecovery (cfg).exchange.forward.toConfig current.report.final =
      some core.live.senderFlight.recovery := by
  have senderEq : (cfg).exchange.forward.sender = sender := rfl
  simp only [CampusTCPGapProgressMonitor.senderRecovery, current.connection, senderEq, core.live.senderFlight.runtime]

theorem sender_now (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received) :
    (endpoint current.endpoints sender).now = core.live.senderFlight.recovery.now := by
  simp only [Endpoint.State.now, core.live.senderFlight.runtime, Option.map_some, Option.getD_some]

theorem retry_bound (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received) :
    monitor.exchange.forward.retries ≤ allowance := Nat.le_trans core.losses.count core.lossBound

theorem target_le (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (target : Nat) (selected : M.timerTarget core.live.senderFlight.recovery = some target) :
    target ≤ core.live.senderFlight.recovery.now + core.live.senderFlight.recovery.rto :=
  CampusTCPTwoProgressRecoveryBounds.target_le _ core.live.senderFlight.clocked core.deadline target selected

theorem remaining_le (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received) :
    CampusTCPTwoProgressTimer.remaining core.live.senderFlight.recovery ≤ core.live.senderFlight.recovery.rto :=
  CampusTCPTwoProgressRecoveryBounds.remaining_le _ core.live.senderFlight.clocked core.deadline

theorem slots_le (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received) :
    K.timerSlots (cfg).exchange.forward current.report.final ≤
      CampusTCPTwoProgressTimer.waitSlots quantum core.live.senderFlight.recovery.rto := by
  rw [CampusTCPTwoProgressRecoveryRank.timerSlots_of_runtime _ _ _ (sender_runtime core)]
  exact CampusTCPTwoProgressRecoveryBounds.slots_le _ _ core.live.senderFlight.clocked core.deadline

theorem active_work_shape (active : Active core) : K.WorkShape monitor.exchange.forward := by
  refine ⟨?_, ?_⟩
  · cases active.retry with
    | done phase => exact .inr (.inr (.inr phase))
    | active _ _ _ _ work =>
      cases work with
      | ingress path _ => exact .inl path.phase
      | ticket path _ _ => exact .inr (.inl path.phase)
      | link path _ _ => exact .inr (.inr (.inl path.phase))
  · intro lane pending
    have work : AckWork checks core.live lane := by simpa only [AckState, pending] using active.ack
    cases work with
    | pending phase _ => exact .inl phase
    | ingress path => exact .inr (.inl path.phase)
    | ticket path _ => exact .inr (.inr (.inl path.phase))
    | link path => exact .inr (.inr (.inr path.phase))

theorem active_rank_shape (active : Active core) (mode : monitor.exchange.forward.mode = .recovery) :
    K.RankShape monitor.exchange.forward := {
  toWorkShape := active_work_shape active
  waiting := active.waiting
  serial := active.serial
  runnable := active.runnable mode }

theorem active_waiting_credit (active : Active core) (waiting : monitor.exchange.forward.waiting = true) :
    monitor.exchange.forward.retries < allowance := active.waiting_credit_current waiting

theorem active_target (active : Active core) : ∃ target, M.timerTarget core.live.senderFlight.recovery = some target := by
  obtain ⟨part, head, rest, selected⟩ := active.current_head
  have armed := core.live.senderFlight.armed active.nonempty
  cases timer : core.live.senderFlight.recovery.deadline with
  | none => rw [timer] at armed; cases armed
  | some deadline =>
    exact ⟨max deadline (head.lastAt + core.live.senderFlight.recovery.rto),
      CampusTCPTwoProgressTimer.target_of_fields (core.live.senderFlight.ledger.trans selected.ledger) timer⟩

theorem evidence_positive (value : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (bound : Nat) (nonoriginal : monitor.exchange.forward.mode ≠ .originals) :
    0 < rank cfg bound allowance current.report.final monitor := by
  rcases value with ⟨sent, received, core, forward, controls, scope, armed, recorded⟩
  cases forward with
  | written state => exact False.elim (nonoriginal state.mode)
  | pending state => exact False.elim (nonoriginal state.mode)
  | active active =>
    have mode := active.mode.resolve_left nonoriginal
    exact CampusTCPTwoProgressRecoveryRank.recovery_positive _ _ _ _ _ mode (active_rank_shape active mode)
      (active_waiting_credit active)
  | readable _ _ mode _ _ _ => simp only [rank, CampusTCPTwoProgressRecoveryRank.rank, mode]; decide

private theorem lane_pending (packetConfig : M.Config) (state : State input) (localMonitor : M.Monitor) (lane : M.Lane)
    (action : CampusTCPRoundMonitor.Action)
    (present : CampusTCPGapProgressMonitor.nextAction packetConfig.toConfig state lane.toGap = some action) :
    ∃ demand, M.laneDemand packetConfig state localMonitor lane = some demand := by
  unfold M.laneDemand
  rw [present]
  simp only [bind, Option.bind]
  cases packet : CampusTCPGapProgressMonitor.packetAt lane.toGap with
  | none => exact ⟨.operation action, rfl⟩
  | some id =>
    by_cases budget : localMonitor.drops.length < packetConfig.lossAllowance
    · exact ⟨.resolution action id, by dsimp only; rw [ite_eq_left budget]; rfl⟩
    · exact ⟨.operation action, by dsimp only; rw [ite_eq_right budget]; rfl⟩

theorem active_pending (active : Active core) (mode : monitor.exchange.forward.mode = .recovery) :
    ∃ demand, M.nextDemand ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward = some demand := by
  let packetConfig := ((cfg).at current.report.final).forward
  change ∃ demand, M.nextDemand packetConfig current.report.final monitor.exchange.forward = some demand
  cases ack : monitor.exchange.forward.ack with
  | some lane =>
    have work : AckWork checks core.live lane := by simpa only [AckState, ack] using active.ack
    obtain ⟨demand, selected⟩ := lane_pending packetConfig current.report.final monitor.exchange.forward lane _ (work.command_next packetConfig)
    exact ⟨.single demand, by simp only [M.nextDemand, mode, ack, selected, Option.map_some]⟩
  | none =>
    cases waiting : monitor.exchange.forward.waiting with
    | false =>
      have runnable := active.runnable mode waiting ack
      cases active.retry with
      | done phase => exact False.elim (runnable phase)
      | active _ _ _ _ work =>
        obtain ⟨demand, selected⟩ := lane_pending packetConfig current.report.final monitor.exchange.forward _ _ (work.command_next packetConfig)
        exact ⟨.single demand, by simp only [M.nextDemand, mode, ack, waiting, Bool.false_eq_true, ite_false, selected, Option.map_some]⟩
    | true =>
      obtain ⟨target, selected⟩ := active_target active
      have runtime : CampusTCPGapProgressMonitor.senderRecovery packetConfig.toConfig current.report.final =
          some core.live.senderFlight.recovery := sender_runtime core
      have demand := CampusTCPTwoProgressTimer.timerDemand_of_target runtime selected
      exact ⟨.single _, by simp only [M.nextDemand, mode, ack, waiting, ite_true, demand, Option.map_some]; rfl⟩

theorem pending (value : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (nonoriginal : monitor.exchange.forward.mode ≠ .originals) :
    ∃ demand, W.nextDemand cfg current.report.final monitor = some demand := by
  have finished := value.nonoriginal_finished nonoriginal
  have control : W.controlDemand monitor = none := by rw [W.controlDemand, finished]
  have drained := CampusTCPTwoTransferControlObserve.noDrain_of_non_capture current.report.final monitor (by rw [finished]; decide)
  have valid := value.healthy
  simp only [W.nextDemand, valid, decide_false, Bool.false_eq_true, ite_false, drained, control,
    CampusTCPTwoExchangeMonitor.nextDemand, value.forward.exchange]
  rcases value with ⟨sent, received, core, forward, controls, scope, armed, recorded⟩
  cases forward with
  | written state => exact False.elim (nonoriginal state.mode)
  | pending state => exact False.elim (nonoriginal state.mode)
  | active active =>
    obtain ⟨demand, selected⟩ := active_pending active (active.mode.resolve_left nonoriginal)
    exact ⟨.exchange (.forward demand), by rw [selected]; rfl⟩
  | readable _ _ mode _ _ _ =>
    exact ⟨.exchange (.forward (.single (.operation (.read sender.other (lower ++ upper).length)))), by
      simp only [M.nextDemand, mode]; rfl⟩

end Netlib.Check.CampusTCPTwoTransferRecoveryRank
