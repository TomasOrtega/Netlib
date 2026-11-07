import Netlib.Check.CampusTCPTwoTransferRecoveryRank
import Netlib.Check.CampusTCPTwoTransferHandoffRTO

namespace Netlib.Check.CampusTCPTwoTransferRecoveryRank

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferEvidence (Evidence)
open CampusTCPTwoTransferPhaseState (Active)
open CampusTCPTwoTransferHandoffRTO (PendingCap)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance capacity : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : CampusTCPTwoTransferMonitor.Monitor} {sent : CampusTCPTwoProgressSender.Stage initial}
variable {received : CampusTCPTwoProgressReceiver.Stage}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

theorem core_slots_le (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (cap : PendingCap cfg capacity current.report.final monitor) (pending : sent.ledger ≠ []) :
    K.timerSlots (cfg).exchange.forward current.report.final ≤ boundSlots cfg capacity allowance := by
  have rto := CampusTCPTwoTransferHandoffRTO.at_core core cap pending
  have powers : 2 ^ monitor.exchange.forward.retries * capacity ≤ 2 ^ allowance * capacity :=
    Nat.mul_le_mul_right capacity (Nat.pow_le_pow_of_le (by decide) (retry_bound core))
  exact Nat.le_trans (slots_le core) (CampusTCPRecoveryRoundMonitor.waitSlots_mono (Nat.le_trans rto powers))

theorem active_slots_le (active : Active core) (cap : PendingCap cfg capacity current.report.final monitor) :
    K.timerSlots (cfg).exchange.forward current.report.final ≤ boundSlots cfg capacity allowance :=
  core_slots_le core cap active.nonempty

theorem empty_slots (packetConfig : CampusTCPTwoProgressMonitor.Config) (state : State input) (recovery : Recovery.State)
    (runtime : CampusTCPGapProgressMonitor.senderRecovery packetConfig.toConfig state = some recovery)
    (empty : recovery.outstanding = []) : K.timerSlots packetConfig state = 0 := by
  rw [CampusTCPTwoProgressRecoveryRank.timerSlots_of_runtime _ _ _ runtime]
  have target : CampusTCPTwoProgressMonitor.timerTarget recovery = none := by
    simp only [CampusTCPTwoProgressMonitor.timerTarget, empty, List.head?_nil, bind, Option.bind]
  rw [CampusTCPTwoProgressTimer.slots, CampusTCPTwoProgressTimer.remaining_none target]
  by_cases positive : 0 < packetConfig.quantum
  · exact CampusTCPRecoveryRoundMonitor.waitSlots_zero positive
  · have zero : packetConfig.quantum = 0 := by omega
    change CampusTCPRecoveryRoundMonitor.waitSlots packetConfig.quantum 0 = 0
    rw [zero]
    rfl

theorem evidence_slots_le (value : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (nonoriginal : monitor.exchange.forward.mode ≠ .originals) (cap : PendingCap cfg capacity current.report.final monitor) :
    K.timerSlots (cfg).exchange.forward current.report.final ≤ boundSlots cfg capacity allowance := by
  rcases value with ⟨sent, received, core, forward, controls, scope, armed, recorded⟩
  cases forward with
  | written state => exact False.elim (nonoriginal state.mode)
  | pending state => exact False.elim (nonoriginal state.mode)
  | active active => exact active_slots_le active cap
  | readable core _ _ _ _ _ =>
    rw [empty_slots _ _ _ (sender_runtime core) core.live.senderFlight.ledger]
    exact Nat.zero_le _

theorem evidence_rank_le (value : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (nonoriginal : monitor.exchange.forward.mode ≠ .originals) (cap : PendingCap cfg capacity current.report.final monitor) :
    rank cfg (boundSlots cfg capacity allowance) allowance current.report.final monitor ≤
      (allowance + 1) * boundSlots cfg capacity allowance + 8 * allowance + 7 := by
  rcases value with ⟨sent, received, core, forward, controls, scope, armed, recorded⟩
  cases forward with
  | written state => exact False.elim (nonoriginal state.mode)
  | pending state => exact False.elim (nonoriginal state.mode)
  | active active =>
    exact CampusTCPTwoProgressRecoveryRank.recovery_le _ _ _ _ _ (active.mode.resolve_left nonoriginal)
      (active_work_shape active) (retry_bound core) (active_slots_le active cap)
  | readable _ _ mode _ _ _ => simp only [rank, CampusTCPTwoProgressRecoveryRank.rank, mode]; omega

end Netlib.Check.CampusTCPTwoTransferRecoveryRank
