import Netlib.Check.CampusTCPTwoProgressRecoveryRank
import Netlib.Check.CampusTCPTwoProgressRecoveryCap
import Netlib.Check.CampusTCPTwoProgressTimerInvariant

namespace Netlib.Check.CampusTCPTwoProgressEvidenceRecoveryRank

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressPhaseBase
open CampusTCPTwoProgressPhaseState
open CampusTCPTwoProgressSetup (config)
open CampusTCPTwoProgressEvidence (Evidence)
open CampusTCPTwoProgressRecoveryCap (PendingCap)

namespace K
export CampusTCPTwoProgressRecoveryRank (WorkShape RankShape timerSlots rank)
end K
namespace S
export CampusTCPTwoProgressSender (Stage Part)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R

def boundSlots (cfg : CampusTCPTwoProgressMonitor.Config) (capacity allowance : Nat) : Nat :=
  CampusTCPTwoProgressTimer.waitSlots cfg.quantum (2 ^ allowance * capacity)

theorem boundSlots_positive (cfg : CampusTCPTwoProgressMonitor.Config) (capacity allowance : Nat)
    (quantum : 0 < cfg.quantum) (positive : 0 < capacity) : 0 < boundSlots cfg capacity allowance :=
  CampusTCPRecoveryRoundMonitor.waitSlots_positive quantum (Nat.mul_pos (Nat.pow_pos (by decide)) positive)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance capacity : Nat}
variable {monitor : CampusTCPTwoProgressMonitor.Monitor} {sent : S.Stage initial} {received : R.Stage}
variable {core : Core initial native quantum allowance current monitor sent received}

theorem handoff_cap_positive (initial : TwoWriteInitial cut sender gateway lower upper) (span : Nat) :
    0 < CampusTCPTwoProgressHandoffRTO.cap initial span := by
  have floor := RTOEnvelope.cap_floor initial.senderState.idle.recovery.rto initial.senderState.idle.recovery.estimator span
  change 1000 ≤ CampusTCPTwoProgressHandoffRTO.cap initial span at floor
  omega

theorem active_work_shape (active : Active core) : K.WorkShape monitor := by
  refine ⟨?_, ?_⟩
  · cases active.retry with
    | done phase => exact .inr (.inr (.inr phase))
    | active _ _ _ _ work =>
      cases work with
      | ingress path _ => exact .inl path.phase
      | ticket path _ => exact .inr (.inl path.phase)
      | link path _ _ => exact .inr (.inr (.inl path.phase))
  · intro lane pending
    have work : AckWork core lane := by simpa only [AckState, pending] using active.ack
    cases work with
    | pending phase _ => exact .inl phase
    | ingress path => exact .inr (.inl path.phase)
    | ticket path => exact .inr (.inr (.inl path.phase))
    | link path => exact .inr (.inr (.inr path.phase))

theorem active_rank_shape (active : Active core) (mode : monitor.mode = .recovery) : K.RankShape monitor := {
  toWorkShape := active_work_shape active
  waiting := active.waiting
  serial := active.serial
  runnable := active.runnable mode }

theorem active_waiting_credit (active : Active core) (waiting : monitor.waiting = true) : monitor.retries < allowance := by
  cases sent with
  | written => cases active.preparing
  | lower first => cases active.preparing
  | both first second head => exact active.waiting_credit waiting .lower head [second.entry] (.lower first second head)
  | tail first second head => exact active.waiting_credit waiting .upper head [] (.upper first second head)
  | retired first second => exact False.elim (active.nonempty rfl)

theorem evidence_positive (value : Evidence initial native quantum allowance current monitor) (bound : Nat)
    (nonoriginal : monitor.mode ≠ .originals) (nondone : monitor.mode ≠ .done) :
    0 < K.rank (config initial native quantum allowance) bound allowance current.report.final monitor := by
  cases value with
  | written value _ => exact False.elim (nonoriginal value.mode)
  | upper _ value _ => exact False.elim (nonoriginal value.mode)
  | active core active =>
    have mode := active.mode.resolve_left nonoriginal
    exact CampusTCPTwoProgressRecoveryRank.recovery_positive _ _ _ _ _ mode (active_rank_shape active mode)
      (active_waiting_credit active)
  | ready _ ready => simp only [K.rank, ready.mode]; decide
  | done value => exact False.elim (nondone value.mode)

theorem zero_rank_done (value : Evidence initial native quantum allowance current monitor) (bound : Nat)
    (nonoriginal : monitor.mode ≠ .originals)
    (zero : K.rank (config initial native quantum allowance) bound allowance current.report.final monitor = 0) : monitor.mode = .done := by
  by_cases done : monitor.mode = .done
  · exact done
  · have positive := evidence_positive value bound nonoriginal done
    rw [zero] at positive
    exact False.elim (Nat.not_lt_zero _ positive)

private theorem core_slots_le (core : Core initial native quantum allowance current monitor sent received)
    (cap : PendingCap (config initial native quantum allowance) capacity current.report.final monitor)
    (pending : sent.ledger ≠ []) (counts : monitor.retries ≤ allowance) :
    K.timerSlots (config initial native quantum allowance) current.report.final ≤
      boundSlots (config initial native quantum allowance) capacity allowance := by
  rw [CampusTCPTwoProgressRecoveryRank.timerSlots_of_runtime _ _ _ (CampusTCPTwoProgressPhaseNormalize.sender_runtime core)]
  have rto := CampusTCPTwoProgressRecoveryCap.at_core core cap pending
  have powers : 2 ^ monitor.retries * capacity ≤ 2 ^ allowance * capacity :=
    Nat.mul_le_mul_right capacity (Nat.pow_le_pow_of_le (by decide) counts)
  exact Nat.le_trans (CampusTCPTwoProgressTimerInvariant.slots_le core)
    (CampusTCPRecoveryRoundMonitor.waitSlots_mono (Nat.le_trans rto powers))

theorem active_slots_le (active : Active core)
    (cap : PendingCap (config initial native quantum allowance) capacity current.report.final monitor) :
    K.timerSlots (config initial native quantum allowance) current.report.final ≤
      boundSlots (config initial native quantum allowance) capacity allowance :=
  core_slots_le core cap active.nonempty (CampusTCPTwoProgressHandoffRTO.evidence_retry_bound (.active core active))

private theorem empty_slots (cfg : CampusTCPTwoProgressMonitor.Config) (state : State input) (recovery : Recovery.State)
    (runtime : CampusTCPGapProgressMonitor.senderRecovery cfg.toConfig state = some recovery)
    (empty : recovery.outstanding = []) : K.timerSlots cfg state = 0 := by
  rw [CampusTCPTwoProgressRecoveryRank.timerSlots_of_runtime _ _ _ runtime]
  have target : CampusTCPTwoProgressMonitor.timerTarget recovery = none := by
    simp only [CampusTCPTwoProgressMonitor.timerTarget, empty, List.head?_nil, bind, Option.bind]
  rw [CampusTCPTwoProgressTimer.slots, CampusTCPTwoProgressTimer.remaining_none target]
  by_cases positive : 0 < cfg.quantum
  · exact CampusTCPRecoveryRoundMonitor.waitSlots_zero positive
  · have zero : cfg.quantum = 0 := by omega
    change CampusTCPRecoveryRoundMonitor.waitSlots cfg.quantum 0 = 0
    rw [zero]
    rfl

theorem evidence_slots_le (value : Evidence initial native quantum allowance current monitor)
    (nonoriginal : monitor.mode ≠ .originals)
    (cap : PendingCap (config initial native quantum allowance) capacity current.report.final monitor) :
    K.timerSlots (config initial native quantum allowance) current.report.final ≤
      boundSlots (config initial native quantum allowance) capacity allowance := by
  cases value with
  | written value _ => exact False.elim (nonoriginal value.mode)
  | upper _ value _ => exact False.elim (nonoriginal value.mode)
  | active core active => exact active_slots_le active cap
  | ready core ready =>
    rw [empty_slots _ _ _ (CampusTCPTwoProgressPhaseNormalize.sender_runtime core)
      (core.live.senderFlight.ledger.trans ready.retired)]
    exact Nat.zero_le _
  | done value =>
    have runtime : CampusTCPGapProgressMonitor.senderRecovery (config initial native quantum allowance).toConfig
        current.report.final = some value.completed.senderFlight.recovery := by
      simp only [CampusTCPGapProgressMonitor.senderRecovery, current.connection, config]
      exact value.completed.senderFlight.runtime
    rw [empty_slots _ _ _ runtime value.completed.senderFlight.ledger]
    exact Nat.zero_le _

theorem evidence_rank_le (value : Evidence initial native quantum allowance current monitor)
    (nonoriginal : monitor.mode ≠ .originals)
    (cap : PendingCap (config initial native quantum allowance) capacity current.report.final monitor) :
    K.rank (config initial native quantum allowance) (boundSlots (config initial native quantum allowance) capacity allowance)
      allowance current.report.final monitor ≤
        (allowance + 1) * boundSlots (config initial native quantum allowance) capacity allowance + 8 * allowance + 7 := by
  cases value with
  | written value _ => exact False.elim (nonoriginal value.mode)
  | upper _ value _ => exact False.elim (nonoriginal value.mode)
  | active core active =>
    exact CampusTCPTwoProgressRecoveryRank.recovery_le _ _ _ _ _ (active.mode.resolve_left nonoriginal)
      (active_work_shape active) (CampusTCPTwoProgressHandoffRTO.evidence_retry_bound (.active core active)) (active_slots_le active cap)
  | ready _ ready => simp only [K.rank, ready.mode]; omega
  | done value => simp only [K.rank, value.mode]; exact Nat.zero_le _

end Netlib.Check.CampusTCPTwoProgressEvidenceRecoveryRank
