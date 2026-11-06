import Netlib.Check.CampusTCPTwoProgressRecoveryRank
import Netlib.Check.CampusTCPTwoProgressMonitorFacts

/-!
# Strict recovery work steps

Ordinary path operations reduce running work.
A resolved path enters a bounded wait or the read phase.
-/

namespace Netlib.Check.CampusTCPTwoProgressRecoveryRankWork

open Protocol.TCP CampusTCPModel CampusTCPTwoProgressMonitor
open CampusTCPTwoProgressOriginalRank (dataCost ackCost RetryPhase AckPhase)
open CampusTCPTwoProgressRecoveryRank
local notation "Config" => CampusTCPTwoProgressMonitor.Config
namespace F
export CampusTCPTwoProgressMonitorFacts
  (phase_beq phase_beq_self phase_beq_false normalize_counters observe_action observe_drop dropTarget_packet)
end F

private theorem running_positive (bound allowance retries amount : Nat) (positive : 0 < amount) :
    0 < runningRank bound allowance retries amount := by unfold runningRank; omega

private theorem invalid_zero (cfg : Config) (bound allowance : Nat) (state : State input) (monitor : Monitor) :
    rank cfg bound allowance state monitor.invalid = 0 := rfl

private theorem running_eq (cfg : Config) (bound allowance : Nat) (state : State input) (monitor : Monitor)
    (mode : monitor.mode = .recovery) (running : monitor.waiting = false) :
    rank cfg bound allowance state monitor = runningRank bound allowance monitor.retries (work monitor) := by
  simp only [rank, mode, running, Bool.false_eq_true, ite_false]

private theorem normalized_strict (cfg : Config) (bound allowance retries amount : Nat)
    (state : State input) (raw : Monitor) (mode : raw.mode = .recovery)
    (ack : raw.ack = none) (retry : raw.retry.phase = .done) (counts : raw.retries = retries)
    (positive : 0 < amount) (time : 0 < bound) (slots : timerSlots cfg state ≤ bound) :
    rank cfg bound allowance state (normalize cfg state raw) < runningRank bound allowance retries amount := by
  simp only [normalize, ack, Option.isNone_none, mode, retry, F.phase_beq_self, Bool.true_and, ite_true]
  cases runtime : CampusTCPGapProgressMonitor.senderRecovery cfg.toConfig state with
  | none =>
    simp only [invalid_zero]
    exact running_positive _ _ _ _ positive
  | some recovery =>
    dsimp only
    split
    · simp only [rank]
      exact running_to_read _ _ _ _ (by omega) positive
    · simp only [rank, ite_true, counts]
      exact running_to_waiting _ _ _ _ _ slots positive

private theorem ack_cost_decreases (cfg : Config) (lane : Lane) (actual : Step input)
    (legal : AckPhase lane.phase) : ackCost (ackLane cfg lane actual).phase < ackCost lane.phase := by
  rcases legal with phase | phase | phase | phase
  all_goals
    rcases CampusTCPTwoProgressOriginalRank.ackLane_phase cfg lane actual with decoded | decoded
    all_goals try simp only [phase] at decoded
    all_goals rw [decoded, phase] <;> decide

private theorem ack_strict (cfg : Config) (bound allowance : Nat) (state : State input) (monitor : Monitor)
    (actual : Step input) (lane : Lane) (mode : monitor.mode = .recovery) (running : monitor.waiting = false)
    (ack : monitor.ack = some lane) (legal : AckPhase lane.phase) (retry : monitor.retry.phase = .done)
    (time : 0 < bound) (slots : timerSlots cfg actual.result.state ≤ bound) :
    rank cfg bound allowance actual.result.state (observeAck cfg monitor actual lane) < rank cfg bound allowance state monitor := by
  have positive := CampusTCPTwoProgressOriginalRank.ackCost_positive legal
  have before : rank cfg bound allowance state monitor = runningRank bound allowance monitor.retries (ackCost lane.phase) := by
    rw [running_eq cfg bound allowance state monitor mode running]
    simp only [work, ack]
  rw [before]
  unfold observeAck
  dsimp only
  split
  · rw [invalid_zero]; exact running_positive _ _ _ _ positive
  · split
    · split
      · rw [invalid_zero]; exact running_positive _ _ _ _ positive
      · exact normalized_strict cfg bound allowance monitor.retries (ackCost lane.phase) actual.result.state _ mode rfl retry rfl positive time slots
    · have decrease := ack_cost_decreases cfg lane actual legal
      simpa only [rank, mode, running, Bool.false_eq_true, ite_false, work] using
        running_strict bound allowance monitor.retries decrease

private theorem retry_active (shape : RankShape monitor) (running : monitor.waiting = false) (ack : monitor.ack = none) :
    monitor.retry.phase = .dataIngress ∨ monitor.retry.phase = .dataTicket ∨ monitor.retry.phase = .dataLink := by
  rcases shape.retry with phase | phase | phase | phase
  · exact .inl phase
  · exact .inr (.inl phase)
  · exact .inr (.inr phase)
  · exact False.elim (shape.runnable running ack phase)

private theorem data_cost_decreases (cfg : Config) (lane : Lane) (actual : Step input)
    (legal : lane.phase = .dataIngress ∨ lane.phase = .dataTicket ∨ lane.phase = .dataLink) :
    (if (dataLane cfg lane actual).phase = .done then 4 else dataCost (dataLane cfg lane actual).phase) < dataCost lane.phase := by
  rcases legal with phase | phase | phase
  all_goals
    rcases CampusTCPTwoProgressOriginalRank.dataLane_phase cfg lane actual with decoded | decoded
    all_goals try simp only [phase] at decoded
    all_goals rw [decoded, phase] <;> decide

private theorem recorded_bound (cfg : Config) (bound allowance : Nat) (state : State input)
    (monitor : Monitor) (lane : Lane) (actual : Step input) (mode : monitor.mode = .recovery) :
    rank cfg bound allowance state
      { recordData { monitor with retry := lane } lane actual with ack := some { phase := .needAck, refs := lane.refs }, waiting := false } ≤
      runningRank bound allowance monitor.retries 4 := by
  cases receipt : lane.refs.dataReceipt <;> cases application : actual.result.application with
  | none => simp only [recordData, receipt, application, rank, Monitor.invalid]; exact Nat.zero_le _
  | some pair =>
    cases pair
    simp only [recordData, receipt, application]
    first
    | exact Nat.zero_le _
    | simp only [rank, mode, Bool.false_eq_true, ite_false, work, ackCost]; exact Nat.le_refl _

private theorem retry_strict (cfg : Config) (bound allowance : Nat) (state : State input) (monitor : Monitor)
    (actual : Step input) (mode : monitor.mode = .recovery) (running : monitor.waiting = false)
    (ack : monitor.ack = none)
    (legal : monitor.retry.phase = .dataIngress ∨ monitor.retry.phase = .dataTicket ∨ monitor.retry.phase = .dataLink) :
    rank cfg bound allowance actual.result.state (observeData cfg monitor actual .retry) < rank cfg bound allowance state monitor := by
  have decrease := data_cost_decreases cfg monitor.retry actual legal
  have positive : 0 < dataCost monitor.retry.phase := by
    rcases legal with phase | phase | phase <;> rw [phase] <;> decide
  have before : rank cfg bound allowance state monitor = runningRank bound allowance monitor.retries (dataCost monitor.retry.phase) := by
    rw [running_eq cfg bound allowance state monitor mode running]
    simp only [work, ack]
  rw [before]
  unfold observeData
  dsimp only
  split
  · rw [invalid_zero]; exact running_positive _ _ _ _ positive
  · split
    · rename_i done
      have done : (dataLane cfg monitor.retry actual).phase = .done := by simpa only [F.phase_beq, decide_eq_true_eq] using done
      have reduced : 4 < dataCost monitor.retry.phase := by simpa only [done, ite_true] using decrease
      exact Nat.lt_of_le_of_lt (recorded_bound cfg bound allowance _ monitor _ actual mode)
        (running_strict bound allowance monitor.retries reduced)
    · rename_i pending
      have notDone : (dataLane cfg monitor.retry actual).phase ≠ .done := by
        intro done
        simp only [done, F.phase_beq_self] at pending
        contradiction
      have reduced : dataCost (dataLane cfg monitor.retry actual).phase < dataCost monitor.retry.phase := by
        simpa only [notDone, ite_false] using decrease
      simpa only [rank, mode, running, Bool.false_eq_true, ite_false, work, ack] using
        running_strict bound allowance monitor.retries reduced

theorem ordinary_strict (cfg : Config) (bound allowance : Nat) (state : State input) (monitor : Monitor)
    (actual : Step input) (mode : monitor.mode = .recovery) (running : monitor.waiting = false)
    (shape : RankShape monitor) (time : 0 < bound) (slots : timerSlots cfg actual.result.state ≤ bound) :
    rank cfg bound allowance actual.result.state (observeOrdinary cfg monitor actual) < rank cfg bound allowance state monitor := by
  cases ack : monitor.ack with
  | none =>
    simp only [observeOrdinary, mode, ack, running, Bool.false_eq_true, ite_false]
    exact retry_strict cfg bound allowance state monitor actual mode running ack (retry_active shape running ack)
  | some lane =>
    simp only [observeOrdinary, mode, ack]
    exact ack_strict cfg bound allowance state monitor actual lane mode running ack (shape.ack lane ack)
      (shape.serial (by rw [ack]; rfl)) time slots

theorem action_strict (cfg : Config) (bound allowance : Nat) (state : State input) (monitor : Monitor)
    (actual : Step input) (mode : monitor.mode = .recovery) (running : monitor.waiting = false)
    (shape : RankShape monitor) (time : 0 < bound) (slots : timerSlots cfg actual.result.state ≤ bound)
    (supported : actual.result.supported = true) (passed : actual.result.passed = true)
    (allowed : Allowed cfg actual.before monitor actual.event) (action : CampusTCPRoundMonitor.Action)
    (event : actual.event = action.event) :
    rank cfg bound allowance actual.result.state (observe cfg monitor actual) < rank cfg bound allowance state monitor := by
  rw [F.observe_action cfg monitor actual supported passed allowed action event]
  exact ordinary_strict cfg bound allowance state monitor actual mode running shape time slots

private theorem done_unexposed (cfg : Config) (state : State input) (lane : Lane) (done : lane.phase = .done) :
    exposedPacket cfg state lane = none := by
  simp only [exposedPacket, CampusTCPGapProgressMonitor.nextAction, Lane.toGap, done, bind, Option.bind]

theorem drop_strict (cfg : Config) (bound allowance : Nat) (state : State input) (monitor : Monitor)
    (actual : Step input) (id : Nat) (mode : monitor.mode = .recovery) (running : monitor.waiting = false)
    (shape : RankShape monitor) (lowerDone : monitor.lower.phase = .done) (upperDone : monitor.upper.phase = .done)
    (selected : dropTarget cfg actual.before monitor id = some target)
    (time : 0 < bound) (slots : timerSlots cfg actual.result.state ≤ bound) :
    rank cfg bound allowance actual.result.state (observeDrop cfg monitor actual id) < rank cfg bound allowance state monitor := by
  have packet := F.dropTarget_packet cfg actual.before monitor id selected
  have positive := work_positive shape running
  rw [running_eq cfg bound allowance state monitor mode running]
  cases target with
  | lower =>
    rw [done_unexposed cfg actual.before monitor.lower lowerDone] at packet
    cases packet
  | upper =>
    rw [done_unexposed cfg actual.before monitor.upper upperDone] at packet
    cases packet
  | retry =>
    have ackNone : monitor.ack = none := by
      cases ack : monitor.ack with
      | none => rfl
      | some lane =>
        have retryDone := shape.serial (by rw [ack]; rfl)
        rw [done_unexposed cfg actual.before monitor.retry retryDone] at packet
        cases packet
    simp only [observeDrop, selected]
    exact normalized_strict cfg bound allowance monitor.retries (work monitor) actual.result.state _ mode ackNone rfl rfl positive time slots
  | ack =>
    obtain ⟨lane, ack, _⟩ := packet
    have retryDone := shape.serial (by rw [ack]; rfl)
    simp only [observeDrop, selected]
    exact normalized_strict cfg bound allowance monitor.retries (work monitor) actual.result.state _ mode rfl retryDone rfl positive time slots

theorem observed_drop_strict (cfg : Config) (bound allowance : Nat) (state : State input) (monitor : Monitor)
    (actual : Step input) (id : Nat) (mode : monitor.mode = .recovery) (running : monitor.waiting = false)
    (shape : RankShape monitor) (lowerDone : monitor.lower.phase = .done) (upperDone : monitor.upper.phase = .done)
    (selected : dropTarget cfg actual.before monitor id = some target)
    (time : 0 < bound) (slots : timerSlots cfg actual.result.state ≤ bound)
    (supported : actual.result.supported = true) (passed : actual.result.passed = true)
    (allowed : Allowed cfg actual.before monitor actual.event) (event : actual.event = .dropPacket id) :
    rank cfg bound allowance actual.result.state (observe cfg monitor actual) < rank cfg bound allowance state monitor := by
  rw [F.observe_drop cfg monitor actual supported passed allowed event]
  exact drop_strict cfg bound allowance state monitor actual id mode running shape lowerDone upperDone selected time slots

end Netlib.Check.CampusTCPTwoProgressRecoveryRankWork
