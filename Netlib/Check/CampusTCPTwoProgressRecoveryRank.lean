import Netlib.Check.CampusTCPTwoProgressMonitor
import Netlib.Check.CampusTCPTwoProgressTimer
import Netlib.Check.CampusTCPTwoProgressOriginalRank

/-!
# Recovery work and timeout reserve

The reserve counts remaining global timeout outputs.
Current timer slots matter only while the monitor waits.
-/

namespace Netlib.Check.CampusTCPTwoProgressRecoveryRank

open Protocol.TCP CampusTCPModel CampusTCPTwoProgressMonitor
open CampusTCPTwoProgressOriginalRank (dataCost ackCost RetryPhase AckPhase)
local notation "Config" => CampusTCPTwoProgressMonitor.Config

def work (monitor : Monitor) : Nat :=
  match monitor.ack with
  | some lane => ackCost lane.phase
  | none => dataCost monitor.retry.phase

def timerSlots (cfg : Config) (state : State input) : Nat :=
  match CampusTCPGapProgressMonitor.senderRecovery cfg.toConfig state with
  | none => 0
  | some recovery => CampusTCPTwoProgressTimer.slots cfg.quantum recovery

def waitingRank (bound allowance retries slots : Nat) : Nat :=
  (allowance - retries) * (bound + 8) + slots

def runningRank (bound allowance retries work : Nat) : Nat :=
  (allowance - retries) * (bound + 8) + bound + work

def rank (cfg : Config) (bound allowance : Nat) (state : State input) (monitor : Monitor) : Nat :=
  match monitor.mode with
  | .recovery => if monitor.waiting then waitingRank bound allowance monitor.retries (timerSlots cfg state)
      else runningRank bound allowance monitor.retries (work monitor)
  | .needRead => 1
  | _ => 0

structure WorkShape (monitor : Monitor) : Prop where
  retry : RetryPhase monitor.retry.phase
  ack : ∀ lane, monitor.ack = some lane → AckPhase lane.phase

structure RankShape (monitor : Monitor) : Prop extends WorkShape monitor where
  waiting : monitor.waiting = true → monitor.ack = none ∧ monitor.retry.phase = .done
  serial : monitor.ack.isSome = true → monitor.retry.phase = .done
  runnable : monitor.waiting = false → monitor.ack = none → monitor.retry.phase ≠ .done

theorem timerSlots_of_runtime (cfg : Config) (state : State input) (recovery : Recovery.State)
    (runtime : CampusTCPGapProgressMonitor.senderRecovery cfg.toConfig state = some recovery) :
    timerSlots cfg state = CampusTCPTwoProgressTimer.slots cfg.quantum recovery := by
  rw [timerSlots, runtime]

theorem work_le (shape : WorkShape monitor) : work monitor ≤ 7 := by
  cases ack : monitor.ack with
  | none =>
    have legal := shape.retry
    rcases legal with phase | phase | phase | phase <;> simp only [work, ack, phase, dataCost] <;> decide
  | some lane =>
    have legal := shape.ack lane ack
    rcases legal with phase | phase | phase | phase <;> simp only [work, ack, phase, ackCost] <;> decide

theorem work_positive (shape : RankShape monitor) (running : monitor.waiting = false) : 0 < work monitor := by
  cases ack : monitor.ack with
  | none =>
    have active := shape.runnable running ack
    rcases shape.retry with phase | phase | phase | phase
    all_goals simp only [work, ack, phase, dataCost] at *
    all_goals first | decide | exact False.elim (active rfl)
  | some lane =>
    simpa only [work, ack] using CampusTCPTwoProgressOriginalRank.ackCost_positive (shape.ack lane ack)

theorem waiting_mono (bound allowance retries : Nat) (slots : first ≤ last) :
    waitingRank bound allowance retries first ≤ waitingRank bound allowance retries last := Nat.add_le_add_left slots _

theorem waiting_strict (bound allowance retries : Nat) (slots : first < last) :
    waitingRank bound allowance retries first < waitingRank bound allowance retries last := Nat.add_lt_add_left slots _

theorem running_mono (bound allowance retries : Nat) (work : first ≤ last) :
    runningRank bound allowance retries first ≤ runningRank bound allowance retries last := Nat.add_le_add_left work _

theorem running_strict (bound allowance retries : Nat) (work : first < last) :
    runningRank bound allowance retries first < runningRank bound allowance retries last := Nat.add_lt_add_left work _

theorem timeout_exact (bound allowance retries : Nat) (credit : retries < allowance) :
    runningRank bound allowance (retries + 1) 7 + 1 = waitingRank bound allowance retries 0 := by
  have remaining : allowance - retries = (allowance - (retries + 1)) + 1 := by omega
  simp only [runningRank, waitingRank, remaining, Nat.add_mul, Nat.one_mul]
  omega

theorem timeout_strict (bound allowance retries : Nat) (credit : retries < allowance) :
    runningRank bound allowance (retries + 1) 7 < waitingRank bound allowance retries 0 := by
  have exactStep := timeout_exact bound allowance retries credit
  omega

theorem running_to_waiting (bound allowance retries slots amount : Nat) (distance : slots ≤ bound) (positive : 0 < amount) :
    waitingRank bound allowance retries slots < runningRank bound allowance retries amount := by
  unfold waitingRank runningRank
  omega

theorem running_to_read (bound allowance retries amount : Nat) (time : 1 ≤ bound) (positive : 0 < amount) :
    1 < runningRank bound allowance retries amount := by
  unfold runningRank
  omega

theorem waiting_positive (bound allowance retries slots : Nat) (credit : retries < allowance) :
    0 < waitingRank bound allowance retries slots := by
  have positive : 0 < allowance - retries := by omega
  have reserve := Nat.mul_pos positive (show 0 < bound + 8 by omega)
  unfold waitingRank
  omega

theorem recovery_positive (cfg : Config) (bound allowance : Nat) (state : State input) (monitor : Monitor)
    (mode : monitor.mode = .recovery) (shape : RankShape monitor)
    (credit : monitor.waiting = true → monitor.retries < allowance) : 0 < rank cfg bound allowance state monitor := by
  rw [rank, mode]
  cases waiting : monitor.waiting with
  | true => exact waiting_positive _ _ _ _ (credit waiting)
  | false =>
    have positive := work_positive shape waiting
    simp only [Bool.false_eq_true, ite_false]
    unfold runningRank
    omega

theorem recovery_le (cfg : Config) (bound allowance : Nat) (state : State input) (monitor : Monitor)
    (mode : monitor.mode = .recovery) (shape : WorkShape monitor)
    (_count : monitor.retries ≤ allowance) (slots : timerSlots cfg state ≤ bound) :
    rank cfg bound allowance state monitor ≤ (allowance + 1) * bound + 8 * allowance + 7 := by
  have reserve := Nat.mul_le_mul_right (bound + 8) (Nat.sub_le allowance monitor.retries)
  have workBound := work_le shape
  rw [rank, mode]
  cases waiting : monitor.waiting
  all_goals simp only [Bool.false_eq_true, ite_false, ite_true, waitingRank, runningRank, Nat.add_mul, Nat.one_mul, Nat.mul_add] at *
  all_goals simp only [Nat.mul_comm allowance 8] at reserve
  all_goals omega

theorem waiting_step (cfg : Config) (bound allowance : Nat) (before after : State input) (old next : Monitor)
    (oldMode : old.mode = .recovery) (nextMode : next.mode = .recovery)
    (oldWaiting : old.waiting = true) (nextWaiting : next.waiting = true) (counts : next.retries = old.retries)
    (slots : timerSlots cfg after < timerSlots cfg before) : rank cfg bound allowance after next < rank cfg bound allowance before old := by
  simp only [rank, oldMode, nextMode, oldWaiting, nextWaiting, ite_true, counts]
  exact waiting_strict _ _ _ slots

theorem work_step (cfg : Config) (bound allowance : Nat) (before after : State input) (old next : Monitor)
    (oldMode : old.mode = .recovery) (nextMode : next.mode = .recovery)
    (oldWaiting : old.waiting = false) (nextWaiting : next.waiting = false) (counts : next.retries = old.retries)
    (decrease : work next < work old) : rank cfg bound allowance after next < rank cfg bound allowance before old := by
  simp only [rank, oldMode, nextMode, oldWaiting, nextWaiting, Bool.false_eq_true, ite_false, counts]
  exact running_strict _ _ _ decrease

theorem resolution_step (cfg : Config) (bound allowance : Nat) (before after : State input) (old next : Monitor)
    (oldMode : old.mode = .recovery) (nextMode : next.mode = .recovery)
    (oldWaiting : old.waiting = false) (nextWaiting : next.waiting = true) (counts : next.retries = old.retries)
    (positive : 0 < work old) (slots : timerSlots cfg after ≤ bound) :
    rank cfg bound allowance after next < rank cfg bound allowance before old := by
  simp only [rank, oldMode, nextMode, oldWaiting, nextWaiting, Bool.false_eq_true, ite_false, ite_true, counts]
  exact running_to_waiting _ _ _ _ _ slots positive

theorem timeout_step (cfg : Config) (bound allowance : Nat) (before after : State input) (old next : Monitor)
    (oldMode : old.mode = .recovery) (nextMode : next.mode = .recovery)
    (oldWaiting : old.waiting = true) (nextWaiting : next.waiting = false) (counts : next.retries = old.retries + 1)
    (credit : old.retries < allowance) (due : timerSlots cfg before = 0) (ingress : work next = 7) :
    rank cfg bound allowance after next + 1 = rank cfg bound allowance before old := by
  simp only [rank, oldMode, nextMode, oldWaiting, nextWaiting, Bool.false_eq_true, ite_false, ite_true, counts, due, ingress]
  exact timeout_exact _ _ _ credit

theorem read_ready_step (cfg : Config) (bound allowance : Nat) (before after : State input) (old next : Monitor)
    (oldMode : old.mode = .recovery) (nextMode : next.mode = .needRead)
    (oldWaiting : old.waiting = false) (positive : 0 < work old) (time : 1 ≤ bound) :
    rank cfg bound allowance after next < rank cfg bound allowance before old := by
  simp only [rank, oldMode, nextMode, oldWaiting, Bool.false_eq_true, ite_false]
  exact running_to_read _ _ _ _ time positive

theorem read_done_step (cfg : Config) (bound allowance : Nat) (before after : State input) (old next : Monitor)
    (ready : old.mode = .needRead) (done : next.mode = .done) :
    rank cfg bound allowance after next < rank cfg bound allowance before old := by
  simp only [rank, ready, done]
  decide

end Netlib.Check.CampusTCPTwoProgressRecoveryRank
