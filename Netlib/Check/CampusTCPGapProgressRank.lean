import Netlib.Check.CampusTCPGapProgressMonitor
import Netlib.Check.CampusTCPRecoveryRoundRank

/-!
# Remaining service for a held TCP gap

The first wait starts at the actual initial timer distance.
A selected drop reserves a timer wait and another packet path.
-/

namespace Netlib.Check.CampusTCPGapProgressMonitor

open CampusTCPModel Protocol.TCP

abbrev waitSlots_zero := @CampusTCPRecoveryRoundMonitor.waitSlots_zero
abbrev waitSlots_mono := @CampusTCPRecoveryRoundMonitor.waitSlots_mono
abbrev waitSlots_tick := @CampusTCPRecoveryRoundMonitor.waitSlots_tick
abbrev timer_tick_distance := CampusTCPRecoveryRoundMonitor.timer_tick_distance

theorem reserve_step (config : Config) (retries : Nat)
    (budget : config.lossAllowance ≤ 2) (credit : retries < config.lossAllowance) :
    reserve config retries = waitSlots config.quantum (waitBound config retries) + 8 + reserve config (retries + 1) := by
  cases retries with
  | zero =>
    have positive : 0 < config.lossAllowance := credit
    simp [reserve, waitBound, positive, Nat.add_assoc]
  | succ retries =>
    have first : retries = 0 := by omega
    have two : config.lossAllowance = 2 := by omega
    subst retries
    simp [reserve, waitBound, two]

def initialRank (config : Config) : Nat := 6 + reserve config 0

def boundSlots (config : Config) (service : Nat) : Nat := initialRank config * service

theorem initial_rank_eq (config : Config) (state : State input) (output service packet : Nat) :
    (Monitor.initial output service packet).rank config state = initialRank config := rfl

theorem forward_ten_two (config : Config) (quantum : config.quantum = 10)
    (rto : config.initialRTO = 1000) (remaining : config.initialRemaining = 1000)
    (allowance : config.lossAllowance = 2) : boundSlots config 2 = 644 := by
  simp only [boundSlots, initialRank, reserve, quantum, rto, remaining, allowance,
    Nat.reduceLT, ↓reduceIte]
  rfl

theorem reverse_ten_two (config : Config) (quantum : config.quantum = 10)
    (rto : config.initialRTO = 1000) (remaining : config.initialRemaining = 900)
    (allowance : config.lossAllowance = 2) : boundSlots config 2 = 624 := by
  simp only [boundSlots, initialRank, reserve, quantum, rto, remaining, allowance,
    Nat.reduceLT, ↓reduceIte]
  rfl

theorem rank_drop (config : Config) (before after : State input) (monitor : Monitor) (id : Nat)
    (waiting : monitor.waiting = false) (budget : config.lossAllowance ≤ 2)
    (credit : monitor.retries < config.lossAllowance)
    (phase : monitor.phase = .dataIngress ∨ monitor.phase = .dataLink ∨
      monitor.phase = .ackIngress ∨ monitor.phase = .ackLink)
    (recovery : Recovery.State) (runtime : senderRecovery config before = some recovery)
    (same : senderRecovery config after = senderRecovery config before)
    (deadline : recovery.deadline = some due)
    (remaining : due - recovery.now ≤ waitBound config monitor.retries) :
    ({ monitor with waiting := true, drops := monitor.drops ++ [id] } : Monitor).rank config after <
      monitor.rank config before := by
  have slots : waitSlots config.quantum (due - recovery.now) ≤
      waitSlots config.quantum (waitBound config monitor.retries) :=
    waitSlots_mono remaining
  have future := reserve_step config monitor.retries budget credit
  rcases phase with phase | phase | phase | phase
  all_goals
    simp only [Monitor.rank, waiting, Bool.false_eq_true, ite_false, ite_true, phase,
      CampusTCPRoundMonitor.Phase.rank, same, runtime, deadline, Option.getD_some]
    omega

theorem rank_tick (config : Config) (positive : 0 < config.quantum)
    (before after : State input) (monitor : Monitor) (waiting : monitor.waiting = true)
    (recovery : Recovery.State) (runtime : senderRecovery config before = some recovery)
    (deadline : recovery.deadline = some due) (early : recovery.now < due)
    (updated : senderRecovery config after = some { recovery with now := min (recovery.now + config.quantum) due }) :
    monitor.rank config after < monitor.rank config before := by
  have decreases : waitSlots config.quantum ((due - recovery.now) - config.quantum) <
      waitSlots config.quantum (due - recovery.now) :=
    waitSlots_tick positive (show 0 < due - recovery.now by omega)
  simp only [Monitor.rank, waiting, ite_true, updated, runtime, deadline, Option.getD_some]
  rw [timer_tick_distance]
  omega

theorem rank_timeout (config : Config) (positive : 0 < config.quantum)
    (before after : State input) (monitor next : Monitor) (waiting : monitor.waiting = true)
    (recovery : Recovery.State) (runtime : senderRecovery config before = some recovery)
    (deadline : recovery.deadline = some due) (ready : due ≤ recovery.now)
    (active : next.waiting = false) (phase : next.phase = .dataIngress)
    (retries : next.retries = monitor.retries + 1) :
    next.rank config after < monitor.rank config before := by
  have elapsed : due - recovery.now = 0 := by omega
  have zero : waitSlots config.quantum 0 = 0 := waitSlots_zero positive
  simp only [Monitor.rank, active, Bool.false_eq_true, ite_false, phase,
    CampusTCPRoundMonitor.Phase.rank, waiting, ite_true, runtime, deadline, Option.getD_some,
    elapsed, zero, retries]
  omega

theorem rank_nonwaiting_le (config : Config) (state : State input) (monitor : Monitor)
    (active : monitor.waiting = false) :
    monitor.rank config state ≤ monitor.phase.rank + reserve config monitor.retries := by
  cases phase : monitor.phase <;> simp [Monitor.rank, active, phase, CampusTCPRoundMonitor.Phase.rank]

theorem rank_active (config : Config) (state : State input) (monitor : Monitor)
    (active : monitor.waiting = false) (unread : monitor.phase ≠ .needRead) (unfinished : monitor.phase ≠ .done) :
    monitor.rank config state = monitor.phase.rank + reserve config monitor.retries := by
  cases phase : monitor.phase <;> simp_all [Monitor.rank]

theorem rank_ordinary (config : Config) (before after : State input) (monitor next : Monitor)
    (active : monitor.waiting = false) (nextActive : next.waiting = false)
    (unread : monitor.phase ≠ .needRead) (unfinished : monitor.phase ≠ .done)
    (retries : next.retries = monitor.retries) (phase : next.phase.rank < monitor.phase.rank) :
    next.rank config after < monitor.rank config before := by
  have nextBound := rank_nonwaiting_le config after next nextActive
  rw [rank_active config before monitor active unread unfinished]
  rw [retries] at nextBound
  omega

end Netlib.Check.CampusTCPGapProgressMonitor
