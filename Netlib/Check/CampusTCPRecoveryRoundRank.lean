import Netlib.Check.CampusTCPRecoveryRoundMonitor

/-!
# Remaining service in a timed recovery round

Each allowed drop reserves a real timer wait and another packet path.
A full sender tick reduces its remaining timer distance.
-/

namespace Netlib.Check.CampusTCPRecoveryRoundMonitor

theorem waitSlots_zero (positive : 0 < quantum) : waitSlots quantum 0 = 0 := by
  unfold waitSlots
  exact Nat.div_eq_of_lt (by omega)

theorem waitSlots_mono (order : before ≤ after) : waitSlots quantum before ≤ waitSlots quantum after := by
  unfold waitSlots
  apply Nat.div_le_div_right
  omega

theorem waitSlots_positive (positive : 0 < quantum) (remaining : 0 < count) : 0 < waitSlots quantum count := by
  apply Nat.div_pos_iff.mpr
  exact ⟨positive, by omega⟩

theorem waitSlots_tick (positive : 0 < quantum) (remaining : 0 < count) :
    waitSlots quantum (count - quantum) < waitSlots quantum count := by
  by_cases small : count ≤ quantum
  · rw [Nat.sub_eq_zero_of_le small, waitSlots_zero positive]
    exact waitSlots_positive positive remaining
  · have countBound : quantum < count := by omega
    have numerator : count + quantum - 1 = (count - quantum + quantum - 1) + quantum := by omega
    unfold waitSlots
    rw [numerator, Nat.add_div_right _ positive]
    omega

theorem timer_tick_distance (before deadline quantum : Nat) :
    deadline - min (before + quantum) deadline = (deadline - before) - quantum := by omega

theorem reserve_step (retries : Nat) (credit : retries < 2) :
    reserve quantum retries = waitSlots quantum (2 ^ retries * 1000) + 8 + reserve quantum (retries + 1) := by
  have cases : retries = 0 ∨ retries = 1 := by omega
  rcases cases with rfl | rfl <;> simp [reserve, Nat.add_assoc]

theorem initial_rank_ten (config : Config) (state : CampusTCPModel.State input) (quantum : config.quantum = 10) :
    Monitor.initial.rank config state = 325 := by
  rw [initial_rank, quantum]
  rfl

theorem rank_drop (config : Config) (before after : CampusTCPModel.State input) (monitor : Monitor) (id : Nat)
    (waiting : monitor.waiting = false) (credit : monitor.retries < 2)
    (phase : monitor.round.phase = .dataIngress ∨ monitor.round.phase = .dataLink ∨
      monitor.round.phase = .ackIngress ∨ monitor.round.phase = .ackLink)
    (recovery : Protocol.TCP.Recovery.State) (runtime : clientRecovery before = some recovery)
    (same : clientRecovery after = clientRecovery before) (deadline : recovery.deadline = some due)
    (remaining : due - recovery.now ≤ 2 ^ monitor.retries * 1000) :
    (observeDrop monitor id).rank config after < monitor.rank config before := by
  have slots := waitSlots_mono (quantum := config.quantum) remaining
  have future := reserve_step (quantum := config.quantum) monitor.retries credit
  rcases phase with phase | phase | phase | phase
  all_goals
    simp only [Monitor.rank, observeDrop, ite_true, waiting, Bool.false_eq_true, ite_false,
      phase, CampusTCPRoundMonitor.Monitor.rank, CampusTCPRoundMonitor.Phase.rank,
      same, runtime, deadline, Option.getD_some]
    omega

theorem rank_tick (config : Config) (positive : 0 < config.quantum)
    (before after : CampusTCPModel.State input) (monitor : Monitor) (waiting : monitor.waiting = true)
    (recovery : Protocol.TCP.Recovery.State) (runtime : clientRecovery before = some recovery)
    (deadline : recovery.deadline = some due) (early : recovery.now < due)
    (updated : clientRecovery after = some { recovery with now := min (recovery.now + config.quantum) due }) :
    monitor.rank config after < monitor.rank config before := by
  have decreases := waitSlots_tick positive (show 0 < due - recovery.now by omega)
  simp only [Monitor.rank, waiting, ite_true, updated, runtime, deadline, Option.getD_some]
  rw [timer_tick_distance]
  omega

theorem rank_timeout (config : Config) (positive : 0 < config.quantum)
    (before after : CampusTCPModel.State input) (monitor next : Monitor) (waiting : monitor.waiting = true)
    (recovery : Protocol.TCP.Recovery.State) (runtime : clientRecovery before = some recovery)
    (deadline : recovery.deadline = some due) (ready : due ≤ recovery.now)
    (active : next.waiting = false) (retried : next.retries = monitor.retries + 1)
    (phase : next.round.phase = .dataIngress) : next.rank config after < monitor.rank config before := by
  have zero : due - recovery.now = 0 := by omega
  simp only [Monitor.rank, waiting, ite_true, runtime, deadline, Option.getD_some, zero,
    waitSlots_zero positive, active, Bool.false_eq_true, ite_false, phase, retried,
    CampusTCPRoundMonitor.Monitor.rank, CampusTCPRoundMonitor.Phase.rank]
  omega

theorem rank_ordinary (config : Config) (before after : CampusTCPModel.State input) (monitor next : Monitor)
    (waiting : monitor.waiting = false) (active : next.waiting = false)
    (retries : next.retries = monitor.retries)
    (advance : next.round.rank < monitor.round.rank) : next.rank config after < monitor.rank config before := by
  cases first : monitor.round.phase <;> cases last : next.round.phase
  all_goals
    simp only [CampusTCPRoundMonitor.Monitor.rank, first, last, CampusTCPRoundMonitor.Phase.rank] at advance
    simp only [Monitor.rank, waiting, active, Bool.false_eq_true, ite_false, first, last, retries,
      CampusTCPRoundMonitor.Monitor.rank, CampusTCPRoundMonitor.Phase.rank]
    omega

end Netlib.Check.CampusTCPRecoveryRoundMonitor
