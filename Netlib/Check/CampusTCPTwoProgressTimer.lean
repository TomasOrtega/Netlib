import Netlib.Check.CampusTCPTwoProgressMonitor
import Netlib.Check.CampusTCPRecoveryRoundRank
import Netlib.Protocol.TCP.EndpointClockEnabled

/-!
# Current head timer distance

Both the stored deadline and the head's elapsed-time bound apply.
Clock frames retain those bounds and change only the current time.
-/

namespace Netlib.Check.CampusTCPTwoProgressTimer

open Protocol.TCP CampusTCPModel

namespace M
export CampusTCPTwoProgressMonitor (Config timerTarget timerDemand)
end M
namespace G
export CampusTCPGapProgressMonitor (Demand senderRecovery)
end G

abbrev waitSlots := CampusTCPRecoveryRoundMonitor.waitSlots

def remaining (recovery : Recovery.State) : Nat :=
  match M.timerTarget recovery with
  | none => 0
  | some target => target - recovery.now

def slots (quantum : Nat) (recovery : Recovery.State) : Nat := waitSlots quantum (remaining recovery)

variable {recovery current : Recovery.State} {head : Recovery.Outstanding} {rest : List Recovery.Outstanding}
  {deadline target quantum millis : Nat}

theorem target_of_fields (ledger : recovery.outstanding = head :: rest) (timer : recovery.deadline = some deadline) :
    M.timerTarget recovery = some (max deadline (head.lastAt + recovery.rto)) := by
  simp [M.timerTarget, ledger, timer]

theorem target_some (selected : M.timerTarget recovery = some target) :
    ∃ head rest deadline, recovery.outstanding = head :: rest ∧ recovery.deadline = some deadline ∧
      target = max deadline (head.lastAt + recovery.rto) := by
  cases ledger : recovery.outstanding with
  | nil => simp [M.timerTarget, ledger] at selected
  | cons head rest =>
    cases timer : recovery.deadline with
    | none => simp [M.timerTarget, ledger, timer] at selected
    | some deadline =>
      have same : max deadline (head.lastAt + recovery.rto) = target := by
        simpa [M.timerTarget, ledger, timer] using selected
      exact ⟨head, rest, deadline, rfl, rfl, same.symm⟩

theorem target_now (recovery : Recovery.State) (millis : Nat) :
    M.timerTarget { recovery with now := millis } = M.timerTarget recovery := rfl

theorem remaining_of_target (selected : M.timerTarget recovery = some target) :
    remaining recovery = target - recovery.now := by rw [remaining, selected]

theorem remaining_none (absent : M.timerTarget recovery = none) : remaining recovery = 0 := by rw [remaining, absent]

theorem due_fields (ledger : recovery.outstanding = head :: rest) (timer : recovery.deadline = some deadline)
    (selected : M.timerTarget recovery = some target) (due : target ≤ recovery.now) :
    deadline ≤ recovery.now ∧ head.lastAt + recovery.rto ≤ recovery.now := by
  have same := Option.some.inj ((target_of_fields ledger timer).symm.trans selected)
  rw [← same] at due
  exact Nat.max_le.mp due

theorem due_of_zero (ledger : recovery.outstanding = head :: rest) (timer : recovery.deadline = some deadline)
    (zero : remaining recovery = 0) : deadline ≤ recovery.now ∧ head.lastAt + recovery.rto ≤ recovery.now := by
  rw [remaining_of_target (target_of_fields ledger timer)] at zero
  exact Nat.max_le.mp (show max deadline (head.lastAt + recovery.rto) ≤ recovery.now by omega)

theorem remaining_now_le (recovery : Recovery.State) (monotone : recovery.now ≤ millis) :
    remaining { recovery with now := millis } ≤ remaining recovery := by
  cases selected : M.timerTarget recovery with
  | none => simp only [remaining, target_now, selected, Nat.le_refl]
  | some target =>
    simp only [remaining, target_now, selected]
    omega

theorem slots_now_le (recovery : Recovery.State) (monotone : recovery.now ≤ millis) :
    slots quantum { recovery with now := millis } ≤ slots quantum recovery :=
  CampusTCPRecoveryRoundMonitor.waitSlots_mono (remaining_now_le recovery monotone)

theorem tick_distance (selected : M.timerTarget recovery = some target) (quantum : Nat) :
    remaining { recovery with now := min (recovery.now + quantum) target } = remaining recovery - quantum := by
  simp only [remaining, target_now, selected]
  exact CampusTCPRecoveryRoundMonitor.timer_tick_distance _ _ _

theorem tick_slots_lt (selected : M.timerTarget recovery = some target) (positive : 0 < quantum)
    (early : recovery.now < target) :
    slots quantum { recovery with now := min (recovery.now + quantum) target } < slots quantum recovery := by
  unfold slots
  rw [tick_distance selected]
  exact CampusTCPRecoveryRoundMonitor.waitSlots_tick positive
    (by rw [remaining_of_target selected]; omega)

theorem tick_bounds (positive : 0 < quantum) (early : recovery.now < target) :
    recovery.now < min (recovery.now + quantum) target ∧
      min (recovery.now + quantum) target ≤ recovery.now + quantum ∧
      min (recovery.now + quantum) target ≤ target := by omega

theorem now_eq_of_remaining_eq (old : M.timerTarget recovery = some target)
    (updated : M.timerTarget current = some target) (early : recovery.now < target)
    (distance : remaining current = remaining recovery) : current.now = recovery.now := by
  rw [remaining_of_target updated, remaining_of_target old] at distance
  omega

theorem due_of_remaining_eq (old : M.timerTarget recovery = some target)
    (updated : M.timerTarget current = some target) (due : target ≤ recovery.now)
    (distance : remaining current = remaining recovery) : target ≤ current.now := by
  rw [remaining_of_target updated, remaining_of_target old] at distance
  omega

variable {before after : Endpoint.State}

theorem clock_recovery (frame : Endpoint.ClockFrame before after) (runtime : before.recovery = some recovery)
    (updated : after.recovery = some current) :
    current = { recovery with now := after.now } ∧ recovery.now ≤ current.now := by
  have same : current = { recovery with now := after.now } :=
    Option.some.inj (updated.symm.trans (frame.runtime runtime))
  have monotone : recovery.now ≤ after.now := by
    simpa only [Endpoint.State.now, runtime, Option.map_some, Option.getD_some] using frame.monotone
  exact ⟨same, by rw [same]; exact monotone⟩

theorem clock_target (frame : Endpoint.ClockFrame before after) (runtime : before.recovery = some recovery)
    (updated : after.recovery = some current) : M.timerTarget current = M.timerTarget recovery := by
  rw [(clock_recovery frame runtime updated).1]
  exact target_now _ _

theorem clock_remaining_le (frame : Endpoint.ClockFrame before after) (runtime : before.recovery = some recovery)
    (updated : after.recovery = some current) : remaining current ≤ remaining recovery := by
  have fields := clock_recovery frame runtime updated
  rw [fields.1]
  apply remaining_now_le
  simpa only [fields.1] using fields.2

theorem clock_slots_le (frame : Endpoint.ClockFrame before after) (runtime : before.recovery = some recovery)
    (updated : after.recovery = some current) : slots quantum current ≤ slots quantum recovery :=
  CampusTCPRecoveryRoundMonitor.waitSlots_mono (clock_remaining_le frame runtime updated)

variable {input : Input} {config : M.Config} {state nextState : State input} {demand : G.Demand}

theorem timerDemand_of_target (runtime : G.senderRecovery config.toConfig state = some recovery)
    (selected : M.timerTarget recovery = some target) :
    M.timerDemand config state = some (if recovery.now < target then
      .tick config.sender (min (recovery.now + config.quantum) target) else .timeout config.sender) := by
  simp only [M.timerDemand, runtime, selected, bind, Option.bind]
  split <;> rfl

theorem timerDemand_some (pending : M.timerDemand config state = some demand) :
    ∃ recovery head rest deadline target, G.senderRecovery config.toConfig state = some recovery ∧
      recovery.outstanding = head :: rest ∧ recovery.deadline = some deadline ∧
      target = max deadline (head.lastAt + recovery.rto) ∧
      demand = (if recovery.now < target then .tick config.sender (min (recovery.now + config.quantum) target)
        else .timeout config.sender) := by
  cases runtime : G.senderRecovery config.toConfig state with
  | none => simp [M.timerDemand, runtime] at pending
  | some recovery =>
    cases selected : M.timerTarget recovery with
    | none => simp [M.timerDemand, runtime, selected] at pending
    | some target =>
      obtain ⟨head, rest, deadline, ledger, timer, targetEq⟩ := target_some selected
      have same := Option.some.inj ((timerDemand_of_target runtime selected).symm.trans pending)
      exact ⟨recovery, head, rest, deadline, target, rfl, ledger, timer, targetEq, same.symm⟩

theorem timerDemand_persistent (runtime : G.senderRecovery config.toConfig state = some recovery)
    (updated : G.senderRecovery config.toConfig nextState = some current)
    (target : M.timerTarget current = M.timerTarget recovery) (distance : remaining current = remaining recovery) :
    M.timerDemand config nextState = M.timerDemand config state := by
  cases selected : M.timerTarget recovery with
  | none => simp only [M.timerDemand, runtime, updated, target, selected, bind, Option.bind]
  | some due =>
    have nextTarget := target.trans selected
    rw [timerDemand_of_target updated nextTarget, timerDemand_of_target runtime selected]
    by_cases early : recovery.now < due
    · rw [now_eq_of_remaining_eq selected nextTarget early distance]
    · have late := due_of_remaining_eq selected nextTarget (by omega) distance
      simp only [early, Nat.not_lt.mpr late, ite_false]

theorem clock_tick_slots_lt (frame : Endpoint.ClockFrame before after) (runtime : before.recovery = some recovery)
    (updated : after.recovery = some current) (selected : M.timerTarget recovery = some target)
    (positive : 0 < quantum) (early : recovery.now < target)
    (tick : current.now = min (recovery.now + quantum) target) : slots quantum current < slots quantum recovery := by
  have changed := (clock_recovery frame runtime updated).1
  have now := congrArg Recovery.State.now changed
  have time : after.now = min (recovery.now + quantum) target := now.symm.trans tick
  rw [time] at changed
  rw [changed]
  exact tick_slots_lt selected positive early

theorem timerDemand_tick {actor : Actor}
    (pending : M.timerDemand config state = some (.tick actor millis)) :
    ∃ recovery head rest deadline target, G.senderRecovery config.toConfig state = some recovery ∧
      M.timerTarget recovery = some target ∧ recovery.outstanding = head :: rest ∧
      recovery.deadline = some deadline ∧ target = max deadline (head.lastAt + recovery.rto) ∧
      recovery.now < target ∧ actor = config.sender ∧ millis = min (recovery.now + config.quantum) target := by
  obtain ⟨recovery, head, rest, deadline, target, runtime, ledger, timer, targetEq, demand⟩ := timerDemand_some pending
  by_cases early : recovery.now < target
  · simp only [early, ite_true] at demand
    have fields : actor = config.sender ∧ millis = min (recovery.now + config.quantum) target := by
      cases demand
      exact ⟨rfl, rfl⟩
    refine ⟨recovery, head, rest, deadline, target, runtime, ?_, ledger, timer, targetEq, early, fields⟩
    rw [targetEq]
    exact target_of_fields ledger timer
  · simp only [early, ite_false] at demand
    cases demand

theorem timerDemand_timeout {actor : Actor}
    (pending : M.timerDemand config state = some (.timeout actor)) :
    ∃ recovery head rest deadline, G.senderRecovery config.toConfig state = some recovery ∧
      recovery.outstanding = head :: rest ∧ recovery.deadline = some deadline ∧
      deadline ≤ recovery.now ∧ head.lastAt + recovery.rto ≤ recovery.now ∧ actor = config.sender := by
  obtain ⟨recovery, head, rest, deadline, target, runtime, ledger, timer, targetEq, demand⟩ := timerDemand_some pending
  by_cases early : recovery.now < target
  · simp only [early, ite_true] at demand
    cases demand
  · have due : max deadline (head.lastAt + recovery.rto) ≤ recovery.now := by
      rw [← targetEq]
      omega
    have bounds := Nat.max_le.mp due
    simp only [early, ite_false] at demand
    have actorEq : actor = config.sender := by cases demand; rfl
    exact ⟨recovery, head, rest, deadline, runtime, ledger, timer, bounds.1, bounds.2, actorEq⟩

theorem clock_timerDemand_persistent (frame : Endpoint.ClockFrame before after)
    (runtime : before.recovery = some recovery) (updated : after.recovery = some current)
    (oldState : G.senderRecovery config.toConfig state = some recovery)
    (newState : G.senderRecovery config.toConfig nextState = some current)
    (distance : remaining current = remaining recovery) : M.timerDemand config nextState = M.timerDemand config state :=
  timerDemand_persistent oldState newState (clock_target frame runtime updated) distance

end Netlib.Check.CampusTCPTwoProgressTimer
