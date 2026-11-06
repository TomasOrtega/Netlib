import Netlib.Check.CampusTCPRecoveryRoundClock

/-!
# Clock rank and demand laws

Actual clocks preserve packet work and advance only the selected endpoint time.
A clock that serves the waiting sender's tick reduces the remaining timer slots.
-/

namespace Netlib.Check.CampusTCPRecoveryRoundEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRound (Cut)

namespace M
export CampusTCPRecoveryRoundMonitor (Monitor Demand nextDemand clientRecovery serves Allowed freeClock)
end M

variable {input : Input} {events : List Event} {report : Report input events}
  {complete : H.Completed input.active input.passive} {request : Request input}
  {initial : Initial report complete request} {native : NativeEnv initial} {quantum : Nat}
  {current : Cut input complete} {monitor : M.Monitor} {actor : Actor} {millis : Nat} {actual : Step input}
  {demand : M.Demand}

private theorem nextAction_snapshot (config : CampusTCPRoundMonitor.Config) (state : State input)
    (monitor : CampusTCPRoundMonitor.Monitor) :
    CampusTCPRoundMonitor.nextAction config (CampusTCPRoundStutter.snapshot state) monitor =
      CampusTCPRoundMonitor.nextAction config state monitor := by
  cases monitor.phase <;> rfl

theorem Clocked.next_action (clocked : Clocked initial native quantum current monitor actor millis actual) :
    CampusTCPRoundMonitor.nextAction (CampusTCPRecoveryRoundPhaseBase.config initial native quantum).toConfig
      clocked.move.after.report.final monitor.round =
    CampusTCPRoundMonitor.nextAction (CampusTCPRecoveryRoundPhaseBase.config initial native quantum).toConfig
      current.report.final monitor.round := by
  have same := congrArg (fun state => CampusTCPRoundMonitor.nextAction
    (CampusTCPRecoveryRoundPhaseBase.config initial native quantum).toConfig state monitor.round)
    clocked.placement.frame.fixed
  simpa only [nextAction_snapshot] using same.symm

theorem Clocked.rank_le (clocked : Clocked initial native quantum current monitor actor millis actual) :
    monitor.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) clocked.move.after.report.final ≤
      monitor.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final := by
  by_cases waiting : monitor.waiting = true
  · have frame := clocked.placement.frame.endpointFrame .client
    cases runtime : (endpoint current.endpoints .client).recovery with
    | none =>
      simp only [CampusTCPRecoveryRoundMonitor.Monitor.rank, waiting, ite_true, M.clientRecovery,
        current.connection, clocked.move.after.connection, frame.recovery, runtime, Option.map_none]
      exact Nat.le_refl _
    | some recovery =>
      have updated := frame.runtime runtime
      have monotone : recovery.now ≤ (endpoint clocked.move.after.endpoints .client).now := by
        simpa only [Endpoint.State.now, runtime, Option.map_some, Option.getD_some] using frame.monotone
      cases deadline : recovery.deadline with
      | none =>
        simp only [CampusTCPRecoveryRoundMonitor.Monitor.rank, waiting, ite_true, M.clientRecovery,
          current.connection, clocked.move.after.connection, runtime, updated, deadline,
          Option.getD_none, Nat.sub_self]
        exact Nat.le_refl _
      | some due =>
        have slots := CampusTCPRecoveryRoundMonitor.waitSlots_mono
          (quantum := (CampusTCPRecoveryRoundPhaseBase.config initial native quantum).quantum)
          (show due - (endpoint clocked.move.after.endpoints .client).now ≤ due - recovery.now by omega)
        simpa only [CampusTCPRecoveryRoundMonitor.Monitor.rank, waiting, ite_true, M.clientRecovery,
          current.connection, clocked.move.after.connection, runtime, updated, deadline,
          Option.getD_some] using Nat.add_le_add_right (Nat.add_le_add_right slots 9) _
  · have active := Bool.eq_false_iff.mpr waiting
    simp only [CampusTCPRecoveryRoundMonitor.Monitor.rank, active, Bool.false_eq_true, ite_false]
    exact Nat.le_refl _

private theorem served_clock_fields (config : CampusTCPRecoveryRoundMonitor.Config) (before : State input)
    (monitor : M.Monitor) (pending : M.nextDemand config before monitor = some demand)
    (served : M.serves demand (.advanceClock actor millis) = true) :
    ∃ recovery due, monitor.waiting = true ∧ M.clientRecovery before = some recovery ∧
      recovery.deadline = some due ∧ recovery.now < due ∧ actor = .client ∧
      millis = min (recovery.now + config.quantum) due := by
  by_cases waiting : monitor.waiting = true
  · simp only [M.nextDemand, waiting, ite_true] at pending
    cases runtime : M.clientRecovery before with
    | none => simp only [runtime, bind, Option.bind, reduceCtorEq] at pending
    | some recovery =>
      cases deadline : recovery.deadline with
      | none => simp only [runtime, deadline, bind, Option.bind, reduceCtorEq] at pending
      | some due =>
        simp only [runtime, deadline, bind, Option.bind] at pending
        by_cases early : recovery.now < due
        · simp only [early, ite_true, pure, Option.some.injEq] at pending
          subst demand
          have event := CampusTCPRecoveryRoundMonitorFacts.serves_tick _ _ |>.mp served
          have actors : actor = .client ∧ millis = min (recovery.now + config.quantum) due := by
            cases event
            exact ⟨rfl, rfl⟩
          exact ⟨recovery, due, waiting, rfl, deadline, early, actors⟩
        · simp only [early, ite_false, pure, Option.some.injEq] at pending
          subst demand
          have event := CampusTCPRecoveryRoundMonitorFacts.serves_timeout _ |>.mp served
          cases event
  · have active := Bool.eq_false_iff.mpr waiting
    obtain ⟨action, _, selected⟩ := CampusTCPRecoveryRoundMonitorFacts.nextDemand_action_exists
      config before monitor active demand pending
    rcases selected with rfl | ⟨packet, rfl⟩
    · have event := CampusTCPRecoveryRoundMonitorFacts.serves_operation _ _ |>.mp served
      cases action <;> cases event
    · have event := CampusTCPRecoveryRoundMonitorFacts.serves_resolution _ _ _ |>.mp served
      rcases event with event | event
      · cases action <;> cases event
      · cases event

theorem Clocked.serves_decreases (clocked : Clocked initial native quantum current monitor actor millis actual)
    (positive : 0 < quantum)
    (pending : M.nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum)
      current.report.final monitor = some demand)
    (served : M.serves demand actual.event = true) :
    monitor.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) clocked.move.after.report.final <
      monitor.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final := by
  rw [clocked.event] at served
  obtain ⟨recovery, due, waiting, runtime, deadline, early, actorEq, millisEq⟩ :=
    served_clock_fields _ _ _ pending served
  subst actor
  have endpointRuntime : (endpoint current.endpoints .client).recovery = some recovery := by
    simpa only [M.clientRecovery, current.connection] using runtime
  have updated := clocked.client_recovery endpointRuntime
  have updatedTarget := updated.trans (congrArg (fun time => some { recovery with now := time }) millisEq)
  exact CampusTCPRecoveryRoundMonitor.rank_tick _ positive _ _ _ waiting recovery runtime deadline early updatedTarget

theorem Clocked.client_recovery_free (clocked : Clocked initial native quantum current monitor actor millis actual)
    (waiting : monitor.waiting = true)
    (free : M.freeClock (CampusTCPRecoveryRoundPhaseBase.config initial native quantum)
      current.report.final monitor actual.event = true) :
    M.clientRecovery clocked.move.after.report.final = M.clientRecovery current.report.final := by
  rw [clocked.event] at free
  cases actor with
  | server =>
    simp only [M.clientRecovery, current.connection, clocked.move.after.connection]
    exact congrArg Endpoint.State.recovery clocked.peer
  | client =>
    simp only [M.freeClock, current.connection, waiting, Bool.not_true, Bool.false_or,
      Bool.and_eq_true, beq_iff_eq] at free
    simp only [M.clientRecovery, current.connection, clocked.move.after.connection]
    rw [clocked.selected, Endpoint.clockState, free.2]
    cases runtime : (endpoint current.endpoints .client).recovery with
    | none => rfl
    | some recovery =>
      simp only [Endpoint.State.now, runtime, Option.map_some, Option.getD_some]

theorem Clocked.pending_persistent (clocked : Clocked initial native quantum current monitor actor millis actual)
    (positive : 0 < quantum)
    (allowed : M.Allowed (CampusTCPRecoveryRoundPhaseBase.config initial native quantum)
      current.report.final monitor actual.event)
    (equal : monitor.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) clocked.move.after.report.final =
      monitor.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final)
    (pending : M.nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum)
      current.report.final monitor = some demand) :
    M.nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum)
      clocked.move.after.report.final monitor = some demand := by
  by_cases waiting : monitor.waiting = true
  · obtain ⟨choice, _⟩ := CampusTCPRecoveryRoundMonitorFacts.allowed_at _ _ _ _ demand pending |>.mp allowed
    rcases choice with served | free
    · have decreases := clocked.serves_decreases positive pending served
      omega
    · have same := clocked.client_recovery_free waiting free
      simpa only [M.nextDemand, waiting, ite_true, same] using pending
  · have active := Bool.eq_false_iff.mpr waiting
    simp only [M.nextDemand, active, Bool.false_eq_true, ite_false, clocked.next_action] at *
    exact pending

end Netlib.Check.CampusTCPRecoveryRoundEvidence
