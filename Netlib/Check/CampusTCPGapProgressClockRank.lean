import Netlib.Check.CampusTCPGapProgressContextClock

/-!
# Clock rank and demand laws for held-gap progress

Actual clocks retain packet work and change only the selected endpoint time.
A full waiting tick reduces the current sender timer distance.
-/

namespace Netlib.Check.CampusTCPGapProgressEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPGapProgressStart (GapInitial NativeEnv)
open CampusTCPGapProgressSetup (config)

namespace M
export CampusTCPGapProgressMonitor (Monitor Demand nextDemand nextAction senderRecovery serves Allowed freeClock)
end M

variable {input : Input} {complete : H.Completed input.active input.passive}
  {cut current : Cut input complete} {sender : Actor} {lower upper : List UInt8}
  {initial : GapInitial cut sender lower upper} {native : NativeEnv cut initial.gateway.seed.entry}
  {quantum allowance : Nat} {monitor : M.Monitor} {actor : Actor} {millis : Nat} {actual : Step input}
  {demand : M.Demand}

theorem Clocked.next_action (clocked : Clocked initial native quantum allowance current monitor actor millis actual) :
    M.nextAction (config initial native quantum allowance) clocked.move.after.report.final monitor =
      M.nextAction (config initial native quantum allowance) current.report.final monitor :=
  CampusTCPGapProgressMonitorFacts.Frame.nextAction clocked.placement.frame _ _

theorem Clocked.rank_le (clocked : Clocked initial native quantum allowance current monitor actor millis actual) :
    monitor.rank (config initial native quantum allowance) clocked.move.after.report.final ≤
      monitor.rank (config initial native quantum allowance) current.report.final := by
  by_cases waiting : monitor.waiting = true
  · have frame := clocked.placement.frame.endpointFrame sender
    cases runtime : (endpoint current.endpoints sender).recovery with
    | none =>
      simp only [CampusTCPGapProgressMonitor.Monitor.rank, waiting, ite_true, M.senderRecovery,
        current.connection, clocked.move.after.connection, config, frame.recovery, runtime, Option.map_none]
      exact Nat.le_refl _
    | some recovery =>
      have updated := frame.runtime runtime
      have monotone : recovery.now ≤ (endpoint clocked.move.after.endpoints sender).now := by
        simpa only [Endpoint.State.now, runtime, Option.map_some, Option.getD_some] using frame.monotone
      cases deadline : recovery.deadline with
      | none =>
        simp only [CampusTCPGapProgressMonitor.Monitor.rank, waiting, ite_true, M.senderRecovery,
          current.connection, clocked.move.after.connection, config, runtime, updated, deadline,
          Option.getD_none, Nat.sub_self]
        exact Nat.le_refl _
      | some due =>
        have slots := CampusTCPGapProgressMonitor.waitSlots_mono
          (quantum := (config initial native quantum allowance).quantum)
          (show due - (endpoint clocked.move.after.endpoints sender).now ≤ due - recovery.now by omega)
        simpa only [CampusTCPGapProgressMonitor.Monitor.rank, waiting, ite_true, M.senderRecovery,
          current.connection, clocked.move.after.connection, config, runtime, updated, deadline,
          Option.getD_some, CampusTCPGapProgressMonitor.waitSlots] using Nat.add_le_add_right (Nat.add_le_add_right slots 9) _
  · have active := Bool.eq_false_iff.mpr waiting
    simp only [CampusTCPGapProgressMonitor.Monitor.rank, active, Bool.false_eq_true, ite_false]
    exact Nat.le_refl _

private theorem served_clock_fields (config : CampusTCPGapProgressMonitor.Config) (before : State input)
    (monitor : M.Monitor) (pending : M.nextDemand config before monitor = some demand)
    (served : M.serves demand (.advanceClock actor millis) = true) :
    ∃ recovery due, monitor.waiting = true ∧ M.senderRecovery config before = some recovery ∧
      recovery.deadline = some due ∧ recovery.now < due ∧ actor = config.sender ∧
      millis = min (recovery.now + config.quantum) due := by
  by_cases waiting : monitor.waiting = true
  · simp only [M.nextDemand, waiting, ite_true] at pending
    cases runtime : M.senderRecovery config before with
    | none => simp only [runtime, bind, Option.bind, reduceCtorEq] at pending
    | some recovery =>
      cases deadline : recovery.deadline with
      | none => simp only [runtime, deadline, bind, Option.bind, reduceCtorEq] at pending
      | some due =>
        simp only [runtime, deadline, bind, Option.bind] at pending
        by_cases early : recovery.now < due
        · simp only [early, ite_true, pure, Option.some.injEq] at pending
          subst demand
          have event := CampusTCPGapProgressMonitorFacts.serves_tick config.sender _ _ |>.mp served
          have actors : actor = config.sender ∧ millis = min (recovery.now + config.quantum) due := by
            cases event
            exact ⟨rfl, rfl⟩
          exact ⟨recovery, due, waiting, rfl, deadline, early, actors⟩
        · simp only [early, ite_false, pure, Option.some.injEq] at pending
          subst demand
          have event := CampusTCPGapProgressMonitorFacts.serves_timeout config.sender _ |>.mp served
          cases event
  · have active := Bool.eq_false_iff.mpr waiting
    obtain ⟨action, _, selected⟩ := CampusTCPGapProgressMonitorFacts.nextDemand_action_exists
      config before monitor active demand pending
    rcases selected with rfl | ⟨packet, rfl⟩
    · have event := CampusTCPGapProgressMonitorFacts.serves_operation _ _ |>.mp served
      cases action <;> cases event
    · have event := CampusTCPGapProgressMonitorFacts.serves_resolution _ _ _ |>.mp served
      rcases event with event | event
      · cases action <;> cases event
      · cases event

theorem Clocked.serves_decreases (clocked : Clocked initial native quantum allowance current monitor actor millis actual)
    (positive : 0 < quantum)
    (pending : M.nextDemand (config initial native quantum allowance) current.report.final monitor = some demand)
    (served : M.serves demand actual.event = true) :
    monitor.rank (config initial native quantum allowance) clocked.move.after.report.final <
      monitor.rank (config initial native quantum allowance) current.report.final := by
  rw [clocked.event] at served
  obtain ⟨recovery, due, waiting, runtime, deadline, early, actorEq, millisEq⟩ :=
    served_clock_fields _ _ _ pending served
  change actor = sender at actorEq
  subst actor
  have endpointRuntime : (endpoint current.endpoints sender).recovery = some recovery := by
    simpa only [M.senderRecovery, current.connection, config] using runtime
  have updated := clocked.sender_recovery endpointRuntime
  have updatedTarget := updated.trans (congrArg (fun time => some { recovery with now := time }) millisEq)
  exact CampusTCPGapProgressMonitor.rank_tick _ positive _ _ _ waiting recovery runtime deadline early updatedTarget

theorem Clocked.sender_recovery_free (clocked : Clocked initial native quantum allowance current monitor actor millis actual)
    (waiting : monitor.waiting = true)
    (free : M.freeClock (config initial native quantum allowance) current.report.final monitor actual.event = true) :
    M.senderRecovery (config initial native quantum allowance) clocked.move.after.report.final =
      M.senderRecovery (config initial native quantum allowance) current.report.final := by
  rw [clocked.event] at free
  by_cases selected : actor = sender
  · subst actor
    have sameActor : (sender != sender) = false := by cases sender <;> rfl
    simp only [M.freeClock, current.connection, waiting, config, Bool.not_true, sameActor, Bool.false_or,
      Bool.and_eq_true, beq_iff_eq] at free
    simp only [M.senderRecovery, current.connection, clocked.move.after.connection, config]
    rw [clocked.selected, Endpoint.clockState, free.2]
    cases runtime : (endpoint current.endpoints sender).recovery with
    | none => rfl
    | some recovery =>
      simp only [Endpoint.State.now, runtime, Option.map_some, Option.getD_some]
  · have peer : sender = actor.other := by cases sender <;> cases actor <;> simp_all [Actor.other]
    simp only [M.senderRecovery, current.connection, clocked.move.after.connection, config]
    exact (congrArg (fun selected => (endpoint clocked.move.after.endpoints selected).recovery) peer).trans
      ((congrArg Endpoint.State.recovery clocked.peer).trans
        (congrArg (fun selected => (endpoint current.endpoints selected).recovery) peer).symm)

theorem Clocked.pending_persistent (clocked : Clocked initial native quantum allowance current monitor actor millis actual)
    (positive : 0 < quantum)
    (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event)
    (equal : monitor.rank (config initial native quantum allowance) clocked.move.after.report.final =
      monitor.rank (config initial native quantum allowance) current.report.final)
    (pending : M.nextDemand (config initial native quantum allowance) current.report.final monitor = some demand) :
    M.nextDemand (config initial native quantum allowance) clocked.move.after.report.final monitor = some demand := by
  by_cases waiting : monitor.waiting = true
  · obtain ⟨choice, _⟩ := CampusTCPGapProgressMonitorFacts.allowed_at _ _ _ _ demand pending |>.mp allowed
    rcases choice with served | free
    · have decreases := clocked.serves_decreases positive pending served
      omega
    · have same := clocked.sender_recovery_free waiting free
      simpa only [M.nextDemand, waiting, ite_true, same] using pending
  · have active := Bool.eq_false_iff.mpr waiting
    simp only [M.nextDemand, active, Bool.false_eq_true, ite_false, clocked.next_action] at *
    exact pending

end Netlib.Check.CampusTCPGapProgressEvidence
