import Netlib.Check.CampusTCPStartupCriticalClock
import Netlib.Check.CampusTCPStartupJobSource

/-!
# Protected startup work across actual clocks

Clocks keep the queue and phase. A selected timer may stay fixed or advance
only to its full guarded target; equal rank retains its demand.
-/

namespace Netlib.Check.CampusTCPStartupCriticalClockFrame

open CampusTCPModel

namespace P
export CampusTCPStartupSelection (Protection phaseRank criticalPath criticalTimer choose retain path useful timer timerDemand demand clockAllowed)
end P
namespace J
export CampusTCPStartupJobs (Job inventory)
end J
namespace M
export CampusTCPStartupMonitor (Monitor advanceProtection)
end M
namespace R
export CampusTCPStartupCriticalRank (rank retain_timer critical_pending)
end R
namespace T
export CampusTCPStartupTimerWait (distance remaining)
end T
namespace Q
export CampusTCPStartupJobDrainComplete (QueueFrame)
end Q

variable {input : Input} {events : List Event} {report : Report input events}
variable {config : CampusTCPStartupTransferMonitor.Config} {monitor : M.Monitor}
variable {current : TCPHandshakeRecovery.State input.active input.passive}
variable {actual : Step input} {actor : Actor} {millis : Nat}

private theorem critical_good (selected : P.criticalPath state = some job) :
    job ∈ J.inventory state ∧ P.useful (P.phaseRank state) job = true := by
  unfold P.criticalPath at selected
  split at selected
  · rename_i phase
    cases first : (J.inventory state).find? (fun job => decide (job.actor = .client ∧ job.kind = .finalAck)) with
    | none =>
      simp only [first, Option.or] at selected
      exact ⟨List.mem_of_find?_eq_some selected, by simpa only [phase] using List.find?_some selected⟩
    | some found =>
      simp only [first, Option.or, Option.some.injEq] at selected
      subst job
      have fields : found.actor = .client ∧ found.kind = .finalAck := of_decide_eq_true
        (List.find?_some (p := fun job : J.Job _ => decide (job.actor = .client ∧ job.kind = .finalAck)) first)
      exact ⟨List.mem_of_find?_eq_some first, by simp only [P.useful, phase, fields.1, fields.2]; decide⟩
  · exact ⟨List.mem_of_find?_eq_some selected, List.find?_some selected⟩

private theorem path_exists (member : job ∈ J.inventory state) : ∃ selected, P.path state job.outputIndex = some selected := by
  cases found : P.path state job.outputIndex with
  | none =>
    have absent := List.find?_eq_none.mp found job member
    exact False.elim (absent (by simp only [decide_true]))
  | some selected => exact ⟨selected, rfl⟩

private theorem Report.chosen_path (report : Report input events) (selected : P.choose report.final = some (.path index)) :
    ∃ job, P.path report.final index = some job ∧ P.useful (P.phaseRank report.final) job = true := by
  cases found : P.criticalPath report.final with
  | none =>
    cases pending : P.criticalTimer report.final <;> simp only [P.choose, found, pending, Option.map_none, Option.map_some] at selected
    all_goals cases selected
  | some chosen =>
    have indexEq : chosen.outputIndex = index := by
      have same : (some (.path chosen.outputIndex) : Option P.Protection) = some (.path index) := by simpa only [P.choose, found] using selected
      cases same
      rfl
    obtain ⟨member, relevant⟩ := critical_good found
    obtain ⟨job, atIndex⟩ := path_exists member
    have same := CampusTCPStartupJobSource.Report.useful_same report job chosen
      (CampusTCPStartupSelection.selected_member atIndex) member
      (CampusTCPStartupSelection.selected_index atIndex) (P.phaseRank report.final)
    exact ⟨job, indexEq ▸ atIndex, same.trans relevant⟩

private theorem Report.retained_path (report : Report input events)
    (selected : P.retain report.final held = some (.path index)) :
    ∃ job, P.path report.final index = some job ∧ P.useful (P.phaseRank report.final) job = true := by
  cases held with
  | none => exact Report.chosen_path report selected
  | some protection =>
    cases protection with
    | timer actor =>
      by_cases same : P.criticalTimer report.final = some actor
      · simp only [P.retain, same, ↓reduceIte] at selected
        cases selected
      · exact Report.chosen_path report (by simpa only [P.retain, same, ↓reduceIte] using selected)
    | path old =>
      cases found : P.path report.final old with
      | none => exact Report.chosen_path report (by simpa only [P.retain, found] using selected)
      | some job =>
        by_cases relevant : P.useful (P.phaseRank report.final) job = true
        · have same : old = index := by
            have equal : (some (.path old) : Option P.Protection) = some (.path index) := by simpa only [P.retain, found, relevant, ↓reduceIte] using selected
            cases equal
            rfl
          exact ⟨job, same ▸ found, relevant⟩
        · exact Report.chosen_path report (by simpa only [P.retain, found, relevant, Bool.false_eq_true, ↓reduceIte] using selected)

private theorem none_choose (selected : P.retain state held = none) : P.choose state = none := by
  cases held with
  | none => exact selected
  | some held =>
    cases held with
    | timer actor =>
      by_cases same : P.criticalTimer state = some actor
      · simp only [P.retain, same, ↓reduceIte] at selected
        cases selected
      · simpa only [P.retain, same, ↓reduceIte] using selected
    | path index =>
      cases found : P.path state index with
      | none => simpa only [P.retain, found] using selected
      | some job =>
        by_cases relevant : P.useful (P.phaseRank state) job = true
        · simp only [P.retain, found, relevant, ↓reduceIte] at selected
          cases selected
        · simpa only [P.retain, found, relevant, Bool.false_eq_true, ↓reduceIte] using selected

private theorem Report.retain_idempotent (report : Report input events) :
    P.retain report.final (P.retain report.final held) = P.retain report.final held := by
  cases selected : P.retain report.final held with
  | none => exact none_choose selected
  | some protection =>
    cases protection with
    | path index =>
      obtain ⟨job, found, relevant⟩ := Report.retained_path report selected
      exact CampusTCPStartupSelection.retain_live_path found relevant
    | timer actor => exact CampusTCPStartupSelection.retain_timer (R.retain_timer selected)

private theorem retain_frame (frame : Q.QueueFrame before after) (phase : P.phaseRank after = P.phaseRank before) :
    P.retain after held = P.retain before held := by
  have paths (index : Nat) : P.path after index = P.path before index :=
    CampusTCPStartupSelection.path_same (congrArg Theory.PacketCustody.State.pending frame.custody)
      (congrArg (fun work => work.pending) frame.work)
  have chosen : P.choose after = P.choose before := by
    simp only [P.choose, P.criticalPath, P.criticalTimer, phase, frame.inventory]
  cases held with
  | none => exact chosen
  | some held =>
    cases held with
    | path index => simp only [P.retain, paths, phase, chosen]
    | timer actor => simp only [P.retain, P.criticalTimer, phase, chosen]; rfl

private theorem shapes (connected : actual.before.connection = .recovering current)
    (event : actual.event = .startupClock actor millis) :
    P.phaseRank actual.result.state = P.phaseRank actual.before ∧ Q.QueueFrame actual.before actual.result.state := by
  obtain ⟨clock⟩ := CampusTCPStartupClockStep.Step.recorded_clock actual connected event
  exact ⟨by simp only [P.phaseRank, connected, clock.after, clock.phase],
    (CampusTCPStartupJobDrainComplete.Step.clock_frame actual event).1⟩

theorem protection (report : Report input events) (before : actual.before = report.final)
    (connected : actual.before.connection = .recovering current)
    (event : actual.event = .startupClock actor millis) :
    M.advanceProtection config monitor actual = P.retain actual.before monitor.protection := by
  obtain ⟨phase, queues⟩ := shapes connected event
  have frame := retain_frame (held := P.retain actual.before monitor.protection) queues phase
  simp only [M.advanceProtection, phase, Nat.lt_irrefl, ↓reduceIte, event, CampusTCPStartupMonitor.expired_clock]
  rw [frame, before]
  exact Report.retain_idempotent report

private theorem retained (report : Report input events) (before : actual.before = report.final)
    (connected : actual.before.connection = .recovering current)
    (event : actual.event = .startupClock actor millis) :
    P.retain actual.result.state (M.advanceProtection config monitor actual) = P.retain actual.before monitor.protection := by
  obtain ⟨phase, queues⟩ := shapes connected event
  rw [protection report before connected event, retain_frame queues phase, before]
  exact Report.retain_idempotent report

private theorem clock_bounds (connected : actual.before.connection = .recovering current)
    (permitted : P.clockAllowed config actual.before monitor.protection actor millis = true) :
    (current.timer actor.recoverySide).now ≤ millis ∧ millis ≤ (current.timer actor.recoverySide).now + config.transfer.quantum := by
  simp only [P.clockAllowed, P.timer, connected, Bool.and_eq_true] at permitted
  exact of_decide_eq_true permitted.1

private theorem timer_frame (clock : CampusTCPStartupClockStep.Recorded actual current actor millis) (selected : Actor)
    (different : selected ≠ actor) : clock.control.result.state.timer selected.recoverySide = current.timer selected.recoverySide := by
  cases actor <;> cases selected <;> first | (solve | exact clock.peer) | (solve | exact False.elim (different rfl))

private theorem distance_monotone (pending : state.status = .pending flight) (lower : state.now ≤ millis) :
    T.distance quantum { state with now := millis } ≤ T.distance quantum state := by
  simp only [T.distance, T.remaining, pending]
  exact Nat.add_le_add_right (CampusTCPRecoveryRoundMonitor.waitSlots_mono (by omega)) 1

theorem nonincrease (report : Report input events) (before : actual.before = report.final)
    (connected : actual.before.connection = .recovering current)
    (event : actual.event = .startupClock actor millis)
    (permitted : P.clockAllowed config actual.before monitor.protection actor millis = true) :
    R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) ≤
      R.rank config.transfer.quantum actual.before monitor.protection := by
  obtain ⟨clock⟩ := CampusTCPStartupClockStep.Step.recorded_clock actual connected event
  obtain ⟨phase, queues⟩ := shapes connected event
  have later := retained (config := config) (monitor := monitor) report before connected event
  by_cases complete : P.phaseRank actual.before = 4
  · simp only [R.rank, phase, complete, ↓reduceIte, Nat.le_refl]
  simp only [R.rank, phase, complete, ↓reduceIte, later]
  cases selectedAt : P.retain actual.before monitor.protection with
  | none => exact Nat.le_refl _
  | some protection =>
    cases protection with
    | path index =>
      dsimp only
      rw [CampusTCPStartupSelection.path_same (congrArg Theory.PacketCustody.State.pending queues.custody)
        (congrArg (fun work => work.pending) queues.work)]
      exact Nat.le_refl _
    | timer chosen =>
      have reachable := CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report (before ▸ connected)
      obtain ⟨flight, pending⟩ := R.critical_pending connected reachable (R.retain_timer selectedAt)
      simp only [P.timer, connected, clock.after]
      by_cases same : chosen = actor
      · subst chosen
        rw [clock.selected]
        exact Nat.add_le_add_right (distance_monotone pending (clock_bounds connected permitted).1) _
      · rw [timer_frame clock chosen same]
        exact Nat.le_refl _

private theorem selected_timer_same (report : Report input events) (before : actual.before = report.final)
    (connected : actual.before.connection = .recovering current)
    (event : actual.event = .startupClock actor millis)
    (permitted : P.clockAllowed config actual.before monitor.protection actor millis = true)
    (held : P.retain actual.before monitor.protection = some (.timer actor))
    (equal : R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) =
      R.rank config.transfer.quantum actual.before monitor.protection) : millis = (current.timer actor.recoverySide).now := by
  by_cases sameNow : millis = (current.timer actor.recoverySide).now
  · exact sameNow
  exfalso
  have changed := sameNow
  have bounds := clock_bounds connected permitted
  have positive : 0 < config.transfer.quantum := by omega
  have reachable := CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report (before ▸ connected)
  obtain ⟨flight, pending⟩ := R.critical_pending connected reachable (R.retain_timer held)
  simp only [P.clockAllowed, P.timer, connected, held, ↓reduceIte, Bool.and_eq_true] at permitted
  have alternatives : millis = (current.timer actor.recoverySide).now ∨
      P.timerDemand config.transfer.quantum actual.before actor = some (.startupClock actor millis) := by
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using permitted.2
  rcases alternatives with same | full
  · exact changed same
  simp only [P.timerDemand, P.timer, connected, pending] at full
  split at full
  · rename_i early
    have targetEq := (Event.startupClock.inj (Option.some.inj full)).2
    have strict := CampusTCPStartupCriticalClock.served_strict connected held pending early positive
      (event.trans (congrArg (Event.startupClock actor) targetEq.symm))
    omega
  · cases full

theorem persistent (report : Report input events) (before : actual.before = report.final)
    (connected : actual.before.connection = .recovering current)
    (event : actual.event = .startupClock actor millis)
    (permitted : P.clockAllowed config actual.before monitor.protection actor millis = true)
    (equal : R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) =
      R.rank config.transfer.quantum actual.before monitor.protection) :
    P.demand config actual.result.state (M.advanceProtection config monitor actual) = P.demand config actual.before monitor.protection := by
  obtain ⟨clock⟩ := CampusTCPStartupClockStep.Step.recorded_clock actual connected event
  obtain ⟨phase, queues⟩ := shapes connected event
  have later := retained (config := config) (monitor := monitor) report before connected event
  simp only [P.demand, later]
  cases selected : P.retain actual.before monitor.protection with
  | none => rw [phase]
  | some protection =>
    cases protection with
    | path index =>
      dsimp only
      rw [CampusTCPStartupSelection.path_same (congrArg Theory.PacketCustody.State.pending queues.custody)
        (congrArg (fun work => work.pending) queues.work)]
    | timer chosen =>
      simp only [P.timerDemand, P.timer, connected, clock.after]
      by_cases same : chosen = actor
      · subst chosen
        rw [clock.selected, selected_timer_same report before connected event permitted selected equal]
      · rw [timer_frame clock chosen same]


theorem Report.retained_useful (report : Report input events) {heldProtection : Option P.Protection}
    (held : P.retain report.final heldProtection = some (.path index))
    (found : P.path report.final index = some job) : P.useful (P.phaseRank report.final) job = true := by
  obtain ⟨selected, selectedAt, useful⟩ := Report.retained_path report held
  have same : selected = job := Option.some.inj (selectedAt.symm.trans found)
  simpa only [same] using useful

end Netlib.Check.CampusTCPStartupCriticalClockFrame
