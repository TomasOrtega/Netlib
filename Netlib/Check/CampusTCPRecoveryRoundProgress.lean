import Netlib.Check.CampusTCPRecoveryRoundDemand
import Netlib.Check.CampusTCPRecoveryRoundPhaseLoss
import Netlib.Check.CampusTCPRecoveryRoundRank
import Netlib.Check.CampusTCPRecoveryRoundSelected
import Netlib.Check.CampusTCPRecoveryRoundClockRank

/-!
# Concrete progress in a timed TCP recovery round

Each state witness retains the actual current report.
Completion retains the actual read and retired sender range.
-/

namespace Netlib.Check.CampusTCPRecoveryRoundProgress

open CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRound (Cut)
open CampusTCPRecoveryRoundEvidence
open CampusTCPRecoveryRoundMonitor

variable {input : Input} {events : List Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}
variable {initial : Initial report complete request} {native : NativeEnv initial} {quantum : Nat}
variable {current : Cut input complete} {monitor : Monitor}
variable {demand : Demand}

def SuffixPassed (initial : Initial report complete request) (current : Cut input complete) : Prop :=
  ∃ extra, current.report.steps = initial.start.next.report.steps ++ extra ∧
    ∀ actual ∈ extra, actual.result.passed = true

theorem SuffixPassed.append (passed : SuffixPassed initial current)
    (move : CampusTCPRoundPhaseBase.Move current actual) : SuffixPassed initial move.after := by
  obtain ⟨extra, history, accepted⟩ := passed
  refine ⟨extra ++ [actual], ?_, ?_⟩
  · rw [move.history, history, List.append_assoc]
  · intro step member
    rcases List.mem_append.mp member with old | fresh
    · exact accepted step old
    · exact List.mem_singleton.mp fresh ▸ move.passed

def Invariant (initial : Initial report complete request) (native : NativeEnv initial) (quantum : Nat)
    (state : State input × Monitor) : Prop :=
  ∃ current : Cut input complete, current.report.final = state.1 ∧ SuffixPassed initial current ∧
    Nonempty (Evidence initial native quantum current state.2)

def Completed (initial : Initial report complete request) (_native : NativeEnv initial) (_quantum : Nat)
    (state : State input × Monitor) : Prop :=
  ∃ current : Cut input complete, current.report.final = state.1 ∧ SuffixPassed initial current ∧
    ∃ retries, Nonempty (Done initial current state.2 retries)

theorem initial_invariant (initial : Initial report complete request) (native : NativeEnv initial) (quantum : Nat) :
    Invariant initial native quantum (initial.state, Monitor.initial) :=
  ⟨Cut.ofPrepared initial.start, rfl, ⟨[], by simp only [List.append_nil]; rfl, by simp⟩,
    ⟨initial_evidence initial native quantum⟩⟩

theorem pending_positive (evidence : Evidence initial native quantum current monitor)
    (pending : nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum)
      current.report.final monitor = some demand) :
    0 < monitor.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final := by
  by_cases positive : 0 < monitor.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final
  · exact positive
  · have zero : monitor.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final = 0 := by omega
    obtain ⟨retries, ⟨done⟩⟩ := evidence.done_of_rank_zero zero
    rw [done.demand native quantum] at pending
    cases pending

theorem finished (invariant : Invariant initial native quantum state)
    (zero : state.2.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) state.1 = 0) :
    Completed initial native quantum state := by
  obtain ⟨current, final, passed, ⟨evidence⟩⟩ := invariant
  rw [← final] at zero
  exact ⟨current, final, passed, evidence.done_of_rank_zero zero⟩

theorem selected_step (evidence : Evidence initial native quantum current monitor) (positive : 0 < quantum)
    (pending : nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum)
      current.report.final monitor = some demand) :
    Nonempty (CampusTCPRecoveryRoundSelected.Selected initial native quantum current monitor demand) := by
  by_cases active : monitor.waiting = false
  · exact CampusTCPRecoveryRoundSelected.ordinary_selected evidence active pending
  · cases evidence with
    | needSend record =>
      simp only [record.monitorEq, Monitor.initial] at active
      exact False.elim (active trivial)
    | dataIngress record => exact False.elim (active record.waiting)
    | dataTicket record => exact False.elim (active record.waiting)
    | dataLink record => exact False.elim (active record.waiting)
    | needAck record => exact False.elim (active record.waiting)
    | ackIngress record => exact False.elim (active record.waiting)
    | ackTicket record => exact False.elim (active record.waiting)
    | ackLink record => exact False.elim (active record.waiting)
    | needRead record => exact False.elim (active record.waiting)
    | done record => exact False.elim (active record.waiting)
    | waiting record =>
      by_cases early : record.live.sender.recovery.now < record.live.sender.entry.lastAt + record.live.sender.recovery.rto
      · have offered := record.tick_demand native quantum early
        have same := Option.some.inj (pending.symm.trans offered)
        subst demand
        obtain ⟨actual, ⟨ticked⟩⟩ := record.tick_at native quantum positive early
        refine ⟨⟨actual, ticked.clocked.move, ticked.clocked.event, ?_, ?_⟩⟩
        · rw [ticked.clocked.observed]
          exact ⟨ticked.clocked.evidence⟩
        · rw [ticked.clocked.observed]
          exact ticked.decreases
      · have due : record.live.sender.entry.lastAt + record.live.sender.recovery.rto ≤ record.live.sender.recovery.now := by omega
        have offered := record.timeout_demand native quantum due
        have same := Option.some.inj (pending.symm.trans offered)
        subst demand
        obtain ⟨actual, move, event, ⟨next⟩⟩ := record.retry_at due (native := native) (quantum := quantum)
        refine ⟨⟨actual, move, event, ⟨.dataIngress next⟩, ?_⟩⟩
        apply rank_timeout (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) positive
          current.report.final move.after.report.final monitor _ record.waiting record.live.sender.recovery
          record.recovery record.live.sender.deadline due next.waiting _ next.phaseEq
        rw [next.retryCount, record.retryCount]

theorem canonical_advance (evidence : Evidence initial native quantum current monitor) (positive : 0 < quantum)
    (actual : Step input) (before : actual.before = current.report.final)
    (pending : nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum)
      current.report.final monitor = some demand) (event : actual.event = demand.event) :
    ∃ move : CampusTCPRoundPhaseBase.Move current actual,
      Nonempty (Evidence initial native quantum move.after
        (observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) monitor actual)) ∧
      (observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) monitor actual).rank
        (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) move.after.report.final <
        monitor.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final := by
  obtain ⟨selected⟩ := selected_step evidence positive pending
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event selected.actual actual
    (selected.move.beforeEq.trans before.symm) (selected.event.trans event.symm)
  cases same
  exact ⟨selected.move, selected.evidence, selected.decreases⟩

structure CheckedStep (initial : Initial report complete request) (native : NativeEnv initial) (quantum : Nat)
    (current : Cut input complete) (monitor : Monitor) (actual : Step input) where
  move : CampusTCPRoundPhaseBase.Move current actual
  evidence : Nonempty (Evidence initial native quantum move.after
    (observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) monitor actual))
  nonincrease : (observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) monitor actual).rank
      (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) move.after.report.final ≤
    monitor.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final
  persistent : ∀ demand,
    (observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) monitor actual).rank
        (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) move.after.report.final =
      monitor.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final →
    nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final monitor = some demand →
    nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) move.after.report.final
      (observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) monitor actual) = some demand
  advances : ∀ demand,
    nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final monitor = some demand →
    serves demand actual.event = true →
    (observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) monitor actual).rank
        (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) move.after.report.final <
      monitor.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final

private def strict_step (move : CampusTCPRoundPhaseBase.Move current actual)
    (evidence : Nonempty (Evidence initial native quantum move.after
      (observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) monitor actual)))
    (decreases : (observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) monitor actual).rank
        (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) move.after.report.final <
      monitor.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final) :
    CheckedStep initial native quantum current monitor actual :=
  ⟨move, evidence, Nat.le_of_lt decreases, by intro demand equal _; omega, by intro _ _ _; exact decreases⟩

private def clock_step (clocked : Clocked initial native quantum current monitor actor millis actual)
    (positive : 0 < quantum)
    (allowed : Allowed (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final monitor actual.event) :
    CheckedStep initial native quantum current monitor actual where
  move := clocked.move
  evidence := by rw [clocked.observed]; exact ⟨clocked.evidence⟩
  nonincrease := by rw [clocked.observed]; exact clocked.rank_le
  persistent := by
    intro demand equal pending
    rw [clocked.observed] at equal ⊢
    exact clocked.pending_persistent positive allowed equal pending
  advances := by
    intro demand pending served
    rw [clocked.observed]
    exact clocked.serves_decreases positive pending served

theorem checked_step (evidence : Evidence initial native quantum current monitor) (positive : 0 < quantum)
    (actual : Step input) (before : actual.before = current.report.final)
    (allowed : Allowed (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final monitor actual.event) :
    Nonempty (CheckedStep initial native quantum current monitor actual) := by
  classical
  by_cases clock : ∃ actor millis, actual.event = .advanceClock actor millis
  · obtain ⟨actor, millis, event⟩ := clock
    have guarded := (CampusTCPRecoveryRoundMonitorFacts.allowed_iff _ _ _ _).mp allowed |>.2
    have clockAllowed : clockAllowed (CampusTCPRecoveryRoundPhaseBase.config initial native quantum)
        current.report.final (.advanceClock actor millis) = true := by simpa only [event] using guarded
    obtain ⟨clocked⟩ := CampusTCPRecoveryRoundEvidence.Step.clock actual evidence actor millis before event clockAllowed
    exact ⟨clock_step clocked positive allowed⟩
  · obtain ⟨choice, _⟩ := (CampusTCPRecoveryRoundMonitorFacts.allowed_iff _ _ _ _).mp allowed
    rcases choice with ⟨demand, pending, served⟩ | free
    · cases demand with
      | operation action =>
        have event := (CampusTCPRecoveryRoundMonitorFacts.serves_operation action actual.event).mp served
        obtain ⟨move, next, decreases⟩ := canonical_advance evidence positive actual before pending event
        exact ⟨strict_step move next decreases⟩
      | resolution action id =>
        rcases (CampusTCPRecoveryRoundMonitorFacts.serves_resolution action id actual.event).mp served with event | event
        · obtain ⟨move, next, decreases⟩ := canonical_advance evidence positive actual before pending event
          exact ⟨strict_step move next decreases⟩
        · obtain ⟨dropped⟩ := evidence.drop_selected pending
          have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event dropped.actual actual
            (dropped.move.beforeEq.trans before.symm) (dropped.event.trans event.symm)
          cases same
          exact ⟨strict_step dropped.move dropped.evidence dropped.decreases⟩
      | tick target =>
        have event := (CampusTCPRecoveryRoundMonitorFacts.serves_tick target actual.event).mp served
        exact False.elim (clock ⟨.client, target, event⟩)
      | timeout =>
        have event := (CampusTCPRecoveryRoundMonitorFacts.serves_timeout actual.event).mp served
        obtain ⟨move, next, decreases⟩ := canonical_advance evidence positive actual before pending event
        exact ⟨strict_step move next decreases⟩
    · obtain ⟨actor, millis, event, _⟩ := CampusTCPRecoveryRoundMonitorFacts.freeClock_event _ _ _ _ free
      exact False.elim (clock ⟨actor, millis, event⟩)

structure EdgeFacts (initial : Initial report complete request) (native : NativeEnv initial) (quantum : Nat)
    (before after : State input × Monitor) (event : Event) : Prop where
  invariant : Invariant initial native quantum after
  nonincrease : after.2.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) after.1 ≤
    before.2.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) before.1
  persistent : ∀ demand,
    after.2.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) after.1 =
      before.2.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) before.1 →
    nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) before.1 before.2 = some demand →
    nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) after.1 after.2 = some demand
  advances : ∀ demand,
    nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) before.1 before.2 = some demand →
    serves demand event = true →
    after.2.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) after.1 <
      before.2.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) before.1

theorem transition (invariant : Invariant initial native quantum beforeState) (positive : 0 < quantum)
    (edge : (guardedSystem input (CampusTCPRecoveryRoundPhaseBase.config initial native quantum)).step
      beforeState event afterState) : EdgeFacts initial native quantum beforeState afterState event := by
  obtain ⟨current, final, passed, ⟨evidence⟩⟩ := invariant
  obtain ⟨allowed, actual, before, selected, after, observed⟩ := edge
  have atCurrent : actual.before = current.report.final := before.trans final.symm
  have allowedHere : Allowed (CampusTCPRecoveryRoundPhaseBase.config initial native quantum)
      current.report.final beforeState.2 actual.event := by rw [final, selected]; exact allowed
  obtain ⟨checked⟩ := checked_step evidence positive actual atCurrent allowedHere
  have newFinal : checked.move.after.report.final = afterState.1 := checked.move.final.trans after
  refine ⟨⟨checked.move.after, newFinal, passed.append checked.move, ?_⟩, ?_, ?_, ?_⟩
  · simpa only [observed] using checked.evidence
  · simpa only [newFinal, observed, final] using checked.nonincrease
  · intro demand equal pending
    have equalHere : (observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) beforeState.2 actual).rank
        (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) checked.move.after.report.final =
      beforeState.2.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final := by
      simpa only [newFinal, observed, final] using equal
    have pendingHere : nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum)
        current.report.final beforeState.2 = some demand := by simpa only [final] using pending
    simpa only [newFinal, observed] using checked.persistent demand equalHere pendingHere
  · intro demand pending served
    have pendingHere : nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum)
        current.report.final beforeState.2 = some demand := by simpa only [final] using pending
    have servedHere : serves demand actual.event = true := by simpa only [selected] using served
    simpa only [newFinal, observed, final] using checked.advances demand pendingHere servedHere

def adapter (initial : Initial report complete request) (native : NativeEnv initial) (quantum : Nat)
    (positive : 0 < quantum) : Theory.BoundedProgress.Adapter (State input × Monitor) Event Demand where
  system := guardedSystem input (CampusTCPRecoveryRoundPhaseBase.config initial native quantum)
  invariant := Invariant initial native quantum
  pending state demand := nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) state.1 state.2 = some demand
  enabled state demand := ∃ actual : Step input, actual.before = state.1 ∧ actual.event = demand.event ∧
    actual.result.supported = true
  serves demand event := serves demand event = true
  rank state := state.2.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) state.1
  complete := Completed initial native quantum
  preserve := by
    intro before event after invariant edge
    exact (transition invariant positive edge).invariant
  nonincrease := by
    intro before event after invariant edge
    exact (transition invariant positive edge).nonincrease
  demand := by
    intro state invariant begun
    obtain ⟨current, final, _, ⟨evidence⟩⟩ := invariant
    have positiveHere : 0 < state.2.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final := by
      simpa only [final] using begun
    simpa only [final] using evidence.pending_positive positiveHere
  pending_enabled := by
    intro state demand invariant pending
    obtain ⟨current, final, _, ⟨evidence⟩⟩ := invariant
    have pendingHere : nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum)
        current.report.final state.2 = some demand := by simpa only [final] using pending
    obtain ⟨selected⟩ := selected_step evidence positive pendingHere
    exact ⟨selected.actual, selected.move.beforeEq.trans final, selected.event, selected.move.supported⟩
  persistent := by
    intro before event after demand invariant edge equal pending
    exact (transition invariant positive edge).persistent demand equal pending
  advance := by
    intro before event after demand invariant edge pending _ served
    exact (transition invariant positive edge).advances demand pending served
  finished := by
    intro state invariant zero
    exact finished invariant zero

end Netlib.Check.CampusTCPRecoveryRoundProgress
