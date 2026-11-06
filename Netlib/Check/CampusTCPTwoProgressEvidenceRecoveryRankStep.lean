import Netlib.Check.CampusTCPTwoProgressEvidenceRecoveryCap
import Netlib.Check.CampusTCPTwoProgressRecoveryRankWork
import Netlib.Check.CampusTCPTwoProgressRecoveryRankTimer
import Netlib.Check.CampusTCPTwoProgressEvidenceRecoveryClockStep

/-!
# Recovery descent on every allowed actual step

The fixed cap bounds each successor timer.
Every nonclock event reduces the rank.
-/

namespace Netlib.Check.CampusTCPTwoProgressEvidenceRecoveryRankStep

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressSetup (config)
open CampusTCPTwoProgressPhaseBase (Core)
open CampusTCPTwoProgressPhaseState (Active)
open CampusTCPTwoProgressEvidence (Evidence)
open CampusTCPTwoProgressRecoveryCap (PendingCap)
open CampusTCPTwoProgressEvidenceRecoveryRank (boundSlots)

namespace M
export CampusTCPTwoProgressMonitor (Monitor Allowed observe nextDemand serves dropTarget exposedPacket)
end M
namespace K
export CampusTCPTwoProgressRecoveryRank (rank timerSlots)
end K

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance capacity : Nat}
variable {monitor : M.Monitor} {actual : Step input}
variable {sent : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
variable {core : Core initial native quantum allowance current monitor sent received}

private theorem successor_slots_le (value : Evidence initial native quantum allowance current monitor)
    (nonoriginal : monitor.mode ≠ .originals)
    (cap : PendingCap (config initial native quantum allowance) capacity current.report.final monitor)
    (budget : allowance ≤ 2) (move : Move current actual)
    (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event) :
    K.timerSlots (config initial native quantum allowance) actual.result.state ≤
      boundSlots (config initial native quantum allowance) capacity allowance := by
  obtain ⟨nextMove, ⟨next⟩, bounded⟩ := CampusTCPTwoProgressRecoveryCap.cap_step value nonoriginal cap budget actual move.beforeEq allowed
  have mode := CampusTCPTwoProgressOriginalRank.observe_nonoriginal (config initial native quantum allowance) monitor actual nonoriginal
  have slots := CampusTCPTwoProgressEvidenceRecoveryRank.evidence_slots_le next mode bounded
  rw [nextMove.final] at slots
  exact slots

private theorem ack_running (active : Active core) {lane : CampusTCPTwoProgressMonitor.Lane}
    (pending : monitor.ack = some lane) : monitor.waiting = false := by
  cases waiting : monitor.waiting
  · rfl
  · have absent := (active.waiting waiting).1
    rw [pending] at absent
    cases absent

private theorem drop_running (active : Active core) (mode : monitor.mode = .recovery) (id : Nat)
    {target : CampusTCPTwoProgressMonitor.DropTarget}
    (selected : M.dropTarget (config initial native quantum allowance) current.report.final monitor id = some target) :
    monitor.waiting = false := by
  cases waiting : monitor.waiting
  · rfl
  · obtain ⟨ack, retry⟩ := active.waiting waiting
    obtain ⟨lowerDone, upperDone⟩ := active.recovery mode
    simp [M.dropTarget, mode, M.exposedPacket, CampusTCPGapProgressMonitor.nextAction,
      CampusTCPTwoProgressMonitor.Lane.toGap, lowerDone, upperDone, retry, ack] at selected

private theorem active_nonclock_strict (active : Active core) (nonoriginal : monitor.mode ≠ .originals)
    (cap : PendingCap (config initial native quantum allowance) capacity current.report.final monitor)
    (budget : allowance ≤ 2) (positive : 0 < quantum) (capacityPositive : 0 < capacity)
    (move : Move current actual) (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event)
    (nonClock : ∀ actor millis, actual.event ≠ .advanceClock actor millis) :
    K.rank (config initial native quantum allowance) (boundSlots (config initial native quantum allowance) capacity allowance)
      allowance actual.result.state (M.observe (config initial native quantum allowance) monitor actual) <
      K.rank (config initial native quantum allowance) (boundSlots (config initial native quantum allowance) capacity allowance)
        allowance current.report.final monitor := by
  classical
  have mode := active.mode.resolve_left nonoriginal
  have shape := CampusTCPTwoProgressEvidenceRecoveryRank.active_rank_shape active mode
  have time := CampusTCPTwoProgressEvidenceRecoveryRank.boundSlots_positive
    (config initial native quantum allowance) capacity allowance positive capacityPositive
  have slots := successor_slots_le (.active core active) nonoriginal cap budget move allowed
  by_cases drop : ∃ id, actual.event = .dropPacket id
  · obtain ⟨id, event⟩ := drop
    obtain ⟨target, selected⟩ := CampusTCPTwoProgressEvidence.allowed_drop_target active id (by rw [← event]; exact allowed)
    obtain ⟨lowerDone, upperDone⟩ := active.recovery mode
    exact CampusTCPTwoProgressRecoveryRankWork.observed_drop_strict _ _ _ _ _ actual id mode
      (drop_running active mode id selected) shape lowerDone upperDone (by rw [move.beforeEq]; exact selected)
      time slots move.supported move.passed (by rw [move.beforeEq]; exact allowed) event
  have nonDrop : ∀ id, actual.event ≠ .dropPacket id := fun id same => drop ⟨id, same⟩
  cases CampusTCPTwoProgressEvidence.allowed_choice active allowed nonClock nonDrop with
  | lower _ before _ _ _ => exact False.elim (nonoriginal before)
  | upper _ before _ _ _ _ => exact False.elim (nonoriginal before)
  | ack lane action pending _ event =>
    exact CampusTCPTwoProgressRecoveryRankWork.action_strict _ _ _ _ _ actual mode (ack_running active pending)
      shape time slots move.supported move.passed (by rw [move.beforeEq]; exact allowed) action event
  | retry action _ _ running _ event =>
    exact CampusTCPTwoProgressRecoveryRankWork.action_strict _ _ _ _ _ actual mode running
      shape time slots move.supported move.passed (by rw [move.beforeEq]; exact allowed) action event
  | timeout _ _ waiting next event =>
    obtain ⟨hop, decrement⟩ := CampusTCPTwoProgressRecoveryRankTimer.timeout_hop_strict active
      (boundSlots (config initial native quantum allowance) capacity allowance) budget waiting next
    have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event hop.actual actual
      (hop.move.beforeEq.trans move.beforeEq.symm) (hop.selected.trans event.symm)
    rw [hop.move.final] at decrement
    rw [← same]
    omega

theorem nonclock_strict (value : Evidence initial native quantum allowance current monitor)
    (nonoriginal : monitor.mode ≠ .originals)
    (cap : PendingCap (config initial native quantum allowance) capacity current.report.final monitor)
    (budget : allowance ≤ 2) (positive : 0 < quantum) (capacityPositive : 0 < capacity)
    (move : Move current actual) (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event)
    (nonClock : ∀ actor millis, actual.event ≠ .advanceClock actor millis) :
    K.rank (config initial native quantum allowance) (boundSlots (config initial native quantum allowance) capacity allowance)
      allowance actual.result.state (M.observe (config initial native quantum allowance) monitor actual) <
      K.rank (config initial native quantum allowance) (boundSlots (config initial native quantum allowance) capacity allowance)
        allowance current.report.final monitor := by
  cases value with
  | written value _ => exact False.elim (nonoriginal value.mode)
  | upper _ value _ => exact False.elim (nonoriginal value.mode)
  | active core active => exact active_nonclock_strict active nonoriginal cap budget positive capacityPositive move allowed nonClock
  | ready core ready =>
    rcases CampusTCPTwoProgressRecoveryCapSettled.settled_event (.inl ready.mode) allowed with ⟨_, event⟩ | ⟨actor, millis, event⟩
    · obtain ⟨hop, decrease⟩ := CampusTCPTwoProgressRecoveryCapSettled.read_hop_strict ready
        (boundSlots (config initial native quantum allowance) capacity allowance)
      have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event hop.actual actual
        (hop.move.beforeEq.trans move.beforeEq.symm) (hop.selected.trans event.symm)
      rw [hop.move.final] at decrease
      rw [← same]
      exact decrease
    · exact False.elim (nonClock actor millis event)
  | done value =>
    rcases CampusTCPTwoProgressRecoveryCapSettled.settled_event (.inr value.mode) allowed with ⟨reading, _⟩ | ⟨actor, millis, event⟩
    · rw [value.mode] at reading
      cases reading
    · exact False.elim (nonClock actor millis event)

theorem nonincrease (value : Evidence initial native quantum allowance current monitor)
    (nonoriginal : monitor.mode ≠ .originals)
    (cap : PendingCap (config initial native quantum allowance) capacity current.report.final monitor)
    (budget : allowance ≤ 2) (positive : 0 < quantum) (capacityPositive : 0 < capacity)
    (move : Move current actual) (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event) :
    K.rank (config initial native quantum allowance) (boundSlots (config initial native quantum allowance) capacity allowance)
      allowance move.after.report.final (M.observe (config initial native quantum allowance) monitor actual) ≤
      K.rank (config initial native quantum allowance) (boundSlots (config initial native quantum allowance) capacity allowance)
        allowance current.report.final monitor := by
  classical
  by_cases clock : ∃ actor millis, actual.event = .advanceClock actor millis
  · obtain ⟨actor, millis, event⟩ := clock
    obtain ⟨clocked⟩ := CampusTCPTwoProgressClock.Step.clock actual value.anchor _ monitor actor millis
      move.beforeEq event (by rw [← event]; exact allowed)
    have decrease := CampusTCPTwoProgressRecoveryRankClock.clock_nonincrease value nonoriginal
      (boundSlots (config initial native quantum allowance) capacity allowance) clocked (by rw [← event]; exact allowed)
    rw [clocked.move.final] at decrease
    rw [move.final]
    exact decrease
  · rw [move.final]
    exact Nat.le_of_lt (nonclock_strict value nonoriginal cap budget positive capacityPositive move allowed
      (fun actor millis same => clock ⟨actor, millis, same⟩))

theorem served_strict (value : Evidence initial native quantum allowance current monitor)
    (nonoriginal : monitor.mode ≠ .originals)
    (cap : PendingCap (config initial native quantum allowance) capacity current.report.final monitor)
    (budget : allowance ≤ 2) (positive : 0 < quantum) (capacityPositive : 0 < capacity)
    (move : Move current actual) (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event)
    (demand : CampusTCPTwoProgressMonitor.Demand)
    (pending : M.nextDemand (config initial native quantum allowance) current.report.final monitor = some demand)
    (served : M.serves demand actual.event = true) :
    K.rank (config initial native quantum allowance) (boundSlots (config initial native quantum allowance) capacity allowance)
      allowance move.after.report.final (M.observe (config initial native quantum allowance) monitor actual) <
      K.rank (config initial native quantum allowance) (boundSlots (config initial native quantum allowance) capacity allowance)
        allowance current.report.final monitor := by
  classical
  by_cases clock : ∃ actor millis, actual.event = .advanceClock actor millis
  · obtain ⟨actor, millis, event⟩ := clock
    obtain ⟨clocked⟩ := CampusTCPTwoProgressClock.Step.clock actual value.anchor _ monitor actor millis
      move.beforeEq event (by rw [← event]; exact allowed)
    have decrease := CampusTCPTwoProgressEvidenceRecoveryClockStep.clock_served_strict value nonoriginal
      (boundSlots (config initial native quantum allowance) capacity allowance) positive clocked
      (by rw [← event]; exact allowed) demand pending served
    rw [clocked.move.final] at decrease
    rw [move.final]
    exact decrease
  · rw [move.final]
    exact nonclock_strict value nonoriginal cap budget positive capacityPositive move allowed
      (fun actor millis same => clock ⟨actor, millis, same⟩)

theorem persistent (value : Evidence initial native quantum allowance current monitor)
    (nonoriginal : monitor.mode ≠ .originals)
    (cap : PendingCap (config initial native quantum allowance) capacity current.report.final monitor)
    (budget : allowance ≤ 2) (positive : 0 < quantum) (capacityPositive : 0 < capacity)
    (move : Move current actual) (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event)
    (equal : K.rank (config initial native quantum allowance) (boundSlots (config initial native quantum allowance) capacity allowance)
      allowance move.after.report.final (M.observe (config initial native quantum allowance) monitor actual) =
      K.rank (config initial native quantum allowance) (boundSlots (config initial native quantum allowance) capacity allowance)
        allowance current.report.final monitor)
    (demand : CampusTCPTwoProgressMonitor.Demand)
    (pending : M.nextDemand (config initial native quantum allowance) current.report.final monitor = some demand) :
    M.nextDemand (config initial native quantum allowance) move.after.report.final
      (M.observe (config initial native quantum allowance) monitor actual) = some demand := by
  classical
  by_cases clock : ∃ actor millis, actual.event = .advanceClock actor millis
  · obtain ⟨actor, millis, event⟩ := clock
    obtain ⟨clocked⟩ := CampusTCPTwoProgressClock.Step.clock actual value.anchor _ monitor actor millis
      move.beforeEq event (by rw [← event]; exact allowed)
    have atClock : K.rank (config initial native quantum allowance) (boundSlots (config initial native quantum allowance) capacity allowance)
        allowance clocked.move.after.report.final (M.observe (config initial native quantum allowance) monitor actual) =
        K.rank (config initial native quantum allowance) (boundSlots (config initial native quantum allowance) capacity allowance)
          allowance current.report.final monitor := by rw [clocked.move.final, ← move.final]; exact equal
    have same := CampusTCPTwoProgressEvidenceRecoveryClockStep.clock_equal_pending value nonoriginal
      (boundSlots (config initial native quantum allowance) capacity allowance) positive clocked
      (by rw [← event]; exact allowed) atClock
    rw [clocked.move.final, ← move.final] at same
    exact same.trans pending
  · have strict := nonclock_strict value nonoriginal cap budget positive capacityPositive move allowed
      (fun actor millis same => clock ⟨actor, millis, same⟩)
    rw [← move.final, equal] at strict
    exact False.elim (Nat.lt_irrefl _ strict)

end Netlib.Check.CampusTCPTwoProgressEvidenceRecoveryRankStep
