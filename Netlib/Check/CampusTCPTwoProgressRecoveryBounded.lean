import Netlib.Check.CampusTCPTwoProgressEvidenceRecoveryRankStep
import Netlib.Check.CampusTCPTwoProgressEvidenceRecoverySelected
import Netlib.Check.CampusTCPTwoProgressRecoveryCapped

/-!
# Bounded completion on the actual two-record suffix

The recovery view uses the same stored states and events after the original handoff.
-/

namespace Netlib.Check.CampusTCPTwoProgressRecoveryBounded

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressPhaseBase CampusTCPTwoProgressPhaseState
open CampusTCPTwoProgressInvariant CampusTCPTwoProgressRecoveryCap
open CampusTCPTwoProgressRecoveryCapped
open CampusTCPTwoProgressEvidence (Evidence Hop)
open CampusTCPTwoProgressSetup (config)

namespace M
export CampusTCPTwoProgressMonitor (Monitor Config Demand guardedSystem nextDemand laneDemand serves stateAt monitorAt)
end M
namespace K
export CampusTCPTwoProgressRecoveryRank (rank)
end K
namespace E
export CampusTCPTwoProgressEvidenceRecoveryRank (boundSlots evidence_rank_le zero_rank_done handoff_cap_positive)
end E
namespace L
export CampusTCPTwoProgressEvidenceRecoveryRankStep (nonincrease served_strict persistent)
end L

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance capacity : Nat}
variable {monitor : M.Monitor} {sent : CampusTCPTwoProgressSender.Stage initial}
variable {received : CampusTCPTwoProgressReceiver.Stage}
variable {core : Core initial native quantum allowance current monitor sent received}
variable {beforeState afterState : State input × M.Monitor} {event : Event} {demand : M.Demand}

def Pending (cfg : M.Config) (state : State input × M.Monitor) (demand : M.Demand) : Prop :=
  M.nextDemand cfg state.1 state.2 = some demand

def Enabled (state : State input × M.Monitor) (demand : M.Demand) : Prop :=
  ∃ actual : Step input, actual.before = state.1 ∧ actual.result.supported = true ∧
    actual.result.passed = true ∧ M.serves demand actual.event = true

def coarse (quantum allowance capacity : Nat) : Nat :=
  (allowance + 1) * CampusTCPTwoProgressTimer.waitSlots quantum (2 ^ allowance * capacity) + 8 * allowance + 7

private theorem active_pending (active : Active core) (mode : monitor.mode = .recovery) :
    ∃ demand, M.nextDemand (config initial native quantum allowance) current.report.final monitor = some demand := by
  cases ack : monitor.ack with
  | some lane =>
    have work : AckWork core lane := by simpa only [AckState, ack] using active.ack
    have command : ∃ action, CampusTCPGapProgressMonitor.nextAction
        (config initial native quantum allowance).toConfig current.report.final lane.toGap = some action := by
      cases work with
      | pending phase _ =>
        exact ⟨.emitAck sender.other true, by simp only [CampusTCPGapProgressMonitor.nextAction,
          CampusTCPTwoProgressMonitor.Lane.toGap, phase]; rfl⟩
      | ingress path => exact ⟨_, path.action _⟩
      | ticket path => exact ⟨_, path.action _⟩
      | link path => exact ⟨_, path.action _⟩
    obtain ⟨action, next⟩ := command
    have served := CampusTCPTwoProgressPhaseObserve.laneDemand_serves (config initial native quantum allowance)
      current.report.final monitor lane action next
    obtain ⟨raw, selected, _⟩ := (CampusTCPTwoProgressMonitorFacts.servesOption_iff _ _).mp served
    exact ⟨.single raw, by simp only [M.nextDemand, mode, ack, selected, Option.map_some]⟩
  | none =>
    cases waiting : monitor.waiting with
    | false =>
      cases active.retry with
      | done phase => exact False.elim (active.runnable mode waiting ack phase)
      | active part head rest selection work =>
        have served := CampusTCPTwoProgressPhaseObserve.laneDemand_serves (config initial native quantum allowance)
          current.report.final monitor monitor.retry (work.command _) (work.command_next _)
        obtain ⟨raw, selected, _⟩ := (CampusTCPTwoProgressMonitorFacts.servesOption_iff _ _).mp served
        exact ⟨.single raw, by simp only [M.nextDemand, mode, ack, waiting, Bool.false_eq_true, ite_false, selected, Option.map_some]⟩
    | true =>
      obtain ⟨deadline, timer⟩ := Option.isSome_iff_exists.mp (core.live.senderFlight.armed active.nonempty)
      cases entries : core.live.senderFlight.recovery.outstanding with
      | nil => exact False.elim (active.nonempty (core.live.senderFlight.ledger.symm.trans entries))
      | cons head rest =>
        have target := CampusTCPTwoProgressTimer.target_of_fields entries timer
        have selected := CampusTCPTwoProgressTimer.timerDemand_of_target
          (CampusTCPTwoProgressPhaseNormalize.sender_runtime core) target
        exact ⟨_, by simp only [M.nextDemand, mode, ack, waiting, ite_true, selected, Option.map_some]; rfl⟩

private theorem recovery_pending (value : Evidence initial native quantum allowance current monitor)
    (nonoriginal : monitor.mode ≠ .originals) (nondone : monitor.mode ≠ .done) :
    ∃ demand, M.nextDemand (config initial native quantum allowance) current.report.final monitor = some demand := by
  cases value with
  | written before _ => exact False.elim (nonoriginal before.mode)
  | upper _ before _ => exact False.elim (nonoriginal before.mode)
  | active core active => exact active_pending active (active.mode.resolve_left nonoriginal)
  | ready core ready => exact ⟨_, by rw [M.nextDemand, ready.mode]⟩
  | done done => exact False.elim (nondone done.mode)

private theorem enabled (value : Capped initial native quantum allowance capacity beforeState) (budget : allowance ≤ 2)
    (pending : Pending (config initial native quantum allowance) beforeState demand) : Enabled beforeState demand := by
  obtain ⟨⟨current, same, ⟨evidence⟩⟩, nonoriginal, _⟩ := value
  obtain ⟨event, ⟨hop⟩, serves⟩ := evidence.recovery_selected nonoriginal budget (by rw [same]; exact pending)
  exact ⟨hop.actual, hop.move.beforeEq.trans same, hop.move.supported, hop.move.passed, by rw [hop.selected]; exact serves⟩

private theorem nonincrease (value : Capped initial native quantum allowance capacity beforeState)
    (budget : allowance ≤ 2) (positive : 0 < quantum) (capacityPositive : 0 < capacity)
    (edge : (M.guardedSystem input (config initial native quantum allowance)).step beforeState event afterState) :
    K.rank (config initial native quantum allowance) (E.boundSlots (config initial native quantum allowance) capacity allowance)
      allowance afterState.1 afterState.2 ≤
      K.rank (config initial native quantum allowance) (E.boundSlots (config initial native quantum allowance) capacity allowance)
        allowance beforeState.1 beforeState.2 := by
  obtain ⟨⟨current, same, ⟨evidence⟩⟩, nonoriginal, cap⟩ := value
  obtain ⟨allowed, actual, before, selected, after, observed⟩ := edge
  have allowedHere : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance)
      current.report.final beforeState.2 actual.event := by rw [same, selected]; exact allowed
  obtain ⟨move, _⟩ := evidence.step budget actual (before.trans same.symm) allowedHere
  have result := L.nonincrease evidence nonoriginal (by rw [same]; exact cap) budget positive capacityPositive move allowedHere
  simpa only [move.final, after, observed, same] using result

private theorem persistent (value : Capped initial native quantum allowance capacity beforeState)
    (budget : allowance ≤ 2) (positive : 0 < quantum) (capacityPositive : 0 < capacity)
    (edge : (M.guardedSystem input (config initial native quantum allowance)).step beforeState event afterState)
    (equal : K.rank (config initial native quantum allowance) (E.boundSlots (config initial native quantum allowance) capacity allowance)
      allowance afterState.1 afterState.2 =
      K.rank (config initial native quantum allowance) (E.boundSlots (config initial native quantum allowance) capacity allowance)
        allowance beforeState.1 beforeState.2)
    (pending : Pending (config initial native quantum allowance) beforeState demand) :
    Pending (config initial native quantum allowance) afterState demand := by
  obtain ⟨⟨current, same, ⟨evidence⟩⟩, nonoriginal, cap⟩ := value
  obtain ⟨allowed, actual, before, selected, after, observed⟩ := edge
  have allowedHere : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance)
      current.report.final beforeState.2 actual.event := by rw [same, selected]; exact allowed
  obtain ⟨move, _⟩ := evidence.step budget actual (before.trans same.symm) allowedHere
  have result := L.persistent evidence nonoriginal (by rw [same]; exact cap) budget positive capacityPositive move allowedHere
    (by simpa only [move.final, after, observed, same] using equal) demand (by rw [same]; exact pending)
  change M.nextDemand (config initial native quantum allowance) afterState.1 afterState.2 = some demand
  simpa only [move.final, after, observed] using result

private theorem advance (value : Capped initial native quantum allowance capacity beforeState)
    (budget : allowance ≤ 2) (positive : 0 < quantum) (capacityPositive : 0 < capacity)
    (edge : (M.guardedSystem input (config initial native quantum allowance)).step beforeState event afterState)
    (pending : Pending (config initial native quantum allowance) beforeState demand) (served : M.serves demand event = true) :
    K.rank (config initial native quantum allowance) (E.boundSlots (config initial native quantum allowance) capacity allowance)
      allowance afterState.1 afterState.2 <
      K.rank (config initial native quantum allowance) (E.boundSlots (config initial native quantum allowance) capacity allowance)
        allowance beforeState.1 beforeState.2 := by
  obtain ⟨⟨current, same, ⟨evidence⟩⟩, nonoriginal, cap⟩ := value
  obtain ⟨allowed, actual, before, selected, after, observed⟩ := edge
  have allowedHere : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance)
      current.report.final beforeState.2 actual.event := by rw [same, selected]; exact allowed
  obtain ⟨move, _⟩ := evidence.step budget actual (before.trans same.symm) allowedHere
  have result := L.served_strict evidence nonoriginal (by rw [same]; exact cap) budget positive capacityPositive move allowedHere
    demand (by rw [same]; exact pending) (by rw [selected]; exact served)
  simpa only [move.final, after, observed, same] using result

def adapter (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (quantum allowance capacity : Nat)
    (budget : allowance ≤ 2) (positive : 0 < quantum) (capacityPositive : 0 < capacity) :
    Theory.BoundedProgress.Adapter (State input × M.Monitor) Event M.Demand where
  system := M.guardedSystem input (config initial native quantum allowance)
  invariant := Capped initial native quantum allowance capacity
  pending := Pending (config initial native quantum allowance)
  enabled := Enabled
  serves demand event := M.serves demand event = true
  rank state := K.rank (config initial native quantum allowance)
    (E.boundSlots (config initial native quantum allowance) capacity allowance) allowance state.1 state.2
  complete := Completed initial native quantum allowance
  preserve := by intro before event after value edge; exact transition value budget edge
  nonincrease value edge := nonincrease value budget positive capacityPositive edge
  demand := by
    intro state value positiveRank
    obtain ⟨⟨current, same, ⟨evidence⟩⟩, nonoriginal, _⟩ := value
    have nondone : state.2.mode ≠ .done := by
      intro done
      simp only [K.rank, done] at positiveRank
      omega
    obtain ⟨demand, pending⟩ := recovery_pending evidence nonoriginal nondone
    exact ⟨demand, by change M.nextDemand _ state.1 state.2 = some demand; rw [← same]; exact pending⟩
  pending_enabled value pending := enabled value budget pending
  persistent value edge equal pending := persistent value budget positive capacityPositive edge equal pending
  advance value edge pending _ served := advance value budget positive capacityPositive edge pending served
  finished := by
    intro state value zero
    obtain ⟨invariant, nonoriginal, _⟩ := value
    obtain ⟨current, same, ⟨evidence⟩⟩ := invariant
    exact (show Invariant initial native quantum allowance state from ⟨current, same, ⟨evidence⟩⟩).finished
      (E.zero_rank_done evidence _ nonoriginal (by rw [same]; exact zero))

private theorem rank_le (value : Capped initial native quantum allowance capacity beforeState) :
    K.rank (config initial native quantum allowance) (E.boundSlots (config initial native quantum allowance) capacity allowance)
      allowance beforeState.1 beforeState.2 ≤ coarse quantum allowance capacity := by
  obtain ⟨⟨current, same, ⟨evidence⟩⟩, nonoriginal, cap⟩ := value
  have bound := E.evidence_rank_le evidence nonoriginal (by rw [same]; exact cap)
  rw [same] at bound
  simpa only [coarse, E.boundSlots, config] using bound

def capacityAt (initial : TwoWriteInitial cut sender gateway lower upper) (quantum bound : Nat) : Nat :=
  CampusTCPTwoProgressHandoffRTO.cap initial ((16 * bound) * quantum)

def boundSlots (initial : TwoWriteInitial cut sender gateway lower upper) (quantum allowance bound : Nat) : Nat :=
  16 * bound + coarse quantum allowance (capacityAt initial quantum bound) * bound

variable {suffix remaining : List Event} {steps : List (Step input)} {final : State input} {bound : Nat}

theorem completes_by (budget : allowance ≤ 2) (positive : 0 < quantum)
    (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : CampusTCPTwoProgressProgress.Actions initial native quantum allowance steps)
    (service : CampusTCPTwoProgressMonitor.Serviced (config initial native quantum allowance) cut.report.final .initial steps bound)
    (enough : boundSlots initial quantum allowance bound ≤ steps.length) :
    Completed initial native quantum allowance
      (M.stateAt (config initial native quantum allowance) cut.report.final .initial steps (boundSlots initial quantum allowance bound)) := by
  let capacity := capacityAt initial quantum bound
  have capacityPositive : 0 < capacity := E.handoff_cap_positive initial _
  let model := adapter initial native quantum allowance capacity budget positive capacityPositive
  let full : Theory.BoundedProgress.Prefix model.system :=
    CampusTCPTwoProgressMonitor.Trace.guardedPrefix trace (config initial native quantum allowance) .initial actions
  let execution := full.suffix (16 * bound)
  have handoffWithin : 16 * bound ≤ steps.length := by
    have total := enough
    unfold boundSlots at total
    omega
  have start : model.invariant (execution.state 0) := by
    change Capped initial native quantum allowance capacity
      (M.stateAt (config initial native quantum allowance) cut.report.final .initial steps (16 * bound + 0))
    simpa only [Nat.add_zero, capacity, capacityAt] using
      trace_capped budget trace actions service (16 * bound) (Nat.le_refl _) handoffWithin
  have serviced : execution.ServiceBound bound := by
    intro first _ within demand pending retained
    have selected : 16 * bound + first + bound ≤ steps.length := by
      change first + bound ≤ steps.length - 16 * bound at within
      omega
    obtain ⟨offset, inside, served⟩ := service (16 * bound + first) selected demand pending (by
      intro offset inside
      have current := retained offset inside
      change M.nextDemand (config initial native quantum allowance)
        (CampusTCPSchedule.stateAt cut.report.final steps (16 * bound + (first + offset)))
        (M.monitorAt (config initial native quantum allowance) .initial steps (16 * bound + (first + offset))) = some demand at current
      simpa only [CampusTCPTwoProgressMonitor.pendingAt, Nat.add_assoc] using current)
    refine ⟨offset, inside, ?_⟩
    change M.serves demand (CampusTCPSchedule.eventAt steps (16 * bound + (first + offset))) = true
    simpa only [Nat.add_assoc] using served
  have initialRank : model.rank (execution.state 0) ≤ coarse quantum allowance capacity := rank_le start
  have room : coarse quantum allowance capacity * bound ≤ execution.length := by
    change coarse quantum allowance capacity * bound ≤ steps.length - 16 * bound
    change 16 * bound + coarse quantum allowance capacity * bound ≤ steps.length at enough
    omega
  have later : 0 + model.rank (execution.state 0) * bound ≤ coarse quantum allowance capacity * bound := by
    simpa only [Nat.zero_add] using Nat.mul_le_mul_right bound initialRank
  have done := execution.completes_after start serviced 0 (Nat.zero_le _) (coarse quantum allowance capacity * bound) later room
  exact done

theorem completes_by_checked (budget : allowance ≤ 2) (positive : 0 < quantum)
    (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : CampusTCPTwoProgressMonitor.actions (config initial native quantum allowance) cut.report.final .initial steps = true)
    (service : CampusTCPTwoProgressMonitor.check (config initial native quantum allowance) cut.report.final .initial steps bound = true)
    (enough : boundSlots initial quantum allowance bound ≤ steps.length) :
    Completed initial native quantum allowance
      (M.stateAt (config initial native quantum allowance) cut.report.final .initial steps (boundSlots initial quantum allowance bound)) :=
  completes_by budget positive trace ((CampusTCPTwoProgressMonitor.actions_correct _ _ _ _).mp actions)
    ((CampusTCPTwoProgressMonitor.check_correct _ _ _ _ _).mp service) enough

end Netlib.Check.CampusTCPTwoProgressRecoveryBounded
