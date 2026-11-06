import Netlib.Check.CampusTCPTwoProgressEvidenceSelected
import Netlib.Check.CampusTCPTwoProgressEvidenceRankStep
import Netlib.Check.CampusTCPTwoProgressProgress

/-!
# Bounded handoff from the two original paths

The bound counts evaluated slots in the supplied actual trace.
It stops at recovery or read and does not bound the later recovery stage.
-/

namespace Netlib.Check.CampusTCPTwoProgressOriginalBounded

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressSetup (config)
open CampusTCPTwoProgressEvidence (Evidence)
open CampusTCPTwoProgressInvariant (Invariant initial_invariant)

namespace M
export CampusTCPTwoProgressMonitor (Monitor Demand nextDemand observe serves stateAt monitorAt)
end M
namespace R
export CampusTCPTwoProgressOriginalRank (originalRank rank_zero_of_nonoriginal observe_nonoriginal initial_rank)
end R
namespace P
export CampusTCPTwoProgressProgress (Actions)
end P

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {beforeState afterState : State input × M.Monitor} {event : Event}

def Pending (cfg : CampusTCPTwoProgressMonitor.Config) (state : State input × M.Monitor) (demand : M.Demand) : Prop :=
  state.2.mode = .originals ∧ M.nextDemand cfg state.1 state.2 = some demand

def Enabled (state : State input × M.Monitor) (demand : M.Demand) : Prop :=
  ∃ actual : Step input, actual.before = state.1 ∧ actual.result.supported = true ∧
    actual.result.passed = true ∧ M.serves demand actual.event = true

def HandedOff (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (quantum allowance : Nat)
    (state : State input × M.Monitor) : Prop :=
  Invariant initial native quantum allowance state ∧ state.2.mode ≠ .originals

private theorem positive_mode {monitor : M.Monitor} (positive : 0 < R.originalRank monitor) : monitor.mode = .originals := by
  by_cases mode : monitor.mode = .originals
  · exact mode
  · rw [R.rank_zero_of_nonoriginal mode] at positive
    exact False.elim (Nat.not_lt_zero _ positive)

private theorem nonincrease (invariant : Invariant initial native quantum allowance beforeState)
    (edge : (CampusTCPTwoProgressMonitor.guardedSystem input (config initial native quantum allowance)).step beforeState event afterState) :
    R.originalRank afterState.2 ≤ R.originalRank beforeState.2 := by
  obtain ⟨current, final, ⟨evidence⟩⟩ := invariant
  obtain ⟨_, actual, _, _, _, observed⟩ := edge
  rw [← observed]
  by_cases mode : beforeState.2.mode = .originals
  · exact evidence.original_step_nonincrease mode actual
  · rw [R.rank_zero_of_nonoriginal mode, R.rank_zero_of_nonoriginal (R.observe_nonoriginal _ _ actual mode)]
    exact Nat.le_refl _

private theorem enabled (invariant : Invariant initial native quantum allowance beforeState)
    (pending : Pending (config initial native quantum allowance) beforeState demand) : Enabled beforeState demand := by
  obtain ⟨current, final, ⟨evidence⟩⟩ := invariant
  obtain ⟨event, ⟨hop⟩, serves⟩ := evidence.original_selected pending.1 (by rw [final]; exact pending.2)
  exact ⟨hop.actual, hop.move.beforeEq.trans final, hop.move.supported, hop.move.passed, by rw [hop.selected]; exact serves⟩

private theorem persistent (invariant : Invariant initial native quantum allowance beforeState) (budget : allowance ≤ 2)
    (edge : (CampusTCPTwoProgressMonitor.guardedSystem input (config initial native quantum allowance)).step beforeState event afterState)
    (equal : R.originalRank afterState.2 = R.originalRank beforeState.2)
    (pending : Pending (config initial native quantum allowance) beforeState demand) :
    Pending (config initial native quantum allowance) afterState demand := by
  obtain ⟨current, final, ⟨evidence⟩⟩ := invariant
  obtain ⟨allowed, actual, before, selected, after, observed⟩ := edge
  have allowedHere : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance)
      current.report.final beforeState.2 actual.event := by rw [final, selected]; exact allowed
  obtain ⟨move, _⟩ := evidence.step budget actual (before.trans final.symm) allowedHere
  have same : R.originalRank (M.observe (config initial native quantum allowance) beforeState.2 actual) =
      R.originalRank beforeState.2 := by rw [observed]; exact equal
  have next := evidence.original_persistent pending.1 move allowedHere same demand (by rw [final]; exact pending.2)
  constructor
  · apply positive_mode
    rw [equal]
    exact evidence.original_positive pending.1
  · rw [move.final, after, observed] at next
    exact next

private theorem advances (invariant : Invariant initial native quantum allowance beforeState) (budget : allowance ≤ 2)
    (edge : (CampusTCPTwoProgressMonitor.guardedSystem input (config initial native quantum allowance)).step beforeState event afterState)
    (pending : Pending (config initial native quantum allowance) beforeState demand) (served : M.serves demand event = true) :
    R.originalRank afterState.2 < R.originalRank beforeState.2 := by
  obtain ⟨current, final, ⟨evidence⟩⟩ := invariant
  obtain ⟨allowed, actual, before, selected, _, observed⟩ := edge
  have allowedHere : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance)
      current.report.final beforeState.2 actual.event := by rw [final, selected]; exact allowed
  obtain ⟨move, _⟩ := evidence.step budget actual (before.trans final.symm) allowedHere
  rw [← observed]
  exact evidence.original_served_strict pending.1 move allowedHere demand
    (by rw [final]; exact pending.2) (by rw [selected]; exact served)

def adapter (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (quantum allowance : Nat) (budget : allowance ≤ 2) :
    Theory.BoundedProgress.Adapter (State input × M.Monitor) Event M.Demand where
  system := CampusTCPTwoProgressMonitor.guardedSystem input (config initial native quantum allowance)
  invariant := Invariant initial native quantum allowance
  pending := Pending (config initial native quantum allowance)
  enabled := Enabled
  serves demand event := M.serves demand event = true
  rank state := R.originalRank state.2
  complete := HandedOff initial native quantum allowance
  preserve := by intro before event after invariant edge; exact CampusTCPTwoProgressProgress.transition invariant budget edge
  nonincrease := nonincrease
  demand := by
    intro state invariant positive
    obtain ⟨current, final, ⟨evidence⟩⟩ := invariant
    have mode := positive_mode positive
    obtain ⟨demand, pending⟩ := evidence.original_pending mode
    exact ⟨demand, mode, by rw [← final]; exact pending⟩
  pending_enabled := enabled
  persistent invariant edge equal pending := persistent invariant budget edge equal pending
  advance invariant edge pending _ served := advances invariant budget edge pending served
  finished := by
    intro state invariant zero
    refine ⟨invariant, ?_⟩
    intro mode
    obtain ⟨current, _, ⟨evidence⟩⟩ := invariant
    have positive := evidence.original_positive mode
    rw [zero] at positive
    exact Nat.not_lt_zero _ positive

def boundSlots (bound : Nat) : Nat := 16 * bound

variable {suffix remaining : List Event} {steps : List (Step input)} {final : State input} {bound : Nat}

def execution (budget : allowance ≤ 2) (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : P.Actions initial native quantum allowance steps) :
    Theory.BoundedProgress.Prefix (adapter initial native quantum allowance budget).system :=
  CampusTCPTwoProgressMonitor.Trace.guardedPrefix trace (config initial native quantum allowance) .initial actions

theorem serviced (budget : allowance ≤ 2) (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : P.Actions initial native quantum allowance steps)
    (service : CampusTCPTwoProgressMonitor.Serviced (config initial native quantum allowance) cut.report.final .initial steps bound) :
    Theory.BoundedProgress.Prefix.ServiceBound (adapter := adapter initial native quantum allowance budget)
      (execution budget trace actions) bound := by
  intro start _ within demand pending persistent
  exact service start within demand pending.2 (fun offset within => (persistent offset within).2)

private theorem execution_initial (budget : allowance ≤ 2) (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : P.Actions initial native quantum allowance steps) :
    (adapter initial native quantum allowance budget).invariant ((execution budget trace actions).state 0) := by
  change Invariant initial native quantum allowance
    (CampusTCPSchedule.stateAt cut.report.final steps 0, M.monitorAt (config initial native quantum allowance) .initial steps 0)
  simpa only [CampusTCPSchedule.stateAt_zero, CampusTCPTwoProgressMonitor.monitorAt_zero] using
    initial_invariant initial native quantum allowance

theorem execution_rank (budget : allowance ≤ 2) (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : P.Actions initial native quantum allowance steps) :
    (adapter initial native quantum allowance budget).rank ((execution budget trace actions).state 0) = 16 := by
  change R.originalRank (M.monitorAt (config initial native quantum allowance) .initial steps 0) = 16
  rw [CampusTCPTwoProgressMonitor.monitorAt_zero, R.initial_rank]

theorem handoff_by (budget : allowance ≤ 2) (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : P.Actions initial native quantum allowance steps)
    (service : CampusTCPTwoProgressMonitor.Serviced (config initial native quantum allowance) cut.report.final .initial steps bound)
    (enough : boundSlots bound ≤ steps.length) :
    HandedOff initial native quantum allowance
      (M.stateAt (config initial native quantum allowance) cut.report.final .initial steps (boundSlots bound)) := by
  have rank := execution_rank budget trace actions
  have within : 0 + (adapter initial native quantum allowance budget).rank ((execution budget trace actions).state 0) * bound ≤
      (execution budget trace actions).length := by rw [rank, Nat.zero_add]; exact enough
  have done := Theory.BoundedProgress.Prefix.completes_by (adapter := adapter initial native quantum allowance budget)
    (execution budget trace actions) (execution_initial budget trace actions) (serviced budget trace actions service)
    0 (Nat.zero_le _) within
  rw [rank, Nat.zero_add] at done
  exact done

theorem handoff_by_checked (budget : allowance ≤ 2) (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : CampusTCPTwoProgressMonitor.actions (config initial native quantum allowance) cut.report.final .initial steps = true)
    (service : CampusTCPTwoProgressMonitor.check (config initial native quantum allowance) cut.report.final .initial steps bound = true)
    (enough : boundSlots bound ≤ steps.length) :
    HandedOff initial native quantum allowance
      (M.stateAt (config initial native quantum allowance) cut.report.final .initial steps (boundSlots bound)) :=
  handoff_by budget trace ((CampusTCPTwoProgressMonitor.actions_correct _ _ _ _).mp actions)
    ((CampusTCPTwoProgressMonitor.check_correct _ _ _ _ _).mp service) enough

theorem handed_off_actual {state : State input × M.Monitor} (done : HandedOff initial native quantum allowance state) :
    ∃ current : Cut input complete, current.report.final = state.1 ∧ Nonempty (Evidence initial native quantum allowance current state.2) ∧
      state.2.mode ≠ .originals := by
  obtain ⟨⟨current, final, evidence⟩, mode⟩ := done
  exact ⟨current, final, evidence, mode⟩

end Netlib.Check.CampusTCPTwoProgressOriginalBounded
