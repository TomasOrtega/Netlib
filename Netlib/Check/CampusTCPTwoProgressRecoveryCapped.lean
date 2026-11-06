import Netlib.Check.CampusTCPTwoProgressEvidenceRecoveryCap

/-!
# A fixed cap on every actual recovery prefix

The original handoff supplies the cap once.
Each later stored step retains that cap on the same trace.
-/

namespace Netlib.Check.CampusTCPTwoProgressRecoveryCapped

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressInvariant
open CampusTCPTwoProgressRecoveryCap
open CampusTCPTwoProgressSetup (config)

namespace M
export CampusTCPTwoProgressMonitor (Monitor guardedSystem stateAt monitorAt)
end M
namespace S
export CampusTCPSchedule (stateAt)
end S

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}

def Capped (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (quantum allowance capacity : Nat)
    (state : State input × M.Monitor) : Prop :=
  Invariant initial native quantum allowance state ∧ state.2.mode ≠ .originals ∧
    PendingCap (config initial native quantum allowance) capacity state.1 state.2

variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance capacity : Nat}
variable {beforeState afterState : State input × M.Monitor} {event : Event}

theorem Capped.retry_bound (value : Capped initial native quantum allowance capacity beforeState) :
    beforeState.2.retries ≤ allowance := by
  obtain ⟨⟨current, _, ⟨evidence⟩⟩, _, _⟩ := value
  exact CampusTCPTwoProgressHandoffRTO.evidence_retry_bound evidence

theorem transition (value : Capped initial native quantum allowance capacity beforeState) (budget : allowance ≤ 2)
    (edge : (M.guardedSystem input (config initial native quantum allowance)).step beforeState event afterState) :
    Capped initial native quantum allowance capacity afterState := by
  obtain ⟨⟨current, final, ⟨evidence⟩⟩, nonoriginal, prior⟩ := value
  obtain ⟨allowed, actual, before, selected, after, observed⟩ := edge
  have atCurrent : actual.before = current.report.final := before.trans final.symm
  have allowedHere : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance)
      current.report.final beforeState.2 actual.event := by rw [final, selected]; exact allowed
  have capHere : PendingCap (config initial native quantum allowance) capacity current.report.final beforeState.2 := by
    rw [final]
    exact prior
  obtain ⟨move, next, bounded⟩ := cap_step evidence nonoriginal capHere budget actual atCurrent allowedHere
  refine ⟨⟨move.after, move.final.trans after, ?_⟩, ?_, ?_⟩
  · simpa only [observed] using next
  · rw [← observed]
    exact CampusTCPTwoProgressOriginalRank.observe_nonoriginal _ _ actual nonoriginal
  · rw [move.final, after, observed] at bounded
    exact bounded

theorem prefix_offsets (budget : allowance ≤ 2)
    (execution : Theory.BoundedProgress.Prefix (M.guardedSystem input (config initial native quantum allowance)))
    (first : Nat) (start : Capped initial native quantum allowance capacity (execution.state first)) :
    ∀ offset, first + offset ≤ execution.length →
      Capped initial native quantum allowance capacity (execution.state (first + offset)) := by
  intro offset
  induction offset with
  | zero => intro _; simpa only [Nat.add_zero] using start
  | succ offset ih =>
    intro within
    exact transition (ih (by omega)) budget (execution.checked (first + offset) (by omega))

theorem prefix_from (budget : allowance ≤ 2)
    (execution : Theory.BoundedProgress.Prefix (M.guardedSystem input (config initial native quantum allowance)))
    (first : Nat) (start : Capped initial native quantum allowance capacity (execution.state first))
    (slot : Nat) (begun : first ≤ slot) (within : slot ≤ execution.length) :
    Capped initial native quantum allowance capacity (execution.state slot) := by
  have atSlot := prefix_offsets budget execution first start (slot - first) (by omega)
  have same : first + (slot - first) = slot := by omega
  simpa only [same] using atSlot

variable {suffix remaining : List Event} {steps : List (Step input)} {final : State input} {bound : Nat}

theorem trace_capped (budget : allowance ≤ 2) (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : CampusTCPTwoProgressProgress.Actions initial native quantum allowance steps)
    (service : CampusTCPTwoProgressMonitor.Serviced (config initial native quantum allowance) cut.report.final .initial steps bound)
    (slot : Nat) (begun : 16 * bound ≤ slot) (within : slot ≤ steps.length) :
    Capped initial native quantum allowance (CampusTCPTwoProgressHandoffRTO.cap initial ((16 * bound) * quantum))
      (M.stateAt (config initial native quantum allowance) cut.report.final .initial steps slot) := by
  obtain ⟨current, evidence, same, nonoriginal, pending, _⟩ :=
    CampusTCPTwoProgressHandoffRTO.handoff_by budget trace actions service (by omega)
  let execution := CampusTCPTwoProgressMonitor.Trace.guardedPrefix trace (config initial native quantum allowance) .initial actions
  have start : Capped initial native quantum allowance (CampusTCPTwoProgressHandoffRTO.cap initial ((16 * bound) * quantum))
      (execution.state (16 * bound)) := by
    refine ⟨⟨current, same, ⟨evidence⟩⟩, nonoriginal, ?_⟩
    have bounded := from_handoff (native := native) (quantum := quantum) (allowance := allowance) pending
    rw [same] at bounded
    exact bounded
  exact prefix_from budget execution (16 * bound) start slot begun within

theorem trace_capped_checked (budget : allowance ≤ 2) (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : CampusTCPTwoProgressMonitor.actions (config initial native quantum allowance) cut.report.final .initial steps = true)
    (service : CampusTCPTwoProgressMonitor.check (config initial native quantum allowance) cut.report.final .initial steps bound = true)
    (slot : Nat) (begun : 16 * bound ≤ slot) (within : slot ≤ steps.length) :
    Capped initial native quantum allowance (CampusTCPTwoProgressHandoffRTO.cap initial ((16 * bound) * quantum))
      (M.stateAt (config initial native quantum allowance) cut.report.final .initial steps slot) :=
  trace_capped budget trace ((CampusTCPTwoProgressMonitor.actions_correct _ _ _ _).mp actions)
    ((CampusTCPTwoProgressMonitor.check_correct _ _ _ _ _).mp service) slot begun within

theorem trace_at (budget : allowance ≤ 2) (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : CampusTCPTwoProgressProgress.Actions initial native quantum allowance steps)
    (service : CampusTCPTwoProgressMonitor.Serviced (config initial native quantum allowance) cut.report.final .initial steps bound)
    (slot : Nat) (begun : 16 * bound ≤ slot) (within : slot ≤ steps.length) :
    ∃ current : Cut input complete,
      current.report.final = S.stateAt cut.report.final steps slot ∧
      Nonempty (CampusTCPTwoProgressEvidence.Evidence initial native quantum allowance current
        (M.monitorAt (config initial native quantum allowance) .initial steps slot)) ∧
      (M.monitorAt (config initial native quantum allowance) .initial steps slot).mode ≠ .originals ∧
      (M.monitorAt (config initial native quantum allowance) .initial steps slot).retries ≤ allowance ∧
      PendingCap (config initial native quantum allowance) (CampusTCPTwoProgressHandoffRTO.cap initial ((16 * bound) * quantum))
        current.report.final (M.monitorAt (config initial native quantum allowance) .initial steps slot) := by
  have value := trace_capped budget trace actions service slot begun within
  have retries := value.retry_bound
  obtain ⟨⟨current, same, evidence⟩, nonoriginal, bounded⟩ := value
  refine ⟨current, same, evidence, nonoriginal, retries, ?_⟩
  rw [same]
  exact bounded

end Netlib.Check.CampusTCPTwoProgressRecoveryCapped
