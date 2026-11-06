import Netlib.Check.CampusTCPTwoProgressEvidenceStep
import Netlib.Check.CampusTCPTwoProgressInvariant

/-!
# Invariant on every allowed actual prefix

Each abstract edge extends the same campus report.
No selected event needs a supplied future success witness.
-/

namespace Netlib.Check.CampusTCPTwoProgressProgress

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressSetup (config)
open CampusTCPTwoProgressInvariant

namespace M
export CampusTCPTwoProgressMonitor (Monitor guardedSystem stateAt monitorAt)
end M
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {beforeState afterState : State input × M.Monitor} {event : Event}

theorem transition (invariant : Invariant initial native quantum allowance beforeState) (budget : allowance ≤ 2)
    (edge : (M.guardedSystem input (config initial native quantum allowance)).step beforeState event afterState) :
    Invariant initial native quantum allowance afterState := by
  obtain ⟨current, final, ⟨evidence⟩⟩ := invariant
  obtain ⟨allowed, actual, before, selected, after, observed⟩ := edge
  have atCurrent : actual.before = current.report.final := before.trans final.symm
  have allowedHere : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance)
      current.report.final beforeState.2 actual.event := by rw [final, selected]; exact allowed
  obtain ⟨move, next⟩ := evidence.step budget actual atCurrent allowedHere
  refine ⟨move.after, move.final.trans after, ?_⟩
  simpa only [observed] using next

theorem prefix_invariant (budget : allowance ≤ 2)
    (execution : Theory.BoundedProgress.Prefix (M.guardedSystem input (config initial native quantum allowance)))
    (start : Invariant initial native quantum allowance (execution.state 0)) :
    ∀ slot, slot ≤ execution.length → Invariant initial native quantum allowance (execution.state slot) := by
  intro slot
  induction slot with
  | zero => exact fun _ => start
  | succ slot ih =>
    intro within
    exact transition (ih (by omega)) budget (execution.checked slot (by omega))

def Actions (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (quantum allowance : Nat)
    (steps : List (Step input)) : Prop :=
  ∀ slot, slot < steps.length → CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance)
    (S.stateAt cut.report.final steps slot) (M.monitorAt (config initial native quantum allowance) .initial steps slot)
    (S.eventAt steps slot)

variable {suffix remaining : List Event} {steps : List (Step input)} {final : State input}

theorem trace_invariant (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : Actions initial native quantum allowance steps) (budget : allowance ≤ 2) (slot : Nat) (within : slot ≤ steps.length) :
    Invariant initial native quantum allowance (M.stateAt (config initial native quantum allowance) cut.report.final .initial steps slot) := by
  let execution := CampusTCPTwoProgressMonitor.Trace.guardedPrefix trace (config initial native quantum allowance) .initial actions
  apply prefix_invariant budget execution ?_ slot within
  simpa only [execution, CampusTCPTwoProgressMonitor.Trace.guardedPrefix, CampusTCPTwoProgressMonitor.Trace.prefix,
    CampusTCPTwoProgressMonitor.stateAt, CampusTCPSchedule.stateAt_zero, CampusTCPTwoProgressMonitor.monitorAt_zero] using
    initial_invariant initial native quantum allowance

theorem trace_healthy (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : Actions initial native quantum allowance steps) (budget : allowance ≤ 2) (slot : Nat) (within : slot ≤ steps.length) :
    (M.monitorAt (config initial native quantum allowance) .initial steps slot).mode ≠ .invalid :=
  (trace_invariant trace actions budget slot within).healthy

theorem trace_passed (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : Actions initial native quantum allowance steps) (budget : allowance ≤ 2) :
    ∀ actual ∈ steps, actual.result.supported = true ∧ actual.result.passed = true := by
  have healthy := trace_healthy trace actions budget steps.length (Nat.le_refl _)
  rw [CampusTCPTwoProgressMonitor.monitorAt_length] at healthy
  exact (CampusTCPTwoProgressEvidenceTrace.fold_passed _ _ _ healthy).2

theorem trace_compliant (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : Actions initial native quantum allowance steps) (budget : allowance ≤ 2) (prior : cut.report.compliant = true)
    (slot : Nat) (within : slot ≤ steps.length) :
    ∃ current : Cut input complete, current.report.final = S.stateAt cut.report.final steps slot ∧ current.report.compliant = true :=
  (trace_invariant trace actions budget slot within).compliant prior

end Netlib.Check.CampusTCPTwoProgressProgress
