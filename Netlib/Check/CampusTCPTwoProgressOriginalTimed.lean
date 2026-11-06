import Netlib.Check.CampusTCPTwoProgressOriginalBounded
import Netlib.Check.CampusTCPTwoProgressSuffixAge

/-!
# Original-phase handoff and actual endpoint clocks

Bounded service ends the original phase by slot 16B.
Allowed clock inputs bound each endpoint at that same actual cut.
-/

namespace Netlib.Check.CampusTCPTwoProgressOriginalTimed

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressSetup (config)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {suffix remaining : List Event} {steps : List (Step input)} {final : State input} {bound : Nat}

theorem handoff_by (budget : allowance ≤ 2) (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : CampusTCPTwoProgressProgress.Actions initial native quantum allowance steps)
    (service : CampusTCPTwoProgressMonitor.Serviced (config initial native quantum allowance) cut.report.final .initial steps bound)
    (enough : 16 * bound ≤ steps.length) :
    ∃ current : Cut input complete,
      current.report.final = CampusTCPSchedule.stateAt cut.report.final steps (16 * bound) ∧
      Nonempty (CampusTCPTwoProgressEvidence.Evidence initial native quantum allowance current
        (CampusTCPTwoProgressMonitor.monitorAt (config initial native quantum allowance) .initial steps (16 * bound))) ∧
      (CampusTCPTwoProgressMonitor.monitorAt (config initial native quantum allowance) .initial steps (16 * bound)).mode ≠ .originals ∧
      ∀ actor, (endpoint current.endpoints actor).now ≤ (endpoint cut.endpoints actor).now + (16 * bound) * quantum := by
  have handoff := CampusTCPTwoProgressOriginalBounded.handoff_by budget trace actions service enough
  obtain ⟨current, same, evidence, clocks⟩ := CampusTCPTwoProgressSuffixAge.trace_cut_now trace actions budget (16 * bound) enough
  exact ⟨current, same, evidence, handoff.2, clocks⟩

theorem handoff_by_checked (budget : allowance ≤ 2) (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : CampusTCPTwoProgressMonitor.actions (config initial native quantum allowance) cut.report.final .initial steps = true)
    (service : CampusTCPTwoProgressMonitor.check (config initial native quantum allowance) cut.report.final .initial steps bound = true)
    (enough : 16 * bound ≤ steps.length) :
    ∃ current : Cut input complete,
      current.report.final = CampusTCPSchedule.stateAt cut.report.final steps (16 * bound) ∧
      Nonempty (CampusTCPTwoProgressEvidence.Evidence initial native quantum allowance current
        (CampusTCPTwoProgressMonitor.monitorAt (config initial native quantum allowance) .initial steps (16 * bound))) ∧
      (CampusTCPTwoProgressMonitor.monitorAt (config initial native quantum allowance) .initial steps (16 * bound)).mode ≠ .originals ∧
      ∀ actor, (endpoint current.endpoints actor).now ≤ (endpoint cut.endpoints actor).now + (16 * bound) * quantum :=
  handoff_by budget trace ((CampusTCPTwoProgressMonitor.actions_correct _ _ _ _).mp actions)
    ((CampusTCPTwoProgressMonitor.check_correct _ _ _ _ _).mp service) enough

end Netlib.Check.CampusTCPTwoProgressOriginalTimed
