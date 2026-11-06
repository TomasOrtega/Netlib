import NetlibTest.CampusTCPTwoProgressPlans
import Netlib.Check.CampusTCPTwoProgressOriginalBounded
import Netlib.Check.CampusTCPTwoProgressBounded

/-!
# Public proofs on the same generated schedule

The checker certificates refer to the actual recorded suffix.
The universal invariant and handoff theorem use that same trace.
-/

namespace NetlibTest.CampusTCPTwoProgressPlans

open Netlib Packet Protocol

variable {input : M.Input} {events : List M.Event} {report : M.Report input events} {count : Nat}
variable {sender : M.Actor} {gateway : M.Gateway} {lower upper : List UInt8}
variable {witness : I.Witness report count sender gateway lower upper}

theorem Generated.prefix_invariant (generated : Generated witness) (slot : Nat) (within : slot ≤ generated.suffix.recorded.length) :
    Check.CampusTCPTwoProgressInvariant.Invariant witness.initial witness.native 10 2
      (Check.CampusTCPTwoProgressMonitor.stateAt (configuration witness) witness.current.cut.report.final .initial
        generated.suffix.recorded slot) :=
  Check.CampusTCPTwoProgressProgress.trace_invariant generated.suffix.suffix
    ((Check.CampusTCPTwoProgressMonitor.actions_correct _ _ _ _).mp generated.allowed) (by decide) slot within

theorem Generated.prefix_healthy (generated : Generated witness) (slot : Nat) (within : slot ≤ generated.suffix.recorded.length) :
    (Check.CampusTCPTwoProgressMonitor.monitorAt (configuration witness) .initial generated.suffix.recorded slot).mode ≠ .invalid :=
  (generated.prefix_invariant slot within).healthy

theorem Generated.actual_steps_passed (generated : Generated witness) :
    ∀ actual ∈ generated.suffix.recorded, actual.result.supported = true ∧ actual.result.passed = true :=
  Check.CampusTCPTwoProgressProgress.trace_passed generated.suffix.suffix
    ((Check.CampusTCPTwoProgressMonitor.actions_correct _ _ _ _).mp generated.allowed) (by decide)

theorem Generated.original_handoff (generated : Generated witness) (enough : 48 ≤ generated.suffix.recorded.length) :
    Check.CampusTCPTwoProgressOriginalBounded.HandedOff witness.initial witness.native 10 2
      (Check.CampusTCPTwoProgressMonitor.stateAt (configuration witness) witness.current.cut.report.final .initial
        generated.suffix.recorded 48) :=
  Check.CampusTCPTwoProgressOriginalBounded.handoff_by_checked (by decide) generated.suffix.suffix
    generated.allowed generated.serviced enough

theorem Generated.recovery_cap (generated : Generated witness) (slot : Nat)
    (begun : 48 ≤ slot) (within : slot ≤ generated.suffix.recorded.length) :
    Check.CampusTCPTwoProgressRecoveryCapped.Capped witness.initial witness.native 10 2
      (Check.CampusTCPTwoProgressHandoffRTO.cap witness.initial 480)
      (Check.CampusTCPTwoProgressMonitor.stateAt (configuration witness) witness.current.cut.report.final .initial
        generated.suffix.recorded slot) :=
  Check.CampusTCPTwoProgressRecoveryCapped.trace_capped_checked (by decide) generated.suffix.suffix
    generated.allowed generated.serviced slot begun within

theorem Generated.bounded_read (generated : Generated witness)
    (enough : Check.CampusTCPTwoProgressBounded.boundSlots witness.initial 10 2 3 ≤ generated.suffix.recorded.length) :
    Nonempty (Check.CampusTCPTwoProgressBounded.Result witness.initial witness.native 10 2 3 generated.suffix.recorded) :=
  Check.CampusTCPTwoProgressBounded.complete_by_checked (by decide) (by decide) generated.suffix.suffix
    generated.allowed generated.serviced enough

end NetlibTest.CampusTCPTwoProgressPlans
