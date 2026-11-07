import Netlib.Check.CampusTCPStartupTransferMonitor
import Netlib.Check.CampusTCPTraceSlices
import Netlib.Theory.BoundedServiceRestriction

/-!
# Data service on one literal whole-report suffix

These interval lemmas consume projections of the observed whole monitor.
They do not assume a second local service condition or a future ready state.
-/

namespace Netlib.Check.CampusTCPStartupTransferRestriction

open CampusTCPModel

namespace M
export CampusTCPStartupTransferMonitor (Config Demand serves data_serves)
end M
namespace T
export CampusTCPStartupTransferConfig (Handoff)
end T
namespace W
export CampusTCPTwoTransferMonitor (Monitor allowed monitorAt pendingAt Serviced actions check)
end W
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

variable {input : Input} {config : M.Config} {initial : State input}
variable {steps : List (Step input)} {offset bound : Nat}
variable {handoff : T.Handoff input.active input.passive} {monitor : W.Monitor}
variable {wholePending : Nat → Option M.Demand} {wholeAllowed : Nat → Event → Bool}

theorem data_service_suffix (within : offset ≤ steps.length)
    (service : Theory.BoundedServiceCheck.Serviced steps.length wholePending (S.eventAt steps) (M.serves config) bound)
    (pendingEq : ∀ slot, slot ≤ (steps.drop offset).length → wholePending (offset + slot) =
      (W.pendingAt (config.transfer.data handoff) (S.stateAt initial steps offset) monitor (steps.drop offset) slot).map
        CampusTCPStartupTransferMonitor.Demand.data) :
    W.Serviced (config.transfer.data handoff) (S.stateAt initial steps offset) monitor (steps.drop offset) bound := by
  change Theory.BoundedServiceCheck.Serviced (steps.drop offset).length _ _ _ bound
  apply Theory.BoundedServiceRestriction.restrict service (offset := offset) (by rw [List.length_drop]; omega)
    CampusTCPStartupTransferMonitor.Demand.data
    CampusTCPStartupTransferMonitor.Demand.data_injective id pendingEq
  · intro slot _
    exact (CampusTCPTraceSlices.eventAt_drop steps offset slot).symm
  · intro demand event
    exact M.data_serves config handoff demand event

theorem data_actions_suffix (within : offset ≤ steps.length)
    (actions : ∀ slot, slot < steps.length → wholeAllowed slot (S.eventAt steps slot) = true)
    (allowedEq : ∀ slot, slot < (steps.drop offset).length → wholeAllowed (offset + slot) =
      W.allowed (config.transfer.data handoff)
        (S.stateAt (S.stateAt initial steps offset) (steps.drop offset) slot)
        (W.monitorAt (config.transfer.data handoff) monitor (steps.drop offset) slot)) :
    W.actions (config.transfer.data handoff) (S.stateAt initial steps offset) monitor (steps.drop offset) = true := by
  apply (CampusTCPTwoTransferMonitor.actions_correct _ _ _ _).mpr
  intro slot inside
  change W.allowed _ _ _ _ = true
  rw [← allowedEq slot inside, CampusTCPTraceSlices.eventAt_drop]
  apply actions
  rw [List.length_drop] at inside
  omega

theorem data_check_suffix (within : offset ≤ steps.length)
    (service : Theory.BoundedServiceCheck.Serviced steps.length wholePending (S.eventAt steps) (M.serves config) bound)
    (pendingEq : ∀ slot, slot ≤ (steps.drop offset).length → wholePending (offset + slot) =
      (W.pendingAt (config.transfer.data handoff) (S.stateAt initial steps offset) monitor (steps.drop offset) slot).map
        CampusTCPStartupTransferMonitor.Demand.data) :
    W.check (config.transfer.data handoff) (S.stateAt initial steps offset) monitor (steps.drop offset) bound = true :=
  (CampusTCPTwoTransferMonitor.check_correct _ _ _ _ _).mpr (data_service_suffix within service pendingEq)

theorem data_check_suffix_of_check (within : offset ≤ steps.length)
    (checked : Theory.BoundedServiceCheck.check steps.length wholePending (S.eventAt steps) (M.serves config) bound = true)
    (pendingEq : ∀ slot, slot ≤ (steps.drop offset).length → wholePending (offset + slot) =
      (W.pendingAt (config.transfer.data handoff) (S.stateAt initial steps offset) monitor (steps.drop offset) slot).map
        CampusTCPStartupTransferMonitor.Demand.data) :
    W.check (config.transfer.data handoff) (S.stateAt initial steps offset) monitor (steps.drop offset) bound = true :=
  data_check_suffix within ((Theory.BoundedServiceCheck.check_correct _ _ _ _ _).mp checked) pendingEq

end Netlib.Check.CampusTCPStartupTransferRestriction
