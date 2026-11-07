import Netlib.Check.CampusTCPRevocationCompletion
import Netlib.Check.CampusTCPRevocationPhased
import Netlib.Check.CampusTCPRevocationReadOrigin

/-!
# One recorded TCP session through revocation

The certificate retains the original history and physical loss allowance.
Its completion cut contains four native installs and no pending receiver link.
-/

namespace Netlib.Check.CampusTCPRevocation

open CampusTCPModel CampusTCPRevocationTargets

namespace P
export CampusTCPRevocationPhased (actions service checked_actions)
end P
namespace C
export CampusTCPRevocationCompletion (findCompletion found_bounds closed_at suffix_closed)
end C
namespace S
export CampusTCPSchedule (stateAt)
end S

def cutState (report : Report input events) (cut : Nat) : State input := S.stateAt input.initial report.steps cut

structure Result (report : Report input events) (config : CampusTCPStartupTransferMonitor.Config)
    (transferEnd triggerCut bound : Nat) (targets : Targets input (cutState report triggerCut)) where
  slot : Nat
  found : C.findCompletion targets (report.steps.drop triggerCut) bound = some slot
  positive : 0 < bound
  actions : P.actions config transferEnd triggerCut targets.names report = true
  service : P.service config transferEnd triggerCut targets.names input.initial report.steps bound = true

variable {input : Input} {events : List CampusTCPModel.Event} {report : Report input events}
variable {config : CampusTCPStartupTransferMonitor.Config} {transferEnd triggerCut bound : Nat}
variable {targets : Targets input (cutState report triggerCut)}

theorem Result.checked (value : Result report config transferEnd triggerCut bound targets) :
    CampusTCPRevocationPhased.CheckedActions config transferEnd triggerCut targets.names report :=
  P.checked_actions config transferEnd triggerCut targets.names report value.actions

def Result.completion (value : Result report config transferEnd triggerCut bound targets) : Nat := triggerCut + value.slot

theorem Result.bounds (value : Result report config transferEnd triggerCut bound targets) :
    triggerCut ≤ value.completion ∧
      value.completion ≤ triggerCut + CampusTCPRevocationBound.slots (cutState report triggerCut) bound ∧
      value.completion ≤ report.steps.length := by
  have bounds := C.found_bounds targets value.found
  have within := value.checked.within
  rw [List.length_drop] at bounds
  unfold Result.completion
  omega

def Result.current (value : Result report config transferEnd triggerCut bound targets) : State input :=
  cutState report value.completion

theorem Result.trace (value : Result report config transferEnd triggerCut bound targets) :
    Trace input (cutState report triggerCut) ((report.steps.drop triggerCut).map (·.event))
      (report.steps.drop triggerCut) report.final [] :=
  CampusTCPTraceSlices.Trace.drop report.trace value.checked.within

theorem Result.revoked (value : Result report config transferEnd triggerCut bound targets) :
    CampusTCPRevocationTargets.revoked input (cutState report triggerCut).authentication = true :=
  CampusTCPRevocationTrigger.report_triggerAt_revoked report triggerCut value.checked.trigger

theorem Result.closed (value : Result report config transferEnd triggerCut bound targets) :
    CampusTCPRevocationClosure.Closed targets value.current := by
  have closed := C.closed_at value.trace targets value.checked.shutdown value.found
  simpa only [cutState, CampusTCPTraceSlices.stateAt_drop, Result.current, Result.completion] using closed

theorem Result.enabled_at (value : Result report config transferEnd triggerCut bound targets)
    (slot : Nat) (within : slot ≤ (report.steps.drop triggerCut).length)
    (demand : CampusTCPRevocationControl.Demand)
    (selected : CampusTCPRevocationControl.pendingAt targets.names (cutState report triggerCut)
      CampusTCPRevocationMonitor.initial (report.steps.drop triggerCut) slot = some demand) :
    Nonempty (CampusTCPRevocationEnabled.Witness targets.names config.transfer.lossAllowance
      (S.stateAt (cutState report triggerCut) (report.steps.drop triggerCut) slot) demand) :=
  CampusTCPRevocationEnabled.check_witness targets.names config.transfer.lossAllowance
    (cutState report triggerCut) (report.steps.drop triggerCut) value.checked.enabled slot within demand selected

theorem Result.history (value : Result report config transferEnd triggerCut bound targets) :
    (CampusTCPSchedule.Report.cut report value.completion value.bounds.2.2).steps = report.steps.take value.completion := rfl

theorem Result.service_observed (value : Result report config transferEnd triggerCut bound targets)
    (actual : Step input) (member : actual ∈ report.steps) (served : Served input)
    (present : actual.result.service = some served) : served.observed = true ∧ served.routeMatched = true := by
  have checked := List.all_eq_true.mp value.checked.observations actual member
  simpa only [present, Option.all_some, Bool.and_eq_true] using checked

theorem Result.whole_budget (value : Result report config transferEnd triggerCut bound targets) :
    report.final.custody.dropped ≤ config.transfer.lossAllowance := by
  apply CampusTCPRevocationLoss.Trace.loss_budget report.trace config.transfer.lossAllowance
    (List.all_eq_true.mp value.checked.loss)
  exact Nat.zero_le _

theorem Result.future (value : Result report config transferEnd triggerCut bound targets) :
    CampusTCPRevocationClosure.Closed targets report.final ∧
      ∀ actual ∈ report.steps.drop value.completion, CampusTCPRevocationClosure.Quiet actual := by
  have history := CampusTCPCustodyFacts.Report.history
    (CampusTCPSchedule.Report.cut report triggerCut value.checked.within)
  have future := C.suffix_closed value.trace targets value.checked.shutdown value.revoked history value.found
  simpa only [List.drop_drop, Result.completion] using future

theorem Result.no_receipts_after (value : Result report config transferEnd triggerCut bound targets) :
    CampusTCPRevocationReadOrigin.NoReceiptsAfter report value.completion := by
  intro actual member later
  obtain ⟨slot, found⟩ := List.mem_iff_getElem?.mp member
  have within := (List.getElem?_eq_some_iff.mp found).1
  obtain ⟨recorded, same, before, _, _⟩ := CampusTCPSchedule.Trace.at report.trace slot within
  have equal : recorded = actual := Option.some.inj (same.symm.trans found)
  have clock := CampusTCPSchedule.Trace.slot_time report.trace slot (Nat.le_of_lt within)
  have stamp : actual.before.time = slot := by
    rw [equal] at before
    rw [← before] at clock
    simpa only [Input.initial, Nat.zero_add] using clock
  have afterCut : value.completion ≤ slot := by simpa only [stamp] using later
  have inSuffix : actual ∈ report.steps.drop value.completion := by
    apply List.mem_iff_getElem?.mpr
    refine ⟨slot - value.completion, ?_⟩
    simpa only [List.getElem?_drop, Nat.add_sub_of_le afterCut] using found
  exact (value.future.2 actual inSuffix).receipt

structure Certified (report : Report input events) (config : CampusTCPStartupTransferMonitor.Config)
    (transferEnd triggerCut bound : Nat) where
  targets : Targets input (cutState report triggerCut)
  result : Result report config transferEnd triggerCut bound targets

def certify (report : Report input events) (config : CampusTCPStartupTransferMonitor.Config)
    (transferEnd triggerCut bound : Nat) (raw : Raw) :
    Except String (Certified report config transferEnd triggerCut bound) := do
  if positive : 0 < bound then
    let targets ← Targets.check input (cutState report triggerCut) raw
    if actions : P.actions config transferEnd triggerCut targets.names report = true then
      if service : P.service config transferEnd triggerCut targets.names input.initial report.steps bound = true then
        match found : C.findCompletion targets (report.steps.drop triggerCut) bound with
        | none => throw "The recorded TCP suffix has no installed and drained completion cut."
        | some slot => return ⟨targets, ⟨slot, found, positive, actions, service⟩⟩
      else throw "The recorded TCP session does not meet its one whole service bound."
    else throw "The recorded TCP session does not meet its phased action contract."
  else throw "The TCP revocation service bound must be positive."

end Netlib.Check.CampusTCPRevocation
