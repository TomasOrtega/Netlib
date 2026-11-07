import Netlib.Check.CampusTCPStartupJobUnique
import Netlib.Check.CampusTCPOrigins

/-!
# Actual output identity selected by a startup job event

Work IDs select one current ticket. Service indices select one stored service.
Packet equality is unnecessary for either identity.
-/

namespace Netlib.Check.CampusTCPStartupJobEvent

open CampusTCPModel CampusTCPStartupJobs

variable {input : Input} {events : List Event} {config : CampusTCPStartupTransferMonitor.Config}

theorem Report.same_event_output (report : Report input events) (left right : Job input)
    (first : left ∈ inventory report.final) (second : right ∈ inventory report.final)
    (event : CampusTCPStartupSelection.Job.event config left = CampusTCPStartupSelection.Job.event config right) :
    left.outputIndex = right.outputIndex := by
  have leftPending := inventory_pending first
  have rightPending := inventory_pending second
  cases left with
  | ingress item index source payload =>
    cases right with
    | ingress other selected secondSource secondPayload => exact (Event.assign.inj event).1
    | ticket other secondSource production | link other selected served emission emitted secondSource production secondPayload => cases event
  | ticket item source production =>
    cases right with
    | ingress other selected secondSource secondPayload | link other selected served emission emitted secondSource secondProduction secondPayload => cases event
    | ticket other secondSource secondProduction =>
      have sameID : item.id = other.id := (Event.serve.inj event).1
      have valid := CampusTCPOrigins.Report.work_valid report
      obtain ⟨completed, computed, selected⟩ := Theory.Outstanding.complete_item report.final.work item valid leftPending
      have same : item = other := selected.symm.trans (completed.item_eq valid other rightPending sameID.symm)
      exact congrArg (fun ticket => ticket.value.outputIndex) same
  | link item index served emission emitted source production payload =>
    cases right with
    | ingress other selected secondSource secondPayload | ticket other secondSource secondProduction => cases event
    | link other selected secondServed secondEmission secondEmitted secondSource secondProduction secondPayload =>
      have serviceIndex : index = selected := (Event.deliver.inj event).1
      have leftSource := CampusTCPCustodyFacts.Report.sources report item (List.mem_append_right _ leftPending)
      have rightSource := CampusTCPCustodyFacts.Report.sources report other (List.mem_append_right _ rightPending)
      rw [payload] at leftSource
      rw [secondPayload] at rightSource
      rw [serviceIndex] at leftSource
      have same : served = secondServed := Option.some.inj (leftSource.symm.trans rightSource)
      exact congrArg (fun service : Served input => service.ticket.value.outputIndex) same

theorem Report.same_event_job (report : Report input events)
    (nocopy : ∀ actual ∈ report.steps, ∀ id, actual.event ≠ .copyPacket id)
    (left right : Job input) (first : left ∈ inventory report.final) (second : right ∈ inventory report.final)
    (event : CampusTCPStartupSelection.Job.event config left = CampusTCPStartupSelection.Job.event config right) : left = right :=
  (CampusTCPStartupJobUnique.Report.linear report nocopy).job_eq first second (Report.same_event_output report left right first second event)

end Netlib.Check.CampusTCPStartupJobEvent
