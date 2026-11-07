import Netlib.Check.CampusTCPStartupProfileFacts
import Netlib.Check.CampusTCPCustodyFacts

/-!
# The raw ingress retained by an actual startup ticket

The earlier allowed assignment selects a real pending ingress packet.
Its output lookup identifies the ticket's source and actor.
-/

namespace Netlib.Check.CampusTCPStartupTicketIngress

open CampusTCPModel

namespace E
export CampusTCPStartupTransferExecution (initial monitorAt actions actions_correct)
end E
namespace P
export CampusTCPStartupMonitor (Monitor allowed nextDemand)
end P
namespace M
export CampusTCPStartupTransferMonitor (Config)
end M

variable {input : Input} {config : M.Config} {state : State input} {monitor : P.Monitor}

private theorem allowed_assign (prep : CampusTCPStartupProfile.Prep config.startup)
    (permitted : P.allowed config state monitor (.assign index ingress) = true) :
    CampusTCPStartupSelection.jobAllowed config state (.assign index ingress) = true := by
  cases mode : monitor.mode with
  | drive => simpa only [P.allowed, mode, CampusTCPStartupSelection.allowed] using permitted
  | preparation position =>
    have selected := CampusTCPStartupProfile.preparation_allowed prep mode permitted
    cases selected
  | opening =>
    simp only [P.allowed, mode, P.nextDemand] at permitted
    have impossible := of_decide_eq_true permitted
    cases impossible
  | setup stage =>
    cases stage <;> simp only [P.allowed, mode, P.nextDemand, CampusTCPStartupMonitor.Setup.event] at permitted
    all_goals have impossible := of_decide_eq_true permitted; cases impossible
  | data | invalid => simp only [P.allowed, mode, Bool.false_eq_true] at permitted

private theorem selected_ingress (sources : CampusTCPCustodyFacts.Sources state)
    (lookup : state.outputs[index]? = some produced)
    (permitted : CampusTCPStartupSelection.jobAllowed config state (.assign index ingress) = true) :
    ingress = config.transfer.ingress .primary produced.actor := by
  obtain ⟨job, member, chosen⟩ := List.any_eq_true.mp permitted
  have event := of_decide_eq_true chosen
  have pending := CampusTCPStartupJobs.inventory_pending member
  cases job with
  | ingress item outputIndex source payload =>
    cases event
    have selected := sources item (List.mem_append_right _ pending)
    rw [payload] at selected
    have same := Option.some.inj (lookup.symm.trans selected)
    rw [same]
    rfl
  | ticket item source production => cases event
  | link item index served emission emitted source production payload => cases event

theorem Report.pending_ingress (whole : Report input events) (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (within : count ≤ whole.steps.length)
    (ending : E.monitorAt config (E.initial config) whole.steps count = .startup current)
    (item : Work.Item (Ticket input.active input.passive))
    (pending : item ∈ (CampusTCPSchedule.Report.cut whole count within).final.work.pending) :
    item.value.ingress = config.transfer.ingress .primary item.value.produced.actor := by
  obtain ⟨assignment, index, ingress, produced, present, event, lookup, ticket, earlier⟩ :=
    CampusTCPOrigins.Report.pending_origin (CampusTCPSchedule.Report.cut whole count within) item pending
  change assignment ∈ whole.steps.take count at present
  obtain ⟨slot, selected⟩ := List.mem_iff_getElem?.mp present
  have inside := (List.getElem?_eq_some_iff.mp selected).1
  rw [List.length_take, Nat.min_eq_left within] at inside
  rw [List.getElem?_take_of_lt inside] at selected
  obtain ⟨actual, found, before, jointEvent, after⟩ := CampusTCPSchedule.Trace.at whole.trace slot (Nat.lt_of_lt_of_le inside within)
  have same : actual = assignment := Option.some.inj (found.symm.trans selected)
  subst actual
  obtain ⟨prior, mode⟩ := CampusTCPStartupProfileFacts.monitorAt_startup_past ending (Nat.le_of_lt inside)
  have permitted := (E.actions_correct _ _ _ _).mp actions slot (Nat.lt_of_lt_of_le inside within)
  rw [mode] at permitted
  have currentGuard : P.allowed config assignment.before prior (.assign index ingress) = true := by
    simpa only [CampusTCPStartupTransferExecution.allowed, ← before, ← jointEvent, event] using permitted
  have rawIngress := selected_ingress (config := config)
    (CampusTCPCustodyFacts.Report.each_sources whole assignment (List.mem_of_mem_take present)) lookup (allowed_assign prep currentGuard)
  rw [ticket]
  exact rawIngress

end Netlib.Check.CampusTCPStartupTicketIngress
