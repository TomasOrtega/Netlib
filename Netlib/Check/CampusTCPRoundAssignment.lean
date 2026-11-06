import Netlib.Check.CampusTCPEnabled
import Netlib.Check.CampusTCPSchedule

/-!
# Assignment in one lossless TCP round

The actual output index determines the new ticket.
Assignment consumes the selected pending ingress identity.
-/

namespace Netlib.Check.CampusTCPRoundAssignment

open CampusTCPModel

namespace O
export Theory.Outstanding (Item newItem enqueue)
end O
namespace C
export Theory.PacketCustody (Resolved History resolve)
end C

def ticketValue (before : State input) (index : Nat) (ingress : I.InterfaceRef)
    (produced : Produced input.active input.passive) : Ticket input.active input.passive :=
  ⟨index, produced, ingress, before.owner produced.actor, before.routeEpoch⟩

def ticket (before : State input) (index : Nat) (ingress : I.InterfaceRef)
    (produced : Produced input.active input.passive) : O.Item (Ticket input.active input.passive) :=
  O.newItem before.work (ticketValue before index ingress produced)

@[simp] theorem ticket_id (before : State input) (index : Nat) (ingress : I.InterfaceRef)
    (produced : Produced input.active input.passive) :
    (ticket before index ingress produced).id = before.work.nextID := rfl

@[simp] theorem ticket_source (before : State input) (index : Nat) (ingress : I.InterfaceRef)
    (produced : Produced input.active input.passive) :
    (ticket before index ingress produced).value.source = produced.source := rfl

theorem Step.assign_frame (actual : Step input) (index : Nat) (ingress : I.InterfaceRef)
    (event : actual.event = .assign index ingress) (produced : Produced input.active input.passive)
    (source : actual.before.outputs[index]? = some produced) :
    ∃ custody, prepareCustody actual.before (.assign index ingress) = .ok custody ∧
      actual.result = { state := { actual.before with
        work := O.enqueue actual.before.work (ticketValue actual.before index ingress produced),
        custody, time := actual.before.time + 1 } } := by
  obtain ⟨effect, custody, computed, prepared, final⟩ := actual.transaction
  rw [event] at computed prepared
  simp only [processCore, CampusTCPModel.get, source, bind, Except.bind, pure, Except.pure] at computed
  repeat' first
    | (solve | cases computed; exact ⟨custody, prepared, final⟩)
    | (cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

structure AssignmentFacts (before : State input) (index : Nat) (ingress : I.InterfaceRef)
    (produced : Produced input.active input.passive) (actual : Step input) : Prop where
  beforeEq : actual.before = before
  event : actual.event = .assign index ingress
  supported : actual.result.supported = true
  passed : actual.result.passed = true
  work : actual.result.state.work = O.enqueue before.work (ticketValue before index ingress produced)
  workValid : actual.result.state.work.Valid
  pending : ticket before index ingress produced ∈ actual.result.state.work.pending
  frame : actual.result = { state := { before with
    work := O.enqueue before.work (ticketValue before index ingress produced),
    custody := actual.result.state.custody, time := before.time + 1 } }
  consumed : ∃ id, ∃ resolved : C.Resolved before.custody id .assigned,
    before.custody.pendingID (Transit.ingressAt index) = some id ∧
    C.resolve before.custody id .assigned = .ok resolved ∧
    resolved.item.value.payload = .ingress index produced ∧
    actual.result.state.custody = resolved.state ∧
    ∀ item ∈ actual.result.state.custody.pending, item.id ≠ id

theorem assign_enabled (before : State input) (index : Nat) (ingress : I.InterfaceRef)
    (produced : Produced input.active input.passive) (source : before.outputs[index]? = some produced)
    (route : CampusTCPEnabled.RouteReady before produced.actor)
    (pending : CampusTCPEnabled.IngressPending before index) (valid : before.work.Valid)
    (history : C.History before.custody) (sources : CampusTCPCustodyFacts.Sources before) :
    ∃ actual : Step input, AssignmentFacts before index ingress produced actual := by
  obtain ⟨effect, computed, supported, passed, work⟩ :=
    CampusTCPEnabled.assign_enabled before index ingress produced source route pending
  let actual : Step input := ⟨before, .assign index ingress, effect, computed⟩
  obtain ⟨custody, prepared, frame⟩ := Step.assign_frame actual index ingress rfl produced source
  obtain ⟨id, resolved, selected, resolution, predicate, absent⟩ :=
    CampusTCPCustodyFacts.Step.assign actual index ingress rfl history
  obtain ⟨selectedProduced, payload⟩ := CampusTCPCustodyFacts.ingress_stage _ _ predicate
  have selectedSource := sources resolved.item (List.mem_append_right _ resolved.member)
  rw [payload] at selectedSource
  have same : selectedProduced = produced := Option.some.inj (selectedSource.symm.trans source)
  subst selectedProduced
  have custodyEq : custody = resolved.state := by
    simp only [prepareCustody, selected, resolution, Except.mapError, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at prepared
    exact prepared.symm
  have actualCustody : actual.result.state.custody = custody := by rw [frame]
  refine ⟨actual, rfl, rfl, supported, passed, work, ?_, ?_, ?_,
    id, resolved, selected, resolution, payload, actualCustody.trans custodyEq, absent⟩
  · rw [work]
    exact Theory.Outstanding.enqueue_valid _ _ valid
  · rw [work]
    exact List.mem_append_right _ (by simp only [ticket, ticketValue, List.mem_singleton])
  · rw [frame]

theorem Report.assign_enabled (report : Report input events) (index : Nat) (ingress : I.InterfaceRef)
    (produced : Produced input.active input.passive) (source : report.final.outputs[index]? = some produced)
    (route : CampusTCPEnabled.RouteReady report.final produced.actor)
    (pending : CampusTCPEnabled.IngressPending report.final index) :
    ∃ actual : Step input, AssignmentFacts report.final index ingress produced actual :=
  CampusTCPRoundAssignment.assign_enabled report.final index ingress produced source route pending (CampusTCPOrigins.Report.work_valid report)
    (CampusTCPCustodyFacts.Report.history report) (CampusTCPCustodyFacts.Report.sources report)

theorem Report.assignment_after_output (report : Report input events) (outputStep : Step input)
    (atFinal : outputStep.result.state = report.final) (produced : Produced input.active input.passive)
    (output : outputStep.result.output = some produced)
    (route : CampusTCPEnabled.RouteReady report.final produced.actor) (ingress : I.InterfaceRef) :
    ∃ actual : Step input, AssignmentFacts report.final outputStep.before.outputs.length ingress produced actual := by
  have source : report.final.outputs[outputStep.before.outputs.length]? = some produced := by
    rw [← atFinal, CampusTCPOrigins.output_history outputStep, output]
    simp
  obtain ⟨packet, member, _, payload⟩ := CampusTCPCustodyFacts.Step.output_packet outputStep produced output
  have pending : CampusTCPEnabled.IngressPending report.final outputStep.before.outputs.length := by
    rw [← atFinal]
    exact ⟨packet, member, by simp only [payload, Transit.ingressAt, beq_self_eq_true]⟩
  exact Report.assign_enabled report outputStep.before.outputs.length ingress produced source route pending

theorem Report.append_assignment (report : Report input events) (supported : report.supported = true)
    (finished : report.remaining = []) (index : Nat) (ingress : I.InterfaceRef)
    (produced : Produced input.active input.passive) (source : report.final.outputs[index]? = some produced)
    (route : CampusTCPEnabled.RouteReady report.final produced.actor)
    (pending : CampusTCPEnabled.IngressPending report.final index) :
    ∃ actual : Step input, ∃ facts : AssignmentFacts report.final index ingress produced actual,
      ∃ after : Report input (events ++ [actual.event]),
        after = CampusTCPSchedule.Report.appendStep report supported finished actual facts.beforeEq facts.supported ∧
        after.final = actual.result.state ∧ after.steps = report.steps ++ [actual] ∧ after.supported = true := by
  obtain ⟨actual, facts⟩ := Report.assign_enabled report index ingress produced source route pending
  exact ⟨actual, facts, CampusTCPSchedule.Report.appendStep report supported finished actual facts.beforeEq facts.supported,
    rfl, rfl, rfl, CampusTCPSchedule.Report.appendStep_supported report supported finished actual facts.beforeEq facts.supported⟩

theorem Step.service_lookup (actual : Step input) (served : Served input) (recorded : actual.result.service = some served) :
    actual.result.state.services[actual.before.services.length]? = some served := by
  rw [CampusTCPOrigins.service_history actual, recorded]
  simp

end Netlib.Check.CampusTCPRoundAssignment
