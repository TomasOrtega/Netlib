import Netlib.Check.CampusTCPStartupJobs
import Netlib.Check.CampusTCPRoundAssignment
import Netlib.Check.CampusTCPCustodyFacts

/-!
# Actual queue-weight changes while draining startup

The arithmetic uses the same pending rows and actual custody resolution.
A failed service is not treated as a completed ticket.
-/

namespace Netlib.Check.CampusTCPStartupJobDrain

open CampusTCPModel CampusTCPStartupJobs

variable {input : Input}

def sourceWeight (stage : Stage) : Produced input.active input.passive → Nat
  | .recovery _ occurrence _ => stageWeight occurrence.kind stage
  | _ => 0

def packetWeight (item : PacketItem input) : Nat :=
  match item.value.payload with
  | .ingress _ produced => sourceWeight .ingress produced
  | .link _ served _ _ => sourceWeight .link served.ticket.value.produced

def ticketWeight (item : TicketItem input) : Nat := sourceWeight .ticket item.value.produced

theorem packetJob_weight (item : PacketItem input) :
    ((packetJob item).map Job.weight).getD 0 = packetWeight item := by
  rcases item with ⟨id, payload, parent⟩
  cases payload with
  | ingress index produced =>
    cases produced <;> simp only [packetJob, packetWeight, sourceWeight, Job.weight, Job.kind, Job.source,
      Job.stage, Option.map_none, Option.map_some, Option.getD_none, Option.getD_some]
  | link index served emission emitted =>
    rcases served with ⟨time, ⟨ticketID, ⟨outputIndex, produced, ingress, gateway, epoch⟩⟩,
      before, mode, evidence, computed, observed⟩
    cases produced <;> simp only [packetJob, packetWeight, sourceWeight, Job.weight, Job.kind, Job.source,
      Job.stage, Option.map_none, Option.map_some, Option.getD_none, Option.getD_some]

theorem ticketJob_weight (item : TicketItem input) :
    ((ticketJob item).map Job.weight).getD 0 = ticketWeight item := by
  rcases item with ⟨id, outputIndex, produced, ingress, gateway, epoch⟩
  cases produced <;> simp only [ticketJob, ticketWeight, sourceWeight, Job.weight, Job.kind, Job.source,
    Job.stage, Option.map_none, Option.map_some, Option.getD_none, Option.getD_some]

private theorem filterMap_weight (rows : List α) (extract : α → Option (Job input)) :
    ((rows.filterMap extract).map Job.weight).sum =
      (rows.map (fun row => ((extract row).map Job.weight).getD 0)).sum := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    cases found : extract row <;> simp only [List.filterMap_cons, found, List.map_cons, Option.map_none,
      Option.map_some, Option.getD_none, Option.getD_some, List.sum_cons, Nat.zero_add, ih]

theorem potential_rows (state : State input) :
    potential state = (state.custody.pending.map packetWeight).sum + (state.work.pending.map ticketWeight).sum := by
  unfold potential inventory
  rw [List.map_append, List.sum_append, filterMap_weight, filterMap_weight]
  simp only [packetJob_weight, ticketJob_weight]

theorem packetWeight_positive (item : PacketItem input) (recovery : item.value.payload.isRecovery = true) :
    0 < packetWeight item := by
  obtain ⟨job, found⟩ := (packetJob_exists item).mpr recovery
  have weight := packetJob_weight item
  rw [found] at weight
  have equal : job.weight = packetWeight item := by simpa only [Option.map_some, Option.getD_some] using weight
  rw [← equal]
  exact Job.weight_positive job

theorem resolved_weight {packetID : Nat} (resolved : Theory.PacketCustody.Resolved before packetID disposition) :
    (before.pending.map (packetWeight (input := input))).sum =
      packetWeight resolved.item + (resolved.state.pending.map packetWeight).sum := by
  have same := (resolved.completed.pendingPerm.map (packetWeight (input := input))).sum_nat
  simpa only [Theory.PacketCustody.State.pending, Theory.PacketCustody.Resolved.item,
    Theory.PacketCustody.Resolved.state, List.map_cons, List.sum_cons] using same

theorem Step.drop_weight (actual : Step input) (id : Nat) (event : actual.event = .dropPacket id) :
    ∃ resolved : Theory.PacketCustody.Resolved actual.before.custody id .dropped,
      Theory.PacketCustody.resolve actual.before.custody id .dropped = .ok resolved ∧
        potential actual.result.state + packetWeight resolved.item = potential actual.before := by
  obtain ⟨resolved, computed, custody⟩ := CampusTCPCustodyFacts.Step.drop actual id event
  obtain ⟨effect, prepared, core, final⟩ := actual.processed
  have exactCore : effect = { state := actual.before } := by
    rw [event] at core
    simpa only [processCore, pure, Except.pure, Except.ok.injEq] using core.symm
  have work : actual.result.state.work = actual.before.work := by rw [final, exactCore]
  have removed := resolved_weight resolved
  refine ⟨resolved, computed, ?_⟩
  rw [potential_rows, potential_rows, custody, work]
  omega

theorem Step.drop_strict (actual : Step input) (id : Nat) (event : actual.event = .dropPacket id)
    (recovery : ∀ item ∈ actual.before.custody.pending, item.id = id → item.value.payload.isRecovery = true) :
    potential actual.result.state < potential actual.before := by
  obtain ⟨resolved, _, delta⟩ := Step.drop_weight actual id event
  have positive := packetWeight_positive resolved.item (recovery resolved.item resolved.member resolved.selected)
  omega

private theorem ingress_weight (item : PacketItem input) (index : Nat) (source : Source input)
    (payload : item.value.payload = .ingress index source.produced) :
    packetWeight item = stageWeight source.occurrence.kind .ingress := by
  rw [packetWeight, payload]
  rfl

private theorem new_ticket_weight (before : State input) (index : Nat) (ingress : I.InterfaceRef) (source : Source input) :
    ticketWeight (CampusTCPRoundAssignment.ticket before index ingress source.produced) =
      stageWeight source.occurrence.kind .ticket := rfl

theorem assignment_weight (source : Source input)
    (facts : CampusTCPRoundAssignment.AssignmentFacts before index ingress source.produced actual) :
    potential actual.result.state + 1 = potential before := by
  obtain ⟨id, resolved, _, _, payload, custody, _⟩ := facts.consumed
  have removed := resolved_weight resolved
  rw [ingress_weight resolved.item index source payload] at removed
  have gap : stageWeight source.occurrence.kind .ingress = stageWeight source.occurrence.kind .ticket + 1 := by
    cases source.occurrence.kind <;> rfl
  rw [potential_rows, potential_rows, facts.work, custody]
  change (resolved.state.pending.map packetWeight).sum +
    ((before.work.pending ++ [CampusTCPRoundAssignment.ticket before index ingress source.produced]).map ticketWeight).sum + 1 = _
  rw [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero, new_ticket_weight]
  omega

theorem assignment_strict (source : Source input)
    (facts : CampusTCPRoundAssignment.AssignmentFacts before index ingress source.produced actual) :
    potential actual.result.state < potential before := by
  have delta := assignment_weight source facts
  omega

end Netlib.Check.CampusTCPStartupJobDrain
