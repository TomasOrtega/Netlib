import Netlib.Check.CampusTCPDropIDs

/-!
# Loss allowance across an actual report prefix

The suffix retains the same packet identities and source records.
Its allowance is the whole allowance less losses in the prefix.
-/

namespace Netlib.Check.CampusTCPReportLoss

open CampusTCPModel

variable {input : Input} {events priorEvents : List Event}

abbrev dropID (actual : Step input) : Option Nat := CampusTCPDropIDs.dropID actual

def drops (steps : List (Step input)) : Nat :=
  steps.countP (fun actual => CampusTCPCustodyFacts.dropEvent actual.event)

def dropIDs (steps : List (Step input)) : List Nat := steps.filterMap dropID

theorem dropIDs_length (steps : List (Step input)) : (dropIDs steps).length = drops steps := by
  induction steps with
  | nil => rfl
  | cons actual rest ih =>
    simp only [dropIDs, drops] at ih ⊢
    cases event : actual.event <;>
      simp [dropID, CampusTCPDropIDs.dropID, CampusTCPDropIDs.eventDropID, event, CampusTCPCustodyFacts.dropEvent, ih, Nat.add_comm]

theorem drops_append (prior later : List (Step input)) :
    drops (prior ++ later) = drops prior + drops later := List.countP_append

theorem dropIDs_append (prior later : List (Step input)) :
    dropIDs (prior ++ later) = dropIDs prior ++ dropIDs later := List.filterMap_append

theorem Report.drop_count (report : Report input events) : report.final.custody.dropped = drops report.steps :=
  CampusTCPCustodyFacts.Report.drop_count report

theorem Report.drop_ids_count (report : Report input events) :
    report.final.custody.dropped = (dropIDs report.steps).length :=
  (Report.drop_count report).trans (dropIDs_length _).symm

theorem Report.drop_ids (report : Report input events) : report.final.custody.droppedIDs = dropIDs report.steps :=
  CampusTCPDropIDs.Report.droppedIDs report

theorem Report.drop_ids_distinct (report : Report input events) : (dropIDs report.steps).Nodup :=
  CampusTCPDropIDs.Report.ids_nodup report

theorem Report.drop_split (prior : Report input priorEvents) (report : Report input events)
    (retained : prior.steps <+: report.steps) :
    report.final.custody.dropped = prior.final.custody.dropped + drops (report.steps.drop prior.steps.length) := by
  obtain ⟨later, same⟩ := retained
  rw [Report.drop_count report, Report.drop_count prior, ← same, List.drop_left, drops_append]

theorem Report.drop_ids_split (prior : Report input priorEvents) (report : Report input events)
    (retained : prior.steps <+: report.steps) :
    dropIDs report.steps = dropIDs prior.steps ++ dropIDs (report.steps.drop prior.steps.length) := by
  obtain ⟨later, same⟩ := retained
  rw [← same, List.drop_left, dropIDs_append]

theorem Report.drop_ids_disjoint (prior : Report input priorEvents) (report : Report input events)
    (retained : prior.steps <+: report.steps) :
    ∀ id ∈ dropIDs prior.steps, ∀ later ∈ dropIDs (report.steps.drop prior.steps.length), id ≠ later := by
  have distinct := Report.drop_ids_distinct report
  rw [Report.drop_ids_split prior report retained] at distinct
  exact (List.nodup_append.mp distinct).2.2

theorem Report.prefix_allowance (prior : Report input priorEvents) (report : Report input events)
    (retained : prior.steps <+: report.steps) (allowance : Nat)
    (bounded : report.final.custody.dropped ≤ allowance) : prior.final.custody.dropped ≤ allowance := by
  have total := Report.drop_split prior report retained
  omega

theorem Report.remaining_allowance (prior : Report input priorEvents) (report : Report input events)
    (retained : prior.steps <+: report.steps) (allowance : Nat)
    (bounded : report.final.custody.dropped ≤ allowance) :
    drops (report.steps.drop prior.steps.length) ≤ allowance - prior.final.custody.dropped := by
  have total := Report.drop_split prior report retained
  omega

theorem Report.allowance_conserved (prior : Report input priorEvents) (report : Report input events)
    (retained : prior.steps <+: report.steps) (allowance : Nat)
    (bounded : report.final.custody.dropped ≤ allowance) :
    prior.final.custody.dropped + (allowance - prior.final.custody.dropped) = allowance := by
  have spent := Report.prefix_allowance prior report retained allowance bounded
  omega

theorem Report.suffix_drop_source (prior : Report input priorEvents) (report : Report input events)
    (actual : Step input) (member : actual ∈ report.steps.drop prior.steps.length) (id : Nat)
    (selected : dropID actual = some id) :
    ∃ resolved : Theory.PacketCustody.Resolved actual.before.custody id .dropped,
      Theory.PacketCustody.resolve actual.before.custody id .dropped = .ok resolved ∧
      actual.result.state.custody = resolved.state ∧
      CampusTCPCustodyFacts.Sourced actual.before resolved.item.value.payload := by
  have event : actual.event = .dropPacket id := by
    cases event : actual.event <;> simp only [dropID, CampusTCPDropIDs.dropID, CampusTCPDropIDs.eventDropID, event, reduceCtorEq] at selected
    exact congrArg Event.dropPacket (Option.some.inj selected)
  obtain ⟨resolved, computed, state⟩ := CampusTCPCustodyFacts.Step.drop actual id event
  refine ⟨resolved, computed, state, ?_⟩
  have source := CampusTCPCustodyFacts.Report.each_sources report actual (List.mem_of_mem_drop member)
  exact source resolved.item (List.mem_append_right _ resolved.member)

end Netlib.Check.CampusTCPReportLoss
