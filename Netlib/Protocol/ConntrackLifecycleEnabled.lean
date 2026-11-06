import Netlib.Protocol.ConntrackLifecycle

/-!
# Existing-flow forwarding from preceding state

A confirmed lookup supplies the actual stored binding.
Route and filter conditions concern the stored pipeline before processing.
-/

namespace Netlib.Protocol.ConntrackLifecycle

open Packet

instance (state : State) : Decidable state.Valid :=
  decidable_of_iff (state.check = true) (State.check_correct state)

def selectedAttachment (record : Record) (direction : FlowNAT.Direction) : Attachment :=
  ⟨record.entry, direction, classify record direction, false⟩

theorem lookup_record (state : State) (input : Input) (hit : FlowNAT.Hit)
    (found : state.model.lookup input.zone input.packet = some hit) :
    ∃ record, state.records.find? (fun record => decide (record.entry.flow = hit.entry)) = some record := by
  have member := (FlowNAT.Snapshot.lookup_sound _ _ _ _ found).1
  obtain ⟨record, member, same⟩ := List.mem_map.mp member
  cases selected : state.records.find? (fun record => decide (record.entry.flow = hit.entry)) with
  | none =>
    have absent := List.find?_eq_none.mp selected record member
    exact False.elim (absent (by simpa using same))
  | some actual => exact ⟨actual, rfl⟩

theorem prepare_existing_selected (state : State) (input : Input) (hit : FlowNAT.Hit) (record : Record)
    (valid : state.Valid) (zone : input.zone < 65536)
    (transport : Conntrack.transport input.packet = true) (candidate : input.candidate = none)
    (found : state.model.lookup input.zone input.packet = some hit)
    (selected : state.records.find? (fun record => decide (record.entry.flow = hit.entry)) = some record) :
    ∃ prepared, prepare state input = .ok prepared ∧
      prepared.attachment = selectedAttachment record hit.direction ∧
      prepared.state = match hit.direction with | .original => state | .reply => state.markReply hit.entry := by
  have checked := (State.check_correct state).mpr valid
  have small : ¬input.zone ≥ 65536 := by omega
  simp only [prepare, checked, dite_true, small, ite_false, transport, Bool.not_true, Bool.false_eq_true,
    candidate, Option.isSome_none, pure, Except.pure]
  split
  · rename_i absent
    rw [found] at absent
    cases absent
  · rename_i actual lookup
    have same : actual = hit := Option.some.inj (lookup.symm.trans found)
    subst actual
    split
    · rename_i absent
      rw [selected] at absent
      cases absent
    · rename_i actual recordFound
      have same : actual = record := Option.some.inj (recordFound.symm.trans selected)
      subst actual
      split
      all_goals
        rename_i direction
        exact ⟨_, rfl, by simp [selectedAttachment, direction], by simp [direction]⟩

theorem prepare_existing_completes (state : State) (input : Input) (hit : FlowNAT.Hit)
    (valid : state.Valid) (zone : input.zone < 65536)
    (transport : Conntrack.transport input.packet = true) (candidate : input.candidate = none)
    (found : state.model.lookup input.zone input.packet = some hit) :
    ∃ record prepared,
      state.records.find? (fun record => decide (record.entry.flow = hit.entry)) = some record ∧
      record ∈ state.records ∧ record.entry.flow = hit.entry ∧
      prepare state input = .ok prepared ∧
      prepared.attachment = selectedAttachment record hit.direction ∧
      prepared.state = match hit.direction with | .original => state | .reply => state.markReply hit.entry := by
  obtain ⟨record, selected⟩ := lookup_record state input hit found
  obtain ⟨prepared, computed, attachment, changed⟩ :=
    prepare_existing_selected state input hit record valid zone transport candidate found selected
  exact ⟨record, prepared, selected, List.mem_of_find?_eq_some selected,
    of_decide_eq_true (List.find?_some (p := fun item : Record => decide (item.entry.flow = hit.entry)) selected),
    computed, attachment, changed⟩

theorem process_existing_forwarded (pipeline : Pipeline) (prepared : Prepared input) (nextHop : String)
    (existing : prepared.attachment.fresh = false)
    (route : Routing.nextHop pipeline.routes
      ((destinationStage prepared.attachment.entry prepared.attachment.direction).apply input.packet).destination = some nextHop)
    (forward : StatefulACL.Policy.evaluate pipeline.forwardDefault pipeline.forward prepared.attachment.classification
      ((destinationStage prepared.attachment.entry prepared.attachment.direction).apply input.packet) = .permit)
    (late : StatefulACL.Policy.evaluate pipeline.lateDefault pipeline.late prepared.attachment.classification
      ((sourceStage prepared.attachment.entry prepared.attachment.direction).apply
        ((destinationStage prepared.attachment.entry prepared.attachment.direction).apply input.packet)) = .permit) :
    ∃ outcome, process pipeline prepared = .ok outcome ∧
      outcome.state = prepared.state ∧ outcome.attachment = prepared.attachment ∧
      outcome.disposition = .forwarded ∧ outcome.nextHop = some nextHop ∧
      outcome.output = some (prepared.attachment.entry.flow.output prepared.attachment.direction) := by
  have attached : prepared.attachment.entry.flow.input prepared.attachment.direction = input.packet :=
    congrArg Prod.snd prepared.attached
  have target := stages_correct prepared.attachment.entry prepared.compatible prepared.attachment.direction
  rw [attached] at target
  simp only [process, route, forward, late, reduceCtorEq, ite_false, existing, Bool.false_eq_true]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, congrArg some target⟩

structure ForwardConditions (pipeline : Pipeline) (packet : Header) (attachment : Attachment) (hop : String) : Prop where
  existing : attachment.fresh = false
  route : Routing.nextHop pipeline.routes
    ((destinationStage attachment.entry attachment.direction).apply packet).destination = some hop
  forward : StatefulACL.Policy.evaluate pipeline.forwardDefault pipeline.forward attachment.classification
    ((destinationStage attachment.entry attachment.direction).apply packet) = .permit
  late : StatefulACL.Policy.evaluate pipeline.lateDefault pipeline.late attachment.classification
    ((sourceStage attachment.entry attachment.direction).apply
      ((destinationStage attachment.entry attachment.direction).apply packet)) = .permit

structure ExistingReady (pipeline : Pipeline) (state : State) (input : Input) (hit : FlowNAT.Hit) (hop : String) : Prop where
  valid : state.Valid
  zone : input.zone < 65536
  transport : Conntrack.transport input.packet = true
  candidate : input.candidate = none
  lookup : state.model.lookup input.zone input.packet = some hit
  forwarding : ∀ record ∈ state.records, record.entry.flow = hit.entry →
    ForwardConditions pipeline input.packet (selectedAttachment record hit.direction) hop

instance (pipeline : Pipeline) (packet : Header) (attachment : Attachment) (hop : String) :
    Decidable (ForwardConditions pipeline packet attachment hop) :=
  decidable_of_iff (attachment.fresh = false ∧
    Routing.nextHop pipeline.routes
      ((destinationStage attachment.entry attachment.direction).apply packet).destination = some hop ∧
    StatefulACL.Policy.evaluate pipeline.forwardDefault pipeline.forward attachment.classification
      ((destinationStage attachment.entry attachment.direction).apply packet) = .permit ∧
    StatefulACL.Policy.evaluate pipeline.lateDefault pipeline.late attachment.classification
      ((sourceStage attachment.entry attachment.direction).apply
        ((destinationStage attachment.entry attachment.direction).apply packet)) = .permit) (by
      constructor
      · rintro ⟨existing, route, forward, late⟩
        exact ⟨existing, route, forward, late⟩
      · intro ready
        exact ⟨ready.existing, ready.route, ready.forward, ready.late⟩)

instance (pipeline : Pipeline) (state : State) (input : Input) (hit : FlowNAT.Hit) (hop : String) :
    Decidable (ExistingReady pipeline state input hit hop) :=
  decidable_of_iff (state.Valid ∧ input.zone < 65536 ∧ Conntrack.transport input.packet = true ∧
    input.candidate = none ∧ state.model.lookup input.zone input.packet = some hit ∧
    ∀ record ∈ state.records, record.entry.flow = hit.entry →
      ForwardConditions pipeline input.packet (selectedAttachment record hit.direction) hop) (by
      constructor
      · rintro ⟨valid, zone, transport, candidate, lookup, forwarding⟩
        exact ⟨valid, zone, transport, candidate, lookup, forwarding⟩
      · intro ready
        exact ⟨ready.valid, ready.zone, ready.transport, ready.candidate, ready.lookup, ready.forwarding⟩)

theorem prepared_selected_confirmed (state : State) (hit : FlowNAT.Hit) (record : Record) (prepared : Prepared input)
    (member : record ∈ state.records) (attachment : prepared.attachment = selectedAttachment record hit.direction)
    (changed : prepared.state = match hit.direction with | .original => state | .reply => state.markReply hit.entry) :
    ∃ actual ∈ prepared.state.records, actual.entry = prepared.attachment.entry := by
  rw [attachment]
  cases direction : hit.direction
  · rw [direction] at changed
    exact ⟨record, by rw [changed]; exact member, rfl⟩
  · rw [direction] at changed
    refine ⟨State.markRecord hit.entry record, ?_, ?_⟩
    · rw [changed]
      exact List.mem_map_of_mem member
    · exact State.markRecord_entry _ _

theorem step_existing_enabled (pipeline : Pipeline) (state : State) (input : Input) (hit : FlowNAT.Hit) (hop : String)
    (ready : ExistingReady pipeline state input hit hop) :
    ∃ outcome, step pipeline state input = .ok outcome ∧ outcome.disposition = .forwarded ∧
      outcome.nextHop = some hop ∧ outcome.attachment.entry.flow = hit.entry ∧
      outcome.attachment.direction = hit.direction ∧ outcome.output = some hit.output := by
  obtain ⟨record, prepared, _, member, same, attached, attachment, _⟩ :=
    prepare_existing_completes state input hit ready.valid ready.zone ready.transport ready.candidate ready.lookup
  have native := ready.forwarding record member same
  rw [← attachment] at native
  obtain ⟨outcome, processed, _, actualAttachment, forwarded, nextHop, output⟩ :=
    process_existing_forwarded pipeline prepared hop native.existing native.route native.forward native.late
  refine ⟨outcome, ?_, forwarded, nextHop, ?_, ?_, ?_⟩
  · simp only [step, attached, bind, Except.bind, processed]
  · rw [actualAttachment, attachment]
    exact same
  · rw [actualAttachment, attachment]
    rfl
  · rw [output, attachment]
    exact congrArg some (congrArg (fun entry => entry.output hit.direction) same)

end Netlib.Protocol.ConntrackLifecycle
