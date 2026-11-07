import Netlib.Protocol.ConntrackLifecycleEnabled

/-!
# Fresh forwarding from current tuple and policy guards

Both candidate keys must be absent from the confirmed table.
This derives ordinary confirmation without assuming a future successful packet.
-/

namespace Netlib.Protocol.ConntrackLifecycle

open Packet

def FreshKeys (state : State) (entry : NetfilterNAT.Entry) : Prop :=
  entry.flow.key .original ∉ state.model.keys ∧ entry.flow.key .reply ∉ state.model.keys

theorem fresh_insert_valid (valid : state.Valid) (compatible : entry.Compatible)
    (keys : FreshKeys state entry) :
    (⟨state.records ++ [⟨entry, false⟩]⟩ : State).Valid := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro flow member
    simp only [State.model, List.map_append, List.map_cons, List.map_nil, List.mem_append,
      List.mem_singleton] at member
    rcases member with old | rfl
    · exact valid.1.1 flow old
    · exact compatible.1
  · have before := valid.1.2
    have distinct := compatible.1.2.2.2.2.2
    have full : (⟨state.records ++ [⟨entry, false⟩]⟩ : State).model.keys =
        state.model.keys ++ [entry.flow.key .original, entry.flow.key .reply] := by
      simp only [State.model, FlowNAT.Snapshot.keys, FlowNAT.Snapshot.slots, List.map_append,
        List.map_cons, List.map_nil, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.map_append]
      rfl
    rw [full]
    apply List.nodup_append.mpr
    refine ⟨before, by simpa using distinct, ?_⟩
    intro key member selected belongs same
    simp only [List.mem_cons, List.not_mem_nil, or_false] at belongs
    rcases belongs with rfl | rfl
    · exact keys.1 (same ▸ member)
    · exact keys.2 (same ▸ member)
  · intro record member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact valid.2 record old
    · exact compatible

theorem fresh_lookup_none (keys : FreshKeys state entry) :
    state.model.lookup entry.flow.originalZone entry.flow.original = none := by
  cases found : state.model.lookup entry.flow.originalZone entry.flow.original with
  | none => rfl
  | some hit =>
    have member := (FlowNAT.Snapshot.lookup_sound _ _ _ _ found).1
    have selected := (FlowNAT.Snapshot.lookup_sound _ _ _ _ found).2
    have keyMember : hit.key ∈ state.model.keys :=
      List.mem_map.mpr ⟨hit, (FlowNAT.Snapshot.mem_slots _ _).mpr member, rfl⟩
    rw [selected] at keyMember
    exact False.elim (keys.1 keyMember)

theorem prepare_fresh_enabled (state : State) (input : Input) (entry : NetfilterNAT.Entry)
    (valid : state.Valid) (zone : input.zone < 65536) (transport : Conntrack.transport input.packet = true)
    (candidate : input.candidate = some entry) (compatible : entry.Compatible)
    (matching : entry.flow.original = input.packet ∧ entry.flow.originalZone = input.zone)
    (keys : FreshKeys state entry) :
    ∃ prepared, prepare state input = .ok prepared ∧ prepared.state = state ∧
      prepared.attachment = ⟨entry, .original, .new, true⟩ := by
  have checked := (State.check_correct state).mpr valid
  have candidateChecked := (NetfilterNAT.Entry.check_correct entry).mpr compatible
  have found : state.model.lookup input.zone input.packet = none := by
    rw [← matching.1, ← matching.2]
    exact fresh_lookup_none keys
  simp only [prepare, checked, dite_true, Nat.not_le.mpr zone, ite_false, transport,
    Bool.not_true, Bool.false_eq_true, candidate, candidateChecked, matching, bind, Except.bind, pure, Except.pure]
  split
  · simp only [true_and, dite_true]
    exact ⟨_, rfl, rfl, rfl⟩
  · rename_i hit selected
    rw [found] at selected
    cases selected

structure FreshForwardConditions (pipeline : Pipeline) (packet : Header)
    (entry : NetfilterNAT.Entry) (hop : String) : Prop where
  route : Routing.nextHop pipeline.routes ((destinationStage entry .original).apply packet).destination = some hop
  forward : StatefulACL.Policy.evaluate pipeline.forwardDefault pipeline.forward .new
    ((destinationStage entry .original).apply packet) = .permit
  late : StatefulACL.Policy.evaluate pipeline.lateDefault pipeline.late .new
    ((sourceStage entry .original).apply ((destinationStage entry .original).apply packet)) = .permit

theorem process_fresh_forwarded (pipeline : Pipeline) (prepared : Prepared input) (hop : String)
    (fresh : prepared.attachment.fresh = true)
    (original : prepared.attachment.direction = .original)
    (classification : prepared.attachment.classification = .new)
    (keys : FreshKeys prepared.state prepared.attachment.entry)
    (ready : FreshForwardConditions pipeline input.packet prepared.attachment.entry hop) :
    ∃ outcome, process pipeline prepared = .ok outcome ∧
      outcome.state.records = prepared.state.records ++ [⟨prepared.attachment.entry, false⟩] ∧
      outcome.attachment = prepared.attachment ∧ outcome.disposition = .forwarded ∧
      outcome.nextHop = some hop ∧ outcome.output = some (prepared.attachment.entry.flow.output .original) := by
  have confirmed := fresh_insert_valid prepared.valid prepared.compatible keys
  have checked := (State.check_correct _).mpr confirmed
  have attached : prepared.attachment.entry.flow.input .original = input.packet := by
    have source := congrArg Prod.snd prepared.attached
    change prepared.attachment.entry.flow.input prepared.attachment.direction = input.packet at source
    simpa only [original] using source
  have target := stages_correct prepared.attachment.entry prepared.compatible .original
  rw [attached] at target
  simp only [process, original, classification, ready.route, ready.forward, ready.late,
    reduceCtorEq, ite_false, fresh, ite_true, checked, dite_true]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, congrArg some target⟩

end Netlib.Protocol.ConntrackLifecycle
