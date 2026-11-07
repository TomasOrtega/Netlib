import Netlib.Theory.PacketCustody

/-!
# Dropped packet identities from the existing custody history

The projection adds no state. Valid custody resolves each identity once,
so its dropped identities are distinct.
-/

namespace Netlib.Theory.PacketCustody

universe u
variable {α : Type u} {before : State α} {id parent : Nat} {disposition : Disposition}

def State.droppedIDs (state : State α) : List Nat :=
  (state.resolutions.filter (fun record => decide (record.disposition = .dropped))).map (·.item.id)

theorem State.resolutionIDs_nodup (state : State α) (valid : state.Valid) :
    (state.resolutions.map (·.item.id)).Nodup := by
  have allIDs : (state.work.completed.map (·.id) ++ state.work.pending.map (·.id)).Nodup := by
    simpa only [Outstanding.State.ids, List.map_append] using valid.1.1
  have completed := (List.nodup_append.mp allIDs).1
  rw [← valid.2.1, List.map_map] at completed
  exact completed

theorem State.droppedIDs_nodup (state : State α) (valid : state.Valid) : state.droppedIDs.Nodup :=
  (List.filter_sublist.map (fun record : ResolutionRecord α => record.item.id)).nodup
    (state.resolutionIDs_nodup valid)

theorem State.droppedIDs_length (state : State α) : state.droppedIDs.length = state.dropped := by
  simp only [droppedIDs, List.length_map, State.dropped, State.count, List.countP_eq_length_filter]

@[simp] theorem mint_droppedIDs (before : State α) (payload : α) :
    (mint before payload).droppedIDs = before.droppedIDs := rfl

@[simp] theorem Copied.droppedIDs (result : Copied before parent) :
    result.state.droppedIDs = before.droppedIDs := rfl

theorem Resolved.droppedIDs (result : Resolved before id disposition) :
    result.state.droppedIDs = before.droppedIDs ++ if disposition = .dropped then [id] else [] := by
  cases disposition <;> simp [State.droppedIDs, result.selected]

theorem History.droppedIDs_nodup (history : History state) : state.droppedIDs.Nodup :=
  state.droppedIDs_nodup history.valid

end Netlib.Theory.PacketCustody
