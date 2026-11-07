import Netlib.Theory.PacketCustody

/-!
# Pending packet frontiers

A payload predicate selects actual pending custody items.
Mint, copy, and resolution account for each selected identity.
-/

namespace Netlib.Theory.PacketCustody

universe u

variable {α : Type u} {before : State α} {id : Nat} {disposition : Disposition}

def State.frontier (state : State α) (property : α → Bool) : List (Item α) :=
  state.pending.filter (fun item => property item.value.payload)

def State.frontierCount (state : State α) (property : α → Bool) : Nat :=
  Outstanding.count state.work (fun packet => property packet.payload)

theorem State.frontier_member (state : State α) (property : α → Bool) (item : Item α) :
    item ∈ state.frontier property ↔ item ∈ state.pending ∧ property item.value.payload = true := by
  simp only [frontier, List.mem_filter]

theorem State.frontierCount_length (state : State α) (property : α → Bool) :
    state.frontierCount property = (state.frontier property).length := by
  exact List.countP_eq_length_filter

theorem State.frontierCount_le_pending (state : State α) (property : α → Bool) :
    state.frontierCount property ≤ state.pending.length := by
  rw [state.frontierCount_length]
  exact List.length_filter_le _ _

theorem State.frontierCount_zero (state : State α) (property : α → Bool) :
    state.frontierCount property = 0 ↔ ∀ item ∈ state.pending, property item.value.payload = false :=
  Outstanding.count_zero state.work (fun packet => property packet.payload)

theorem State.frontier_empty (state : State α) (property : α → Bool) :
    state.frontier property = [] ↔ state.frontierCount property = 0 := by
  rw [state.frontierCount_length]
  exact List.length_eq_zero_iff.symm

theorem mint_frontierCount (before : State α) (payload : α) (property : α → Bool) :
    (mint before payload).frontierCount property =
      before.frontierCount property + if property payload then 1 else 0 :=
  Outstanding.enqueue_count before.work ⟨payload, none⟩ (fun packet => property packet.payload)

theorem mint_frontier (before : State α) (payload : α) (property : α → Bool)
    (outside : property payload = false) :
    (mint before payload).frontier property = before.frontier property := by
  simp only [State.frontier, mint_pending, List.filter_append, List.filter_cons, newItem_payload, outside,
    Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil]

theorem Copied.frontierCount (result : Copied before id) (property : α → Bool) :
    result.state.frontierCount property =
      before.frontierCount property + if property result.source.value.payload then 1 else 0 := by
  change result.state.pending.countP (fun item => property item.value.payload) =
    before.pending.countP (fun item => property item.value.payload) +
      if property result.source.value.payload then 1 else 0
  simp only [result.pending,
    List.countP_append, List.countP_cons, List.countP_nil, result.payload, Nat.zero_add]
  rfl

theorem Resolved.frontierCount (result : Resolved before id disposition) (property : α → Bool) :
    before.frontierCount property = result.state.frontierCount property +
      if property result.item.value.payload then 1 else 0 :=
  result.completed.count (fun packet => property packet.payload)

theorem Resolved.frontierCount_le (result : Resolved before id disposition) (property : α → Bool) :
    result.state.frontierCount property ≤ before.frontierCount property := by
  have counted := result.frontierCount property
  omega

theorem Resolved.frontierCount_strict (result : Resolved before id disposition) (property : α → Bool)
    (selected : property result.item.value.payload = true) :
    result.state.frontierCount property < before.frontierCount property := by
  have counted := result.frontierCount property
  simp only [selected, ite_true] at counted
  omega

theorem Resolved.frontier_member_before (result : Resolved before id disposition) (property : α → Bool)
    (item : Item α) (member : item ∈ result.state.frontier property) :
    item ∈ before.frontier property := by
  obtain ⟨pending, matching⟩ := (result.state.frontier_member property item).mp member
  exact (before.frontier_member property item).mpr
    ⟨result.completed.pendingPerm.mem_iff.mpr (List.mem_cons_of_mem _ pending), matching⟩

theorem Resolved.pending (result : Resolved before id disposition)
    (computed : resolve before id disposition = .ok result) :
    result.state.pending = before.pending.eraseP (fun item => item.id == id) := by
  have completed : Outstanding.complete before.work id = .ok result.completed := by
    unfold resolve at computed
    cases selected : Outstanding.complete before.work id with
    | error reason => simp [selected, Except.mapError, bind, Except.bind] at computed
    | ok value =>
      simp only [selected, Except.mapError, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at computed
      cases computed
      rfl
  exact Outstanding.complete_pending before.work id result.completed completed

theorem Resolved.frontier_sublist (result : Resolved before id disposition)
    (computed : resolve before id disposition = .ok result) (property : α → Bool) :
    (result.state.frontier property).Sublist (before.frontier property) := by
  unfold State.frontier
  rw [result.pending computed]
  exact List.Sublist.filter _ List.eraseP_sublist

theorem Resolved.frontier_eq_of_count_eq (result : Resolved before id disposition)
    (computed : resolve before id disposition = .ok result) (property : α → Bool)
    (equal : result.state.frontierCount property = before.frontierCount property) :
    result.state.frontier property = before.frontier property := by
  apply (result.frontier_sublist computed property).eq_of_length
  simpa only [State.frontierCount_length] using equal

theorem State.frontier_head (state : State α) (property : α → Bool) (item : Item α)
    (selected : (state.frontier property).head? = some item) :
    state.pendingID property = some item.id := by
  have found : state.pending.find? (fun item => property item.value.payload) = some item := by
    simpa only [State.frontier, List.head?_filter] using selected
  simp only [State.pendingID, found, Option.map_some]

private theorem find_subpredicate (items : List β) (major minor : β → Bool)
    (contained : ∀ item, minor item = true → major item = true)
    (item : β) (selected : items.find? major = some item) (matching : minor item = true) :
    items.find? minor = some item := by
  induction items with
  | nil => simp at selected
  | cons head tail ih =>
    cases majorHead : major head with
    | false =>
      have minorHead : minor head = false := by
        cases found : minor head with
        | false => rfl
        | true => have impossible := contained head found; simp only [majorHead, Bool.false_eq_true] at impossible
      simp only [List.find?_cons, majorHead] at selected
      simpa only [List.find?_cons, minorHead, Bool.false_eq_true, ↓reduceIte] using ih selected
    | true =>
      have same : head = item := by
        simpa only [List.find?_cons, majorHead, ↓reduceIte, Option.some.injEq] using selected
      subst head
      simp only [List.find?_cons, matching]

theorem State.frontier_head_subpredicate (state : State α) (major minor : α → Bool)
    (contained : ∀ payload, minor payload = true → major payload = true)
    (item : Item α) (selected : (state.frontier major).head? = some item)
    (matching : minor item.value.payload = true) : state.pendingID minor = some item.id := by
  have found : state.pending.find? (fun item => major item.value.payload) = some item := by
    simpa only [State.frontier, List.head?_filter] using selected
  have smaller := find_subpredicate state.pending (fun item => major item.value.payload)
    (fun item => minor item.value.payload) (fun item => contained item.value.payload) item found matching
  simp only [State.pendingID, smaller, Option.map_some]

end Netlib.Theory.PacketCustody
