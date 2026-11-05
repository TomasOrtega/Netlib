import Std

/-!
# Outstanding work by identity

Admission allocates a fresh identity. Completion selects an actual pending item by identity.
Completion order is unrestricted. Payload equality is unnecessary.
-/

namespace Netlib.Theory.Outstanding

universe u

structure Item (α : Type u) where
  id : Nat
  value : α
  deriving Repr, BEq, DecidableEq

structure State (α : Type u) where
  nextID : Nat := 0
  pending : List (Item α) := []
  completed : List (Item α) := []
  deriving Repr, BEq, DecidableEq

def State.initial : State α := {}

def State.ids (state : State α) : List Nat := (state.completed ++ state.pending).map (·.id)

def State.Valid (state : State α) : Prop :=
  state.ids.Nodup ∧ ∀ id ∈ state.ids, id < state.nextID

def State.check (state : State α) : Bool :=
  decide state.ids.Nodup && state.ids.all (fun id => decide (id < state.nextID))

theorem State.check_correct (state : State α) : state.check = true ↔ state.Valid := by
  simp [check, Valid, List.all_eq_true]

theorem State.initial_valid : (State.initial : State α).Valid := by
  simp [Valid, ids, initial]

def newItem (before : State α) (value : α) : Item α := ⟨before.nextID, value⟩

def enqueue (before : State α) (value : α) : State α :=
  ⟨before.nextID + 1, before.pending ++ [newItem before value], before.completed⟩

inductive Error where
  | notPending
  deriving Repr, BEq, DecidableEq

def Error.describe : Error → String
  | .notPending => "The selected identity is not pending."

structure Completed (before : State α) (id : Nat) where
  state : State α
  item : Item α
  selected : item.id = id
  pendingPerm : before.pending.Perm (item :: state.pending)
  history : state.completed = before.completed ++ [item]
  nextIDeq : state.nextID = before.nextID

private structure Taken (pending : List (Item α)) (id : Nat) where
  item : Item α
  rest : List (Item α)
  selected : item.id = id
  perm : pending.Perm (item :: rest)

private def take : (pending : List (Item α)) → (id : Nat) → Except Error (Taken pending id)
  | [], _ => .error .notPending
  | head :: tail, id => do
    if same : head.id = id then
      return ⟨head, tail, same, .refl _⟩
    else
      let chosen ← take tail id
      return ⟨chosen.item, head :: chosen.rest, chosen.selected,
        (chosen.perm.cons head).trans (.swap chosen.item head chosen.rest)⟩

def complete (before : State α) (id : Nat) : Except Error (Completed before id) := do
  let chosen ← take before.pending id
  return ⟨⟨before.nextID, chosen.rest, before.completed ++ [chosen.item]⟩,
    chosen.item, chosen.selected, chosen.perm, rfl, rfl⟩



variable {α : Type u} {before : State α} {id : Nat}

theorem enqueue_valid (before : State α) (value : α) (valid : before.Valid) : (enqueue before value).Valid := by
  have expanded : (enqueue before value).ids = before.ids ++ [before.nextID] := by
    simp [State.ids, enqueue, newItem, List.append_assoc]
  constructor
  · rw [expanded]
    apply List.nodup_append.mpr
    refine ⟨valid.1, by simp, ?_⟩
    intro old member new current same
    have equal := List.mem_singleton.mp current
    have bounded := valid.2 old member
    omega
  · intro id member
    rw [expanded] at member
    rcases List.mem_append.mp member with previous | current
    · have bounded := valid.2 id previous
      change id < before.nextID + 1
      omega
    · have equal := List.mem_singleton.mp current
      change id < before.nextID + 1
      omega

theorem Completed.member (result : Completed before id) : result.item ∈ before.pending :=
  result.pendingPerm.mem_iff.mpr (by simp)

theorem Completed.allPerm (result : Completed before id) :
    (before.completed ++ before.pending).Perm (result.state.completed ++ result.state.pending) := by
  rw [result.history]
  simpa only [List.append_assoc, List.singleton_append] using
    List.Perm.append_left before.completed result.pendingPerm

theorem Completed.valid (result : Completed before id) (valid : before.Valid) : result.state.Valid := by
  have perm := List.Perm.map Item.id result.allPerm
  constructor
  · exact perm.nodup_iff.mp valid.1
  · intro key member
    rw [result.nextIDeq]
    exact valid.2 key (perm.mem_iff.mpr member)

theorem State.completed_not_pending (before : State α) (valid : before.Valid)
    (item : Item α) (completed : item ∈ before.completed) (pending : Item α) (member : pending ∈ before.pending) :
    pending.id ≠ item.id := by
  have unique := valid.1
  simp only [State.ids, List.map_append] at unique
  have disjoint := (List.nodup_append.mp unique).2.2
  intro same
  exact disjoint item.id (List.mem_map.mpr ⟨item, completed, rfl⟩) pending.id
    (List.mem_map.mpr ⟨pending, member, rfl⟩) same.symm

theorem Completed.no_pending_id (result : Completed before id) (valid : before.Valid) :
    ∀ item ∈ result.state.pending, item.id ≠ id := by
  intro item member same
  have completed : result.item ∈ result.state.completed := by rw [result.history]; simp
  exact State.completed_not_pending result.state (result.valid valid) result.item completed item member
    (same.trans result.selected.symm)

theorem complete_not_pending (before : State α) (id : Nat)
    (absent : ∀ item ∈ before.pending, item.id ≠ id) : complete before id = .error .notPending := by
  cases accepted : complete before id with
  | error error => cases error; rfl
  | ok result => exact False.elim (absent result.item result.member result.selected)

theorem Completed.no_repeat (result : Completed before id) (valid : before.Valid) :
    complete result.state id = .error .notPending :=
  complete_not_pending _ _ (result.no_pending_id valid)

private theorem take_completes (pending : List (Item α)) (item : Item α) (member : item ∈ pending) :
    ∃ result, take pending item.id = .ok result := by
  induction pending with
  | nil => simp at member
  | cons head tail ih =>
    by_cases same : head.id = item.id
    · exact ⟨_, by simp only [take, same, dite_true, pure, Except.pure]; rfl⟩
    · have inside : item ∈ tail := by
        rcases List.mem_cons.mp member with rfl | inside
        · exact False.elim (same rfl)
        · exact inside
      obtain ⟨result, accepted⟩ := ih inside
      exact ⟨_, by simp only [take, same, dite_false, accepted, bind, Except.bind, pure, Except.pure]; rfl⟩

theorem complete_completes (before : State α) (item : Item α) (member : item ∈ before.pending) :
    ∃ result, complete before item.id = .ok result := by
  obtain ⟨result, accepted⟩ := take_completes before.pending item member
  exact ⟨_, by simp only [complete, accepted, bind, Except.bind, pure, Except.pure]; rfl⟩

def count (state : State α) (property : α → Bool) : Nat :=
  state.pending.countP (fun item => property item.value)

def completedCount (state : State α) (property : α → Bool) : Nat :=
  state.completed.countP (fun item => property item.value)

theorem count_zero (state : State α) (property : α → Bool) :
    count state property = 0 ↔ ∀ item ∈ state.pending, property item.value = false := by
  simp [count, List.countP_eq_zero]

theorem enqueue_count (before : State α) (value : α) (property : α → Bool) :
    count (enqueue before value) property = count before property + if property value then 1 else 0 := by
  simp [count, enqueue, newItem, List.countP_append]

theorem Completed.count (result : Completed before id) (property : α → Bool) :
    Netlib.Theory.Outstanding.count before property = Netlib.Theory.Outstanding.count result.state property + if property result.item.value then 1 else 0 := by
  simpa only [Netlib.Theory.Outstanding.count, List.countP_cons] using
    List.Perm.countP_eq (fun item => property item.value) result.pendingPerm

theorem Completed.completed_count (result : Completed before id) (property : α → Bool) :
    completedCount result.state property = completedCount before property + if property result.item.value then 1 else 0 := by
  simp [completedCount, result.history, List.countP_append]

theorem Completed.conservation (result : Completed before id) (property : α → Bool) :
    Netlib.Theory.Outstanding.count before property + completedCount before property =
      Netlib.Theory.Outstanding.count result.state property + completedCount result.state property := by
  have perm := List.Perm.countP_eq (fun item => property item.value) result.allPerm
  simpa only [List.countP_append, Netlib.Theory.Outstanding.count, completedCount, Nat.add_comm] using perm

theorem Completed.decreases (result : Completed before id) (property : α → Bool)
    (matching : property result.item.value = true) : Netlib.Theory.Outstanding.count result.state property < Netlib.Theory.Outstanding.count before property := by
  have counted := result.count property
  simp only [matching, ite_true] at counted
  omega

inductive Trace (property : α → Bool) : State α → State α → Nat → Nat → Prop
  | nil (state : State α) : Trace property state state 0 0
  | enqueue (before : State α) (value : α) (rest : Trace property (enqueue before value) final added retired) :
      Trace property before final (added + if property value then 1 else 0) retired
  | complete {before : State α} {id : Nat} (result : Completed before id) (accepted : complete before id = .ok result)
      (rest : Trace property result.state final added retired) :
      Trace property before final added (retired + if property result.item.value then 1 else 0)

variable {property : α → Bool} {initial final : State α} {added retired : Nat}

theorem Trace.valid (trace : Trace property initial final added retired) (valid : initial.Valid) : final.Valid := by
  induction trace with
  | nil => exact valid
  | enqueue before value rest ih => exact ih (enqueue_valid before value valid)
  | complete result _ rest ih => exact ih (result.valid valid)

theorem Trace.conservation (trace : Trace property initial final added retired) :
    count final property + retired = count initial property + added := by
  induction trace with
  | nil => simp
  | enqueue before value rest ih =>
    have current := enqueue_count before value property
    omega
  | complete result _ rest ih =>
    have current := result.count property
    omega

theorem Trace.no_new (trace : Trace property initial final 0 retired) :
    count final property + retired = count initial property := by simpa using trace.conservation

theorem Trace.drained_iff (trace : Trace property initial final 0 retired) :
    count final property = 0 ↔ retired = count initial property := by
  have equation := trace.no_new
  omega

theorem Trace.drained (trace : Trace property initial final 0 retired)
    (retiredAll : count initial property ≤ retired) : ∀ item ∈ final.pending, property item.value = false := by
  have equation := trace.no_new
  apply (count_zero final property).mp
  omega

theorem Trace.history (trace : Trace property initial final added retired) :
    ∃ items : List (Item α), final.completed = initial.completed ++ items ∧
      items.countP (fun item => property item.value) = retired := by
  induction trace with
  | nil => exact ⟨[], by simp, by simp⟩
  | enqueue before value rest ih =>
    obtain ⟨items, history, counted⟩ := ih
    exact ⟨items, history, counted⟩
  | complete result accepted rest ih =>
    obtain ⟨items, history, counted⟩ := ih
    refine ⟨result.item :: items, ?_, ?_⟩
    · rw [history, result.history]
      simp
    · simp only [List.countP_cons, counted]


private theorem item_id_injective {items : List (Item α)} (unique : (items.map Item.id).Nodup)
    {left right : Item α} (leftMember : left ∈ items) (rightMember : right ∈ items)
    (same : left.id = right.id) : left = right := by
  induction items with
  | nil => simp at leftMember
  | cons head tail ih =>
    have distinct := List.nodup_cons.mp unique
    rcases List.mem_cons.mp leftMember with rfl | leftTail
    · rcases List.mem_cons.mp rightMember with rfl | rightTail
      · rfl
      · exact False.elim (distinct.1 (List.mem_map.mpr ⟨right, rightTail, same.symm⟩))
    · rcases List.mem_cons.mp rightMember with rfl | rightTail
      · exact False.elim (distinct.1 (List.mem_map.mpr ⟨left, leftTail, same⟩))
      · exact ih distinct.2 leftTail rightTail

theorem Completed.item_eq (result : Completed before id) (valid : before.Valid) (item : Item α)
    (member : item ∈ before.pending) (selected : item.id = id) : result.item = item := by
  have unique : (before.completed.map Item.id ++ before.pending.map Item.id).Nodup := by
    simpa only [State.ids, List.map_append] using valid.1
  exact item_id_injective (List.nodup_append.mp unique).2.1 result.member member
    (result.selected.trans selected.symm)

theorem complete_item (before : State α) (item : Item α) (valid : before.Valid) (member : item ∈ before.pending) :
    ∃ result, complete before item.id = .ok result ∧ result.item = item := by
  obtain ⟨result, accepted⟩ := complete_completes before item member
  exact ⟨result, accepted, result.item_eq valid item member rfl⟩

theorem drain_exists (before : State α) (property : α → Bool) (valid : before.Valid) :
    ∃ final, Trace property before final 0 (count before property) ∧ final.Valid ∧ count final property = 0 := by
  by_cases empty : count before property = 0
  · exact ⟨before, by simpa only [empty] using (Trace.nil (property := property) before), valid, empty⟩
  · have positive : 0 < count before property := Nat.pos_of_ne_zero empty
    obtain ⟨item, member, matching⟩ := List.countP_pos_iff.mp positive
    obtain ⟨result, accepted, same⟩ := complete_item before item valid member
    have selected : property result.item.value = true := by rw [same]; exact matching
    have less := result.decreases property selected
    obtain ⟨final, rest, finalValid, drained⟩ := drain_exists result.state property (result.valid valid)
    have counted := result.count property
    have total : count result.state property + 1 = count before property := by
      simpa only [selected, ite_true] using counted.symm
    refine ⟨final, ?_, finalValid, drained⟩
    simpa only [selected, ite_true, total] using Trace.complete result accepted rest
termination_by count before property


end Netlib.Theory.Outstanding
