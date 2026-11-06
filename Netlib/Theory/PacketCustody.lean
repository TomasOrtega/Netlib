import Netlib.Theory.Outstanding

/-!
# Packet custody

A new packet receives an internal identity. A copy retains its source payload and parent.
Assignment, delivery, and explicit loss each consume one pending identity.
An omitted action leaves the packet pending.
-/

namespace Netlib.Theory.PacketCustody

universe u

structure Packet (α : Type u) where
  payload : α
  parent : Option Nat := none
  deriving Repr, BEq, DecidableEq

abbrev Item (α : Type u) := Outstanding.Item (Packet α)

inductive Disposition where
  | assigned | delivered | dropped
  deriving Repr, BEq, DecidableEq

structure ResolutionRecord (α : Type u) where
  item : Item α
  disposition : Disposition
  deriving Repr, BEq, DecidableEq

structure State (α : Type u) where
  work : Outstanding.State (Packet α) := .initial
  resolutions : List (ResolutionRecord α) := []
  deriving Repr, BEq, DecidableEq

def State.initial : State α := {}
def State.nextID (state : State α) : Nat := state.work.nextID
def State.pending (state : State α) : List (Item α) := state.work.pending
def State.items (state : State α) : List (Item α) := state.work.completed ++ state.pending

def State.lookup (state : State α) (id : Nat) : Option (Item α) :=
  state.items.find? (fun item => item.id == id)

def State.pendingID (state : State α) (predicate : α → Bool) : Option Nat :=
  (state.pending.find? (fun item => predicate item.value.payload)).map (·.id)

theorem State.pendingID_exists (state : State α) (predicate : α → Bool)
    (present : ∃ item ∈ state.pending, predicate item.value.payload = true) :
    ∃ id, state.pendingID predicate = some id := by
  cases found : state.pending.find? (fun item => predicate item.value.payload) with
  | none =>
    obtain ⟨item, member, selected⟩ := present
    exact False.elim ((List.find?_eq_none.mp found) item member selected)
  | some item => exact ⟨item.id, by simp only [pendingID, found, Option.map_some]⟩

theorem State.pendingID_source (state : State α) (predicate : α → Bool) (id : Nat)
    (selected : state.pendingID predicate = some id) :
    ∃ item ∈ state.pending, item.id = id ∧ predicate item.value.payload = true := by
  obtain ⟨item, found, same⟩ := Option.map_eq_some_iff.mp selected
  exact ⟨item, List.mem_of_find?_eq_some found, same,
    List.find?_some (p := fun item : Item α => predicate item.value.payload) found⟩

def State.Lineage (state : State α) : Prop :=
  ∀ item ∈ state.items, ∀ parent, item.value.parent = some parent →
    ∃ source ∈ state.items, source.id = parent ∧ source.id < item.id ∧
      source.value.payload = item.value.payload

def State.Valid (state : State α) : Prop :=
  state.work.Valid ∧ state.resolutions.map (·.item) = state.work.completed ∧ state.Lineage

def State.Payloads (state : State α) (property : α → Prop) : Prop :=
  ∀ item ∈ state.items, property item.value.payload

@[simp] theorem State.initial_valid : (State.initial : State α).Valid := by
  exact ⟨Outstanding.State.initial_valid, rfl, by simp [Lineage, items, pending, initial, Outstanding.State.initial]⟩

def newItem (before : State α) (payload : α) : Item α :=
  Outstanding.newItem before.work ⟨payload, none⟩

def mint (before : State α) (payload : α) : State α :=
  { before with work := Outstanding.enqueue before.work ⟨payload, none⟩ }

@[simp] theorem mint_nextID (before : State α) (payload : α) :
    (mint before payload).nextID = before.nextID + 1 := rfl

@[simp] theorem mint_pending (before : State α) (payload : α) :
    (mint before payload).pending = before.pending ++ [newItem before payload] := rfl

@[simp] theorem mint_items (before : State α) (payload : α) :
    (mint before payload).items = before.items ++ [newItem before payload] := by
  simp [mint, State.items, State.pending, newItem, Outstanding.enqueue, List.append_assoc]

@[simp] theorem newItem_id (before : State α) (payload : α) :
    (newItem before payload).id = before.nextID := rfl

@[simp] theorem newItem_payload (before : State α) (payload : α) :
    (newItem before payload).value.payload = payload := rfl

@[simp] theorem newItem_parent (before : State α) (payload : α) :
    (newItem before payload).value.parent = none := rfl

theorem mint_valid (before : State α) (payload : α) (valid : before.Valid) :
    (mint before payload).Valid := by
  refine ⟨Outstanding.enqueue_valid _ _ valid.1, valid.2.1, ?_⟩
  intro item member parent copied
  rw [mint_items] at member
  rcases List.mem_append.mp member with old | fresh
  · obtain ⟨source, sourceMember, selected, earlier, same⟩ := valid.2.2 item old parent copied
    exact ⟨source, by rw [mint_items]; exact List.mem_append_left _ sourceMember, selected, earlier, same⟩
  · have same := List.mem_singleton.mp fresh
    subst item
    simp at copied

theorem mint_payloads (before : State α) (payload : α) (property : α → Prop)
    (prior : before.Payloads property) (current : property payload) : (mint before payload).Payloads property := by
  intro item member
  rw [mint_items] at member
  rcases List.mem_append.mp member with old | fresh
  · exact prior item old
  · have same := List.mem_singleton.mp fresh
    simpa only [same, newItem_payload] using current

inductive Error where
  | notFound | notPending
  deriving Repr, BEq, DecidableEq

def Error.describe : Error → String
  | .notFound => "The packet source does not exist."
  | .notPending => "The packet identity is not pending."

variable {α : Type u} {before : State α} {parent id : Nat} {disposition : Disposition}

structure Copied (before : State α) (parent : Nat) where
  source : Item α
  member : source ∈ before.items
  selected : source.id = parent

def Copied.item (result : Copied before parent) : Item α :=
  Outstanding.newItem before.work ⟨result.source.value.payload, some parent⟩

def Copied.state (result : Copied before parent) : State α :=
  { before with work := Outstanding.enqueue before.work ⟨result.source.value.payload, some parent⟩ }

def copy (before : State α) (parent : Nat) : Except Error (Copied before parent) :=
  match found : before.lookup parent with
  | none => .error .notFound
  | some source => .ok ⟨source, List.mem_of_find?_eq_some found,
      beq_iff_eq.mp (List.find?_some (p := fun item : Item α => item.id == parent) found)⟩

@[simp] theorem Copied.fresh_id (result : Copied before parent) : result.item.id = before.nextID := rfl
@[simp] theorem Copied.payload (result : Copied before parent) :
    result.item.value.payload = result.source.value.payload := rfl
@[simp] theorem Copied.parent_eq (result : Copied before parent) : result.item.value.parent = some parent := rfl
@[simp] theorem Copied.nextID (result : Copied before parent) : result.state.nextID = before.nextID + 1 := rfl
@[simp] theorem Copied.pending (result : Copied before parent) :
    result.state.pending = before.pending ++ [result.item] := rfl
@[simp] theorem Copied.items (result : Copied before parent) :
    result.state.items = before.items ++ [result.item] := by
  simp [state, State.items, State.pending, item, Outstanding.enqueue, List.append_assoc]

theorem Copied.earlier (result : Copied before parent) (valid : before.Valid) :
    parent < result.item.id := by
  have bounded := valid.1.2 result.source.id (List.mem_map.mpr ⟨result.source, result.member, rfl⟩)
  simpa only [result.selected, Copied.fresh_id, State.nextID] using bounded

theorem Copied.valid (result : Copied before parent) (valid : before.Valid) : result.state.Valid := by
  refine ⟨Outstanding.enqueue_valid _ _ valid.1, valid.2.1, ?_⟩
  intro item member parentID copied
  rw [result.items] at member
  rcases List.mem_append.mp member with old | fresh
  · obtain ⟨source, sourceMember, selected, earlier, same⟩ := valid.2.2 item old parentID copied
    exact ⟨source, by rw [result.items]; exact List.mem_append_left _ sourceMember, selected, earlier, same⟩
  · have same := List.mem_singleton.mp fresh
    subst item
    have selected : parent = parentID := Option.some.inj copied
    subst parentID
    exact ⟨result.source, by rw [result.items]; exact List.mem_append_left _ result.member,
      result.selected, by rw [result.selected]; exact result.earlier valid, rfl⟩

theorem Copied.payloads (result : Copied before parent) (property : α → Prop)
    (prior : before.Payloads property) : result.state.Payloads property := by
  intro item member
  rw [result.items] at member
  rcases List.mem_append.mp member with old | fresh
  · exact prior item old
  · have same := List.mem_singleton.mp fresh
    simpa only [same, result.payload] using prior result.source result.member

theorem copy_exists (before : State α) (source : Item α) (member : source ∈ before.items) :
    ∃ result, copy before source.id = .ok result := by
  unfold copy
  split
  · rename_i found
    have absent := List.find?_eq_none.mp found source member
    simp at absent
  · exact ⟨_, rfl⟩

theorem copy_not_found (before : State α) (parent : Nat)
    (absent : ∀ item ∈ before.items, item.id ≠ parent) : copy before parent = .error .notFound := by
  have missing : before.lookup parent = none := by
    apply List.find?_eq_none.mpr
    intro item member
    intro same
    exact absent item member (beq_iff_eq.mp same)
  unfold copy
  split
  · rfl
  · rename_i source found
    rw [missing] at found
    contradiction

theorem State.root (state : State α) (valid : state.Valid) (item : Item α) (member : item ∈ state.items) :
    ∃ source ∈ state.items, source.value.parent = none ∧ source.value.payload = item.value.payload := by
  generalize position : item.id = n
  induction n using Nat.strongRecOn generalizing item with
  | ind n ih =>
    cases parentEq : item.value.parent with
    | none => exact ⟨item, member, parentEq, rfl⟩
    | some parentID =>
      obtain ⟨parentItem, parentMember, selected, earlier, same⟩ := valid.2.2 item member parentID parentEq
      obtain ⟨source, sourceMember, original, payload⟩ := ih parentItem.id (by omega) parentItem parentMember rfl
      exact ⟨source, sourceMember, original, payload.trans same⟩

structure Resolved (before : State α) (id : Nat) (disposition : Disposition) where
  completed : Outstanding.Completed before.work id

def Resolved.item (result : Resolved before id disposition) : Item α := result.completed.item

def Resolved.state (result : Resolved before id disposition) : State α :=
  ⟨result.completed.state, before.resolutions ++ [⟨result.item, disposition⟩]⟩

def resolve (before : State α) (id : Nat) (disposition : Disposition) : Except Error (Resolved before id disposition) := do
  let completed ← (Outstanding.complete before.work id).mapError (fun _ => Error.notPending)
  return ⟨completed⟩

theorem Resolved.member (result : Resolved before id disposition) : result.item ∈ before.pending :=
  result.completed.member

theorem Resolved.selected (result : Resolved before id disposition) : result.item.id = id :=
  result.completed.selected

theorem Resolved.items_perm (result : Resolved before id disposition) :
    before.items.Perm result.state.items := result.completed.allPerm

@[simp] theorem Resolved.nextID (result : Resolved before id disposition) :
    result.state.nextID = before.nextID := result.completed.nextIDeq

@[simp] theorem Resolved.history (result : Resolved before id disposition) :
    result.state.resolutions = before.resolutions ++ [⟨result.item, disposition⟩] := rfl

theorem Resolved.valid (result : Resolved before id disposition) (valid : before.Valid) : result.state.Valid := by
  refine ⟨result.completed.valid valid.1, ?_, ?_⟩
  · simp only [result.history, List.map_append, List.map_cons, List.map_nil, valid.2.1]
    exact result.completed.history.symm
  · intro item member parent copied
    obtain ⟨source, sourceMember, selected, earlier, same⟩ := valid.2.2 item (result.items_perm.mem_iff.mpr member) parent copied
    exact ⟨source, result.items_perm.mem_iff.mp sourceMember, selected, earlier, same⟩

theorem Resolved.payloads (result : Resolved before id disposition) (property : α → Prop)
    (prior : before.Payloads property) : result.state.Payloads property := by
  intro item member
  exact prior item (result.items_perm.mem_iff.mpr member)

theorem resolve_not_pending (before : State α) (id : Nat) (disposition : Disposition)
    (absent : ∀ item ∈ before.pending, item.id ≠ id) : resolve before id disposition = .error .notPending := by
  simp only [resolve, Outstanding.complete_not_pending before.work id absent]
  rfl

theorem Resolved.no_repeat (result : Resolved before id disposition) (valid : before.Valid)
    (next : Disposition) : resolve result.state id next = .error .notPending :=
  resolve_not_pending _ _ _ (result.completed.no_pending_id valid.1)

theorem resolve_completes (before : State α) (item : Item α) (member : item ∈ before.pending) (disposition : Disposition) :
    ∃ result, resolve before item.id disposition = .ok result := by
  obtain ⟨completed, computed⟩ := Outstanding.complete_completes before.work item member
  exact ⟨⟨completed⟩, by simp only [resolve, computed]; rfl⟩

theorem Resolved.item_eq (result : Resolved before id disposition) (valid : before.Valid)
    (item : Item α) (member : item ∈ before.pending) (selected : item.id = id) : result.item = item :=
  result.completed.item_eq valid.1 item member selected

def State.count (state : State α) (disposition : Disposition) : Nat :=
  state.resolutions.countP (fun entry => decide (entry.disposition = disposition))

def State.dropped (state : State α) : Nat := state.count .dropped

@[simp] theorem mint_count (before : State α) (payload : α) (disposition : Disposition) :
    (mint before payload).count disposition = before.count disposition := rfl

@[simp] theorem Copied.count (result : Copied before parent) (disposition : Disposition) :
    result.state.count disposition = before.count disposition := rfl

theorem Resolved.count (result : Resolved before id disposition) (selected : Disposition) :
    result.state.count selected = before.count selected + if disposition = selected then 1 else 0 := by
  simp [State.count, List.countP_append, Resolved.state]

theorem Resolved.pending_length (result : Resolved before id disposition) :
    before.pending.length = result.state.pending.length + 1 := by
  have length := result.completed.pendingPerm.length_eq
  simpa only [List.length_cons, State.pending, Resolved.state] using length

theorem Resolved.conservation (result : Resolved before id disposition) :
    before.pending.length + before.resolutions.length =
      result.state.pending.length + result.state.resolutions.length := by
  have retired := result.pending_length
  simp only [result.history, List.length_append, List.length_cons, List.length_nil]
  omega

theorem Resolved.dropped_of_drop (result : Resolved before id .dropped) :
    result.state.dropped = before.dropped + 1 := by
  exact result.count .dropped

theorem Resolved.dropped_of_other (result : Resolved before id disposition)
    (notDrop : disposition ≠ .dropped) : result.state.dropped = before.dropped := by
  simpa only [State.dropped, notDrop, ite_false, Nat.add_zero] using result.count .dropped

inductive History : State α → Prop
  | initial : History .initial
  | mint {before : State α} (prior : History before) (payload : α) : History (PacketCustody.mint before payload)
  | copy {before : State α} {parent : Nat} (prior : History before) (result : Copied before parent)
      (computed : PacketCustody.copy before parent = .ok result) : History result.state
  | resolve {before : State α} {id : Nat} {disposition : Disposition} (prior : History before) (result : Resolved before id disposition)
      (computed : PacketCustody.resolve before id disposition = .ok result) : History result.state

theorem History.valid (history : History state) : state.Valid := by
  induction history with
  | initial => exact State.initial_valid
  | mint prior payload ih => exact mint_valid _ _ ih
  | copy prior result computed ih => exact result.valid ih
  | resolve prior result computed ih => exact result.valid ih

theorem History.accounted (history : History state) :
    state.pending.length + state.resolutions.length = state.nextID := by
  induction history with
  | initial => rfl
  | @mint before prior payload ih =>
    simp only [mint_pending, List.length_append, List.length_cons, List.length_nil, mint_nextID]
    change before.pending.length + 1 + before.resolutions.length = before.nextID + 1
    omega
  | @copy before parent prior result computed ih =>
    rw [result.pending, result.nextID]
    simp only [List.length_append, List.length_cons, List.length_nil]
    change before.pending.length + 1 + before.resolutions.length = before.nextID + 1
    omega
  | resolve prior result computed ih =>
    rw [← result.conservation, result.nextID]
    exact ih

theorem History.root (history : History state) (item : Item α) (member : item ∈ state.items) :
    ∃ source ∈ state.items, source.value.parent = none ∧ source.value.payload = item.value.payload :=
  state.root history.valid item member

theorem State.resolution_total (state : State α) :
    state.count .assigned + state.count .delivered + state.dropped = state.resolutions.length := by
  simp only [State.dropped, State.count]
  induction state.resolutions with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.countP_cons, List.length_cons]
    cases head.disposition <;> simp_all <;> omega

theorem History.loss_bound (history : History state) :
    state.dropped ≤ state.nextID := by
  have accounted := history.accounted
  have total := state.resolution_total
  omega

end Netlib.Theory.PacketCustody
