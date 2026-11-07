import Netlib.Theory.FiniteProgressRank

/-!
# Complete sparse successor graphs

Discovery admits reachable keys under explicit budgets. A result requires
every discovered row and target; exhausting a budget never returns a prefix.
-/

namespace Netlib.Theory.FiniteSuccessorGraph

universe u w

namespace R
export FiniteProgressRank (Edge Table Event Limits edgeCount)
end R

export FiniteProgressRank (Limits)

structure Model (Key : Type u) (Move : Type u) where
  initial : Key
  successors : Key → List (Move × Key)
  terminal : Key → Bool

def Model.network (model : Model Key Move) : Network Key :=
  ⟨fun source target => ∃ move, (move, target) ∈ model.successors source⟩

def Model.system (model : Model Key Move) : Protocol.Transition Key (R.Event Move) where
  step before event after := match event with
    | .idle => after = before
    | .progress move => (move, after) ∈ model.successors before

structure Costs where
  row : Nat
  key : Nat
  deriving Repr

/-- A structural work estimate, not a processor-time bound. -/
def workEstimate (costs : Costs) (states edges : Nat) : Nat :=
  2 * (states + 1) * (costs.row + 1) +
    4 * (states + 1) * (states + edges + 1) * (costs.key + 1)

def preflight (costs : Costs) (limits : R.Limits) (states edges : Nat) : Except String PUnit.{w + 1} := do
  if states > limits.states then throw s!"Sparse states {states} exceed budget {limits.states}."
  if edges > limits.edges then throw s!"Sparse successors {edges} exceed budget {limits.edges}."
  if workEstimate costs states edges > limits.work then
    throw s!"Sparse work estimate {workEstimate costs states edges} exceeds budget {limits.work}."

private theorem preflight_sound (costs : Costs) (limits : R.Limits) (states edges : Nat)
    (checked : preflight costs limits states edges = .ok ()) :
    states ≤ limits.states ∧ edges ≤ limits.edges ∧ workEstimate costs states edges ≤ limits.work := by
  unfold preflight at checked
  repeat' first
    | (split at checked)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at checked)
    | (solve | cases checked)
    | (solve | omega)

variable {Key : Type u} {Move : Type u} [DecidableEq Key]

def findIndex (keys : Vector Key size) (key : Key) : Option (Fin size) :=
  (List.finRange size).find? (fun index => decide (keys.get index = key))

theorem findIndex_sound (keys : Vector Key size) (key : Key) (index : Fin size)
    (found : findIndex keys key = some index) : keys.get index = key :=
  of_decide_eq_true (List.find?_some (p := fun index : Fin size => decide (keys.get index = key)) found)

theorem findIndex_exists (keys : Vector Key size) (key : Key) (member : key ∈ keys.toList) :
    ∃ index, findIndex keys key = some index := by
  obtain ⟨position, within, selected⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp member)
  let index : Fin size := ⟨position, within⟩
  have equal : keys.get index = key := selected
  cases found : findIndex keys key with
  | some index => exact ⟨index, rfl⟩
  | none =>
    exact False.elim ((List.find?_eq_none.mp found index (List.mem_finRange index)) (decide_eq_true equal))

private structure Draft (model : Model Key Move) where
  keys : List Key
  todo : List Key
  rows : List (Key × List (Move × Key))
  keyCount : Nat
  keyCountEq : keyCount = keys.length
  edgeCount : Nat
  edgeCountEq : edgeCount = (rows.map (fun row => row.2.length)).sum
  keySound : ∀ key ∈ keys, model.network.Reachable model.initial key
  todoSound : ∀ key ∈ todo, model.network.Reachable model.initial key

private def Draft.edges {model : Model Key Move} (draft : Draft model) : Nat := draft.edgeCount

omit [DecidableEq Key] in
private theorem Draft.edges_eq {model : Model Key Move} (draft : Draft model) : draft.edges = (draft.rows.map (fun row => row.2.length)).sum :=
  draft.edgeCountEq

private def admitTargets (model : Model Key Move) (costs : Costs) (limits : R.Limits)
    (source : Key) (reached : model.network.Reachable model.initial source) (edges : Nat) :
    (targets : List (Move × Key)) → (∀ target ∈ targets, target ∈ model.successors source) →
    Draft model → Except String (Draft model)
  | [], _, draft => return draft
  | (move, target) :: rest, present, draft => do
    let next ← if target ∈ draft.keys then pure draft else do
      preflight costs limits (draft.keyCount + 1) edges
      let path := reached.trans (.single ⟨move, present (move, target) (by simp)⟩)
      pure { draft with
        keys := draft.keys ++ [target]
        todo := draft.todo ++ [target]
        keyCount := draft.keyCount + 1
        keyCountEq := by simp only [List.length_append, List.length_singleton, draft.keyCountEq]
        keySound := by
          intro key member
          rcases List.mem_append.mp member with old | added
          · exact draft.keySound key old
          · have same : key = target := List.mem_singleton.mp added
            simpa only [same] using path
        todoSound := by
          intro key member
          rcases List.mem_append.mp member with old | added
          · exact draft.todoSound key old
          · have same : key = target := List.mem_singleton.mp added
            simpa only [same] using path }
    admitTargets model costs limits source reached edges rest
      (fun target member => present target (List.mem_cons_of_mem _ member)) next

private def expand (model : Model Key Move) (costs : Costs) (limits : R.Limits) :
    Nat → Draft model → Except String (Draft model)
  | 0, draft =>
    if draft.todo.isEmpty then return draft
    else throw "Sparse discovery exhausted its state budget before closing every successor row."
  | fuel + 1, draft => do
    match pending : draft.todo with
    | [] => return draft
    | source :: rest =>
      preflight costs limits draft.keyCount draft.edges
      let successors := model.successors source
      let edges := draft.edges + successors.length
      preflight costs limits draft.keyCount edges
      let reached := draft.todoSound source (by rw [pending]; simp)
      let popped : Draft model := {
        draft with
        todo := rest
        todoSound := by
          intro key member
          exact draft.todoSound key (by rw [pending]; exact List.mem_cons_of_mem _ member) }
      let next ← admitTargets model costs limits source reached edges successors (fun _ member => member) popped
      expand model costs limits fuel {
        next with
        rows := next.rows ++ [(source, successors)]
        edgeCount := next.edgeCount + successors.length
        edgeCountEq := by
          simp only [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton, next.edgeCountEq] }

private def encodeRow (keys : Vector Key size) : List (Move × Key) → Except String (List (R.Edge Move size))
  | [] => return []
  | (move, target) :: rest => do
    let some index := findIndex keys target | throw "A discovered successor has no admitted target index."
    return ⟨move, index⟩ :: (← encodeRow keys rest)

structure Indexed (model : Model Key Move) where
  size : Nat
  keys : Vector Key size
  keysNodup : keys.toList.Nodup
  table : R.Table Move size
  initialEq : keys.get table.initial = model.initial
  rowsExact : ∀ index, (table.row index).map (fun edge => (edge.move, keys.get edge.target)) = model.successors (keys.get index)
  doneEq : ∀ index, table.done index = model.terminal (keys.get index)
  keySound : ∀ index, model.network.Reachable model.initial (keys.get index)
  costs : Costs
  limits : R.Limits
  stateBound : size ≤ limits.states
  edgeBound : R.edgeCount table ≤ limits.edges
  workBound : workEstimate costs size (R.edgeCount table) ≤ limits.work

private def exactRows [DecidableEq Move] (model : Model Key Move) (keys : Vector Key size) (table : R.Table Move size) : Bool :=
  decide keys.toList.Nodup && decide (keys.get table.initial = model.initial) &&
    (List.finRange size).all (fun index =>
      decide ((table.row index).map (fun edge => (edge.move, keys.get edge.target)) = model.successors (keys.get index)) &&
      decide (table.done index = model.terminal (keys.get index)))

private def validate [DecidableEq Move] (model : Model Key Move) (costs : Costs) (limits : R.Limits)
    (keys : Vector Key size) (table : R.Table Move size)
    (sound : ∀ index, model.network.Reachable model.initial (keys.get index)) : Except String (Indexed model) := do
  match bounded : preflight costs limits size (R.edgeCount table) with
  | .error reason => throw reason
  | .ok () =>
    if checked : exactRows model keys table = true then
      have facts : (keys.toList.Nodup ∧ keys.get table.initial = model.initial) ∧
          ∀ index ∈ List.finRange size,
            (table.row index).map (fun edge => (edge.move, keys.get edge.target)) = model.successors (keys.get index) ∧
              table.done index = model.terminal (keys.get index) := by
        simpa only [exactRows, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] using checked
      let bounds := preflight_sound costs limits size (R.edgeCount table) bounded
      return ⟨size, keys, facts.1.1, table, facts.1.2,
        fun index => (facts.2 index (List.mem_finRange index)).1,
        fun index => (facts.2 index (List.mem_finRange index)).2, sound, costs, limits,
        bounds.1, bounds.2.1, bounds.2.2⟩
    else throw "The sparse indexed rows differ from the complete model successor rows."

def build [DecidableEq Move] (model : Model Key Move) (costs : Costs) (limits : R.Limits) : Except String (Indexed model) := do
  preflight costs limits 1 0
  let initial : Draft model := ⟨[model.initial], [model.initial], [], 1, rfl, 0, rfl,
    by intro key member; have same := List.mem_singleton.mp member; simpa only [same] using Network.Reachable.refl model.initial,
    by intro key member; have same := List.mem_singleton.mp member; simpa only [same] using Network.Reachable.refl model.initial⟩
  let draft ← expand model costs limits limits.states initial
  let keys := draft.keys.toArray.toVector
  have keysList : keys.toList = draft.keys := by simp [keys]
  let some first := findIndex keys model.initial | throw "The sparse initial key is absent."
  let rows ← Vector.ofFnM fun index => do
    let some cached := draft.rows.find? (fun row => decide (row.1 = keys.get index))
      | throw "A discovered key has no complete successor row."
    encodeRow keys cached.2
  let table : R.Table Move keys.size := ⟨first, rows, Vector.ofFn (fun index => model.terminal (keys.get index))⟩
  validate model costs limits keys table (by
    intro index
    apply draft.keySound
    exact Eq.mp (congrArg (fun entries : List Key => keys.get index ∈ entries) keysList)
      (Vector.mem_toList_iff.mpr (Vector.mem_of_getElem rfl)))

variable {model : Model Key Move}

def Indexed.work (value : Indexed model) : Nat := workEstimate value.costs value.size (R.edgeCount value.table)

omit [DecidableEq Key] in
theorem Indexed.key_injective (value : Indexed model) (first second : Fin value.size)
    (same : value.keys.get first = value.keys.get second) : first = second := by
  change value.keys[first.val] = value.keys[second.val] at same
  apply Fin.ext
  apply value.keysNodup.eq_of_getElem_eq
    (by simpa only [Vector.length_toList] using first.isLt)
    (by simpa only [Vector.length_toList] using second.isLt)
  simpa only [Vector.getElem_toList] using same

omit [DecidableEq Key] in
theorem Indexed.key_mem (value : Indexed model) (index : Fin value.size) : value.keys.get index ∈ value.keys.toList :=
  Vector.mem_toList_iff.mpr (Vector.mem_of_getElem rfl)

omit [DecidableEq Key] in
theorem Indexed.initial_mem (value : Indexed model) : model.initial ∈ value.keys.toList := by
  rw [← value.initialEq]
  exact value.key_mem _

theorem Indexed.closed (value : Indexed model) (source : Key) (member : source ∈ value.keys.toList)
    (move : Move) (target : Key) (edge : (move, target) ∈ model.successors source) : target ∈ value.keys.toList := by
  obtain ⟨index, selected⟩ := findIndex_exists value.keys source member
  have sourceEq := findIndex_sound value.keys source index selected
  rw [← sourceEq, ← value.rowsExact index] at edge
  obtain ⟨actual, _, same⟩ := List.mem_map.mp edge
  rw [← (Prod.mk.inj same).2]
  exact value.key_mem _

theorem Indexed.keys_complete (value : Indexed model) (key : Key)
    (path : model.network.Reachable model.initial key) : key ∈ value.keys.toList := by
  have preserve : ∀ {source target}, model.network.Reachable source target → source ∈ value.keys.toList → target ∈ value.keys.toList := by
    intro source target reachable
    induction reachable with
    | refl => exact id
    | step edge _ ih =>
      intro member
      obtain ⟨move, present⟩ := edge
      exact ih (value.closed _ member move _ present)
  exact preserve path value.initial_mem

theorem Indexed.keys_exact (value : Indexed model) (key : Key) :
    key ∈ value.keys.toList ↔ model.network.Reachable model.initial key := by
  constructor
  · intro member
    obtain ⟨index, found⟩ := findIndex_exists value.keys key member
    rw [← findIndex_sound value.keys key index found]
    exact value.keySound index
  · exact value.keys_complete key

def Indexed.index (value : Indexed model) (key : Key) (reached : model.network.Reachable model.initial key) : Fin value.size :=
  (findIndex value.keys key).get (by
    obtain ⟨index, found⟩ := findIndex_exists value.keys key (value.keys_complete key reached)
    simp only [found, Option.isSome_some])

theorem Indexed.get_index (value : Indexed model) (key : Key) (reached : model.network.Reachable model.initial key) :
    value.keys.get (value.index key reached) = key := by
  obtain ⟨index, found⟩ := findIndex_exists value.keys key (value.keys_complete key reached)
  have same := findIndex_sound value.keys key index found
  simpa only [Indexed.index, found, Option.get_some] using same

theorem Indexed.index_key (value : Indexed model) (index : Fin value.size) :
    value.index (value.keys.get index) (value.keySound index) = index :=
  value.key_injective _ _ (value.get_index _ _)

theorem Indexed.index_initial (value : Indexed model) :
    value.index model.initial (.refl _) = value.table.initial := by
  apply value.key_injective
  rw [value.get_index, value.initialEq]

def Indexed.pending (value : Indexed model) (key : Key) (reached : model.network.Reachable model.initial key) : Option Move :=
  value.table.pending (value.index key reached)

theorem Indexed.done_index (value : Indexed model) (key : Key) (reached : model.network.Reachable model.initial key) :
    value.table.done (value.index key reached) = model.terminal key := by
  rw [value.doneEq, value.get_index]

omit [DecidableEq Key] in
theorem Indexed.progress_iff (value : Indexed model) (before after : Fin value.size) (move : Move) :
    value.table.system.step before (.progress move) after ↔ (move, value.keys.get after) ∈ model.successors (value.keys.get before) := by
  constructor
  · rintro ⟨edge, present, moveEq, targetEq⟩
    rw [← value.rowsExact before]
    exact List.mem_map.mpr ⟨edge, present, by rw [moveEq, targetEq]⟩
  · intro member
    rw [← value.rowsExact before] at member
    obtain ⟨edge, present, same⟩ := List.mem_map.mp member
    have parts := Prod.mk.inj same
    exact ⟨edge, present, parts.1, value.key_injective edge.target after parts.2⟩

omit [DecidableEq Key] in
theorem Indexed.edge_sound (value : Indexed model) (before : Fin value.size) (edge : R.Edge Move value.size)
    (present : edge ∈ value.table.row before) :
    (edge.move, value.keys.get edge.target) ∈ model.successors (value.keys.get before) :=
  (value.progress_iff before edge.target edge.move).mp ⟨edge, present, rfl, rfl⟩

omit [DecidableEq Key] in
theorem Indexed.step_sound (value : Indexed model) {before after : Fin value.size} {event : R.Event Move}
    (step : value.table.system.step before event after) : model.system.step (value.keys.get before) event (value.keys.get after) := by
  cases event with
  | idle => exact congrArg value.keys.get step
  | progress move => exact (value.progress_iff before after move).mp step

theorem Indexed.step_lift (value : Indexed model) (before after : Key) (event : R.Event Move)
    (reached : model.network.Reachable model.initial before) (step : model.system.step before event after) :
    ∃ afterReached : model.network.Reachable model.initial after,
      value.table.system.step (value.index before reached) event (value.index after afterReached) := by
  cases event with
  | idle =>
    have same : after = before := step
    subst after
    exact ⟨reached, rfl⟩
  | progress move =>
    have next : model.network.Reachable model.initial after := reached.trans (.single ⟨move, step⟩)
    refine ⟨next, (value.progress_iff _ _ move).mpr ?_⟩
    simpa only [value.get_index, Model.system] using step

theorem Indexed.reachable_lift (value : Indexed model) {source target : Key}
    (path : model.network.Reachable source target) (reached : model.network.Reachable model.initial source) :
    value.table.network.Reachable (value.index source reached) (value.index target (reached.trans path)) := by
  have lift : ∀ {first last} (route : model.network.Reachable first last), ∀ visited : model.network.Reachable model.initial first,
      value.table.network.Reachable (value.index first visited) (value.index last (visited.trans route)) := by
    intro first last route
    induction route with
    | refl => intro visited; exact .refl _
    | step edge rest ih =>
      intro visited
      obtain ⟨move, present⟩ := edge
      have next := visited.trans (.single ⟨move, present⟩)
      have selected := (value.progress_iff (value.index _ visited) (value.index _ next) move).mpr
        (by simpa only [value.get_index] using present)
      obtain ⟨actual, member, _, same⟩ := selected
      exact .step ⟨actual, member, same⟩ (ih next)
  exact lift path reached

theorem Indexed.reachable (value : Indexed model) (index : Fin value.size) :
    value.table.network.Reachable value.table.initial index := by
  have path := value.reachable_lift (value.keySound index) (.refl _)
  simpa only [value.index_initial, value.index_key] using path

structure Live (value : Indexed model) : Prop where
  terminal : ∀ index, value.table.done index = true → value.table.row index = []
  live : ∀ index, value.table.done index = false → value.table.row index ≠ []

def checkLive (value : Indexed model) : Except String (PLift (Live value)) := do
  if checked : (List.finRange value.size).all (fun index =>
      if value.table.done index then (value.table.row index).isEmpty else !(value.table.row index).isEmpty) = true then
    have rows := List.all_eq_true.mp checked
    return ⟨⟨by
      intro index finished
      have row := rows index (List.mem_finRange index)
      simpa only [finished, ↓reduceIte, List.isEmpty_iff] using row,
      by
        intro index unfinished
        have row := rows index (List.mem_finRange index)
        have nonempty : (value.table.row index).isEmpty = false := by
          cases empty : (value.table.row index).isEmpty <;> simp_all
        exact List.isEmpty_eq_false_iff.mp nonempty⟩⟩
  else throw "The reachable sparse graph has a nonterminal dead end or a terminal progress successor."

variable {value : Indexed model}

omit [DecidableEq Key] in
theorem Live.current (live : Live value) (index : Fin value.size) (unfinished : value.table.done index = false) :
    ∃ edge ∈ value.table.row index, value.table.pending index = some edge.move ∧
      model.system.step (value.keys.get index) (.progress edge.move) (value.keys.get edge.target) := by
  cases row : value.table.row index with
  | nil => exact False.elim (live.live index unfinished row)
  | cons edge rest =>
    have present : edge ∈ value.table.row index := by rw [row]; simp
    refine ⟨edge, by simp, ?_, (value.progress_iff index edge.target edge.move).mp ⟨edge, present, rfl, rfl⟩⟩
    simp only [FiniteProgressRank.Table.pending, row, List.head?_cons, Option.map_some]

theorem Indexed.current (value : Indexed model) (live : Live value) (key : Key)
    (reached : model.network.Reachable model.initial key) (unfinished : model.terminal key = false) :
    ∃ move target, value.pending key reached = some move ∧ (move, target) ∈ model.successors key ∧
      model.network.Reachable model.initial target := by
  obtain ⟨edge, _, selected, step⟩ := live.current (value.index key reached) (by rw [value.done_index]; exact unfinished)
  refine ⟨edge.move, value.keys.get edge.target, selected, ?_, value.keySound edge.target⟩
  simpa only [Model.system, value.get_index] using step

structure Checked (model : Model Key Move) where
  graph : Indexed model
  live : Live graph

def check [DecidableEq Move] (model : Model Key Move) (costs : Costs) (limits : R.Limits) : Except String (Checked model) := do
  let graph ← build model costs limits
  match checkLive graph with
  | .error reason => throw reason
  | .ok live => return ⟨graph, live.down⟩

end Netlib.Theory.FiniteSuccessorGraph
