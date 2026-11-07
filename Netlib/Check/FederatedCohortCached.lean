import Netlib.Check.FederatedCohortComponents
import Netlib.Check.FederatedCohortFacts

/-!
# Complete successor rows from retained component tables

Each header tuple materializes its component cells once. Cached row lookup
equals the native step for every key, with a literal fallback on cache miss.
-/

namespace Netlib.Federation.Cohort.Cached

variable {input : Input} {size : Nat} {context : Context input size}
variable {headers : Vector Packet.Header size} {family : Family context} {accepted : Accepted context headers}
variable {packet : InFlight.Context input} {header : Packet.Header}

structure Cache (family : Family context) (headers : Vector Packet.Header size) (accepted : Accepted context headers) where
  entries : Vector ((index : Fin size) × InFlight.RankedCell (context.packets.get index) (headers.get index)) size
  aligned : ∀ index, (entries.get index).1 = index
  stored : ∀ index, entries.get index = ⟨index, family.cell headers accepted index⟩

def Cache.build (family : Family context) (headers : Vector Packet.Header size) (accepted : Accepted context headers) :
    Cache family headers accepted where
  entries := Vector.ofFn (fun index => ⟨index, family.cell headers accepted index⟩)
  aligned index := by simp [Vector.get, Fin.cast]
  stored index := by simp [Vector.get, Fin.cast]

def Cache.cell (cache : Cache family headers accepted) (index : Fin size) :
    InFlight.RankedCell (context.packets.get index) (headers.get index) :=
  (cache.aligned index) ▸ (cache.entries.get index).2

private theorem aligned_cell (entry : (index : Fin size) × InFlight.RankedCell (context.packets.get index) (headers.get index))
    (index : Fin size) (aligned : entry.1 = index) (cell : InFlight.RankedCell (context.packets.get index) (headers.get index))
    (stored : entry = ⟨index, cell⟩) : aligned ▸ entry.2 = cell := by
  rcases entry with ⟨actual, value⟩
  cases aligned
  cases stored
  rfl

theorem Cache.cell_stored (cache : Cache family headers accepted) (index : Fin size) :
    cache.cell index = family.cell headers accepted index :=
  aligned_cell _ index (cache.aligned index) _ (cache.stored index)

def rowStep (graph : InFlight.Graph.Indexed packet header) (index : Fin graph.size) (move : InFlight.Move) :
    Option (InFlight.Key input) :=
  ((graph.table.row index).find? (fun edge => decide (edge.move = move))).map
    (fun edge => graph.keys.get edge.target)

theorem rowStep_eq (graph : InFlight.Graph.Indexed packet header) (index : Fin graph.size) (move : InFlight.Move) :
    rowStep graph index move = InFlight.Control.step packet header (graph.keys.get index) move := by
  unfold rowStep
  cases found : (graph.table.row index).find? (fun edge => decide (edge.move = move)) with
  | some edge =>
    have moveEq := of_decide_eq_true (List.find?_some
      (p := fun edge : Theory.FiniteProgressRank.Edge InFlight.Move graph.size => decide (edge.move = move)) found)
    have selected := graph.edge_step index edge (List.mem_of_find?_eq_some found)
    rw [moveEq] at selected
    exact selected.symm
  | none =>
    cases selected : InFlight.Control.step packet header (graph.keys.get index) move with
    | none => rfl
    | some after =>
      obtain ⟨target, _, edge, member, moveEq, _⟩ := graph.step_lift index after move selected
      exact False.elim ((List.find?_eq_none.mp found edge member) (decide_eq_true moveEq))

def localStep (cache : Cache family headers accepted) (index : Fin size) (before : InFlight.Key input)
    (move : InFlight.Move) : Option (InFlight.Key input) :=
  let graph := (cache.cell index).graph
  match InFlight.Graph.findIndex graph.keys before with
  | none => InFlight.Control.step (context.packets.get index) (headers.get index) before move
  | some position => rowStep graph position move

theorem localStep_eq (cache : Cache family headers accepted) (index : Fin size) (before : InFlight.Key input)
    (move : InFlight.Move) : localStep cache index before move =
      InFlight.Control.step (context.packets.get index) (headers.get index) before move := by
  dsimp only [localStep]
  cases found : InFlight.Graph.findIndex (cache.cell index).graph.keys before with
  | none => rfl
  | some position =>
    change rowStep (cache.cell index).graph position move = _
    rw [rowStep_eq, InFlight.Graph.findIndex_sound _ _ _ found]

theorem index_present (cache : Cache family headers accepted) (key : Key input size)
    (good : Control.good context key = true) (index : Fin size) :
    ∃ position, InFlight.Graph.findIndex (cache.cell index).graph.keys (key.packet index) = some position := by
  have valid : InFlight.Control.Valid (key.packet index) := by
    intro node occupied
    have checked := ((Control.good_iff context key).mp good).1 index
    cases phase : key.phases.get index with
    | held source =>
      have same : source = node := Option.some.inj (by simpa only [Key.packet, phase, InFlight.Control.occupied] using occupied)
      have known := (Control.held_conserved context key good index source phase).1
      simpa only [Key.packet, same] using known
    | flight receiver =>
      have same : receiver = node := Option.some.inj (by simpa only [Key.packet, phase, InFlight.Control.occupied] using occupied)
      have known := (Control.flight_conserved context key good index receiver phase).1
      simpa only [Key.packet, same] using known
    | delivered => simp [Key.packet, phase, InFlight.Control.occupied] at occupied
  have member := InFlight.Control.mem_allKeys (key.packet index) valid
  obtain ⟨position, selected, _⟩ := (cache.cell index).graph.lookup (key.packet index) member
  exact ⟨position, selected⟩

def localChecks (cache : Cache family headers accepted) (before after : Key input size) (move : Move size) : Bool :=
  (List.finRange size).all fun index => match move.local index with
    | none => decide (after.packet index = before.packet index)
    | some selected => decide (localStep cache index (before.packet index) selected = some (after.packet index))

theorem localChecks_eq (cache : Cache family headers accepted) (before after : Key input size) (move : Move size) :
    localChecks cache before after move = Control.localChecks context headers before after move := by
  unfold localChecks Control.localChecks
  apply congrArg ((List.finRange size).all)
  funext index
  cases move.local index <;> simp only [localStep_eq]

def stepAfter (cache : Cache family headers accepted) (before : Key input size) (move : Move size) :
    Option (Key input size) :=
  match Control.rawStep context before move with
  | none => none
  | some after => if Control.good context after && localChecks cache before after move then some after else none

theorem stepAfter_eq (cache : Cache family headers accepted) (before : Key input size) (move : Move size)
    (good : Control.good context before = true) (member : move ∈ Control.candidates input before) :
    stepAfter cache before move = Control.step context headers before move := by
  simp only [stepAfter, Control.step, good, decide_eq_true member, Bool.true_and, ↓reduceIte, localChecks_eq]
  rfl

private theorem filterMap_eq (items : List α) (first second : α → Option β)
    (same : ∀ item ∈ items, first item = second item) : items.filterMap first = items.filterMap second := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    rw [List.filterMap_cons, List.filterMap_cons, same item (by simp), ih (fun next member => same next (by simp [member]))]

def successors (cache : Cache family headers accepted) (before : Key input size) : List (Move size × Key input size) :=
  if Control.good context before then
    (Control.candidates input before).filterMap fun move => (stepAfter cache before move).map (move, ·)
  else []

theorem successors_eq (cache : Cache family headers accepted) (before : Key input size) :
    successors cache before = Control.successors context headers before := by
  by_cases good : Control.good context before = true
  · simp only [successors, good, ↓reduceIte, Control.successors]
    apply filterMap_eq
    intro move member
    rw [stepAfter_eq cache before move good member]
  · have bad : Control.good context before = false := Bool.eq_false_iff.mpr good
    simp [successors, Control.successors, Control.step, bad]

end Netlib.Federation.Cohort.Cached
