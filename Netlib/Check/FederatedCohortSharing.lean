import Netlib.Check.FederatedCohortCached

/-!
# Exact sharing across independent header tuples

Signatures retain every keyed local row, including unreachable keys. Equal
signatures give equal complete joint successors, without native reevaluation.
-/

namespace Netlib.Federation.Cohort.Sharing

variable {input : Input} {size : Nat} {context : Context input size}
variable {packet : InFlight.Context input} {header : Packet.Header}
variable {family : Family context} {first second : Vector Packet.Header size}
variable {firstAccepted : Accepted context first} {secondAccepted : Accepted context second}

abbrev Row (input : Input) := InFlight.Key input × List (InFlight.Move × InFlight.Key input)
abbrev Signature (input : Input) (size : Nat) := Vector (List (Row input)) size

def keyedRows (graph : InFlight.Graph.Indexed packet header) : List (Row input) :=
  (List.finRange graph.size).map fun index =>
    (graph.keys.get index, (graph.table.row index).map (fun edge => (edge.move, graph.keys.get edge.target)))

def signature (cache : Cached.Cache family first firstAccepted) : Signature input size :=
  Vector.ofFn fun index => keyedRows (cache.cell index).graph

@[simp] theorem signature_get (cache : Cached.Cache family first firstAccepted) (index : Fin size) :
    (signature cache).get index = keyedRows (cache.cell index).graph := by
  simp [signature, Vector.get, Fin.cast]

theorem keyedRows_sound (graph : InFlight.Graph.Indexed packet header) (row : Row input) (member : row ∈ keyedRows graph) :
    row.2 = InFlight.Control.successors packet header row.1 := by
  obtain ⟨index, _, same⟩ := List.mem_map.mp member
  subst row
  exact graph.rowsExact index

theorem keyedRows_complete (graph : InFlight.Graph.Indexed packet header) (key : InFlight.Key input)
    (member : key ∈ InFlight.Control.allKeys input) : ∃ row ∈ keyedRows graph, row.1 = key := by
  obtain ⟨index, _, same⟩ := graph.lookup key member
  exact ⟨_, List.mem_map.mpr ⟨index, List.mem_finRange index, rfl⟩, same⟩

theorem local_successors_eq (left : Cached.Cache family first firstAccepted)
    (right : Cached.Cache family second secondAccepted) (same : signature left = signature right)
    (index : Fin size) (key : InFlight.Key input) (member : key ∈ InFlight.Control.allKeys input) :
    InFlight.Control.successors (context.packets.get index) (first.get index) key =
      InFlight.Control.successors (context.packets.get index) (second.get index) key := by
  have rows : keyedRows (left.cell index).graph = keyedRows (right.cell index).graph := by
    simpa only [signature_get] using congrArg (fun values => values.get index) same
  obtain ⟨row, present, source⟩ := keyedRows_complete (left.cell index).graph key member
  have firstRow := keyedRows_sound (left.cell index).graph row present
  rw [rows] at present
  have secondRow := keyedRows_sound (right.cell index).graph row present
  rw [source] at firstRow secondRow
  exact firstRow.symm.trans secondRow

theorem local_step_eq (left : Cached.Cache family first firstAccepted)
    (right : Cached.Cache family second secondAccepted) (same : signature left = signature right)
    (index : Fin size) (key : InFlight.Key input) (member : key ∈ InFlight.Control.allKeys input)
    (move : InFlight.Move) :
    InFlight.Control.step (context.packets.get index) (first.get index) key move =
      InFlight.Control.step (context.packets.get index) (second.get index) key move := by
  have rows := local_successors_eq left right same index key member
  cases selected : InFlight.Control.step (context.packets.get index) (first.get index) key move with
  | none =>
    cases other : InFlight.Control.step (context.packets.get index) (second.get index) key move with
    | none => rfl
    | some after =>
      have present := (InFlight.Control.mem_successors _ _ key after move).mpr other
      rw [← rows] at present
      have impossible := (InFlight.Control.mem_successors _ _ key after move).mp present
      rw [selected] at impossible
      cases impossible
  | some after =>
    have present := (InFlight.Control.mem_successors _ _ key after move).mpr selected
    rw [rows] at present
    exact ((InFlight.Control.mem_successors _ _ key after move).mp present).symm

theorem good_component_member (cache : Cached.Cache family first firstAccepted) (key : Key input size)
    (good : Control.good context key = true) (index : Fin size) : key.packet index ∈ InFlight.Control.allKeys input := by
  obtain ⟨position, found⟩ := Cached.index_present cache key good index
  have source := InFlight.Graph.findIndex_sound _ _ _ found
  rw [← (cache.cell index).graph.keysExact, ← source]
  exact Vector.mem_toList_iff.mpr (Vector.mem_of_getElem rfl)

theorem localChecks_eq (left : Cached.Cache family first firstAccepted)
    (right : Cached.Cache family second secondAccepted) (same : signature left = signature right)
    (before after : Key input size) (good : Control.good context before = true) (move : Move size) :
    Control.localChecks context first before after move = Control.localChecks context second before after move := by
  unfold Control.localChecks
  apply congrArg ((List.finRange size).all)
  funext index
  cases selected : move.local index with
  | none => rfl
  | some operation =>
    simp only [local_step_eq left right same index _ (good_component_member left before good index) operation]

theorem step_eq (left : Cached.Cache family first firstAccepted)
    (right : Cached.Cache family second secondAccepted) (same : signature left = signature right)
    (before : Key input size) (move : Move size) :
    Control.step context first before move = Control.step context second before move := by
  by_cases good : Control.good context before = true
  · simp only [Control.step, good, Bool.true_and]
    cases Control.rawStep context before move with
    | none => rfl
    | some after => simp only [localChecks_eq left right same before after good move]
  · have bad : Control.good context before = false := Bool.eq_false_iff.mpr good
    simp only [Control.step, bad, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

theorem successors_eq (left : Cached.Cache family first firstAccepted)
    (right : Cached.Cache family second secondAccepted) (same : signature left = signature right)
    (before : Key input size) : Control.successors context first before = Control.successors context second before := by
  simp only [Control.successors, step_eq left right same]

theorem cached_successors_eq (left : Cached.Cache family first firstAccepted)
    (right : Cached.Cache family second secondAccepted) (same : signature left = signature right)
    (before : Key input size) : Cached.successors left before = Cached.successors right before := by
  rw [Cached.successors_eq, Cached.successors_eq]
  exact successors_eq left right same before

end Netlib.Federation.Cohort.Sharing
