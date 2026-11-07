import Netlib.Check.FederatedPacketControl
import Netlib.Theory.FiniteProgressRank

/-!
# Exact indexed packet control graphs

Rows come from the actual control successor list. An independent check compares
every generated row and terminal flag before rank analysis can consume them.
-/

namespace Netlib.Federation.InFlight.Graph

namespace R
export Theory.FiniteProgressRank (Edge Table Event Limits Checked edgeCount workEstimate)
end R

variable {input : Input}

def findIndex (keys : Vector (Key input) size) (key : Key input) : Option (Fin size) :=
  (List.finRange size).find? (fun index => decide (keys.get index = key))

theorem findIndex_sound (keys : Vector (Key input) size) (key : Key input) (index : Fin size)
    (found : findIndex keys key = some index) : keys.get index = key := by
  exact of_decide_eq_true (List.find?_some (p := fun index : Fin size => decide (keys.get index = key)) found)

theorem findIndex_exists (keys : Vector (Key input) size) (key : Key input) (member : key ∈ keys.toList) :
    ∃ index, findIndex keys key = some index := by
  have present : key ∈ keys := Vector.mem_toList_iff.mp member
  obtain ⟨position, within, selected⟩ := Vector.mem_iff_getElem.mp present
  let index : Fin size := ⟨position, within⟩
  have equal : keys.get index = key := selected
  cases found : findIndex keys key with
  | some index => exact ⟨index, rfl⟩
  | none =>
    have absent := List.find?_eq_none.mp found index (List.mem_finRange index)
    exact False.elim (absent (decide_eq_true equal))

private def encodeRow (keys : Vector (Key input) size) : List (Move × Key input) → Except String (List (R.Edge Move size))
  | [] => .ok []
  | (move, target) :: rest => do
    let some index := findIndex keys target | throw "A control successor is outside the finite key inventory."
    return ⟨move, index⟩ :: (← encodeRow keys rest)

def universeSize (input : Input) : Nat :=
  input.left.versions.length * input.right.versions.length * (2 * (Control.nodes input).length + 1)

def sourceRows (context : Context input) : Nat :=
  (input.left.versions.map (fun revision => Native.nativeRows revision + revision.projection.length + revision.anchors.length)).sum +
    (input.right.versions.map (fun revision => Native.nativeRows revision + revision.projection.length + revision.anchors.length)).sum +
    input.intent.borders.foldl (fun count border => count + 1 + border.cases.length) 0 +
    context.profile.leftFences.foldl (fun count names => count + 1 + names.length) 0 +
    context.profile.rightFences.foldl (fun count names => count + 1 + names.length) 0 + 1

/-- Includes candidate guards, native source scans, key lookup, and row validation. -/
def generationWork (context : Context input) : Nat :=
  let rows := sourceRows context
  let states := universeSize input
  let candidates := (Control.nodes input).length + 5
  3 * (rows ^ 2 + (states + 1) * (rows ^ 2 + candidates * (rows + states + 1)))

def preflight (context : Context input) (limits : R.Limits) : Except String Unit := do
  let states := universeSize input
  if states > limits.states then throw s!"Packet control states {states} exceed budget {limits.states}."
  if generationWork context > limits.work then
    throw s!"Packet successor generation estimate {generationWork context} exceeds budget {limits.work}."

private def exact (context : Context input) (header : Packet.Header) (keys : Vector (Key input) size)
    (table : R.Table Move size) : Bool :=
  decide (keys.toList = Control.allKeys input) && decide keys.toList.Nodup &&
    decide (keys.get table.initial = initialKey context) &&
    (List.finRange size).all (fun index =>
      decide ((table.row index).map (fun edge => (edge.move, keys.get edge.target)) =
        Control.successors context header (keys.get index)) &&
      decide (table.done index = finished (keys.get index)))

structure Indexed (context : Context input) (header : Packet.Header) where
  size : Nat
  keys : Vector (Key input) size
  keysExact : keys.toList = Control.allKeys input
  keysNodup : keys.toList.Nodup
  table : R.Table Move size
  initialEq : keys.get table.initial = initialKey context
  rowsExact : ∀ index, (table.row index).map (fun edge => (edge.move, keys.get edge.target)) =
    Control.successors context header (keys.get index)
  doneEq : ∀ index, table.done index = finished (keys.get index)

private def validate (context : Context input) (header : Packet.Header) (keys : Vector (Key input) size)
    (table : R.Table Move size) : Except String (Indexed context header) := do
  if checked : exact context header keys table = true then
    have facts : ((keys.toList = Control.allKeys input ∧ keys.toList.Nodup) ∧
        keys.get table.initial = initialKey context) ∧ ∀ index ∈ List.finRange size,
        (table.row index).map (fun edge => (edge.move, keys.get edge.target)) =
          Control.successors context header (keys.get index) ∧ table.done index = finished (keys.get index) := by
      simpa only [exact, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] using checked
    return ⟨size, keys, facts.1.1.1, facts.1.1.2, table, facts.1.2,
      fun index => (facts.2 index (List.mem_finRange index)).1,
      fun index => (facts.2 index (List.mem_finRange index)).2⟩
  else throw "The indexed packet graph differs from the actual control successor table."

def build (context : Context input) (header : Packet.Header) (limits : R.Limits) : Except String (Indexed context header) := do
  preflight context limits
  let keys := (Control.allKeys input).toArray.toVector
  let some initial := findIndex keys (initialKey context) | throw "The actual initial packet key is absent."
  let rows ← Vector.ofFnM (fun index => encodeRow keys (Control.successors context header (keys.get index)))
  let table : R.Table Move keys.size := ⟨initial, rows, Vector.ofFn (fun index => finished (keys.get index))⟩
  if R.edgeCount table > limits.edges then
    throw s!"Actual packet successors {R.edgeCount table} exceed budget {limits.edges}."
  validate context header keys table

def Indexed.rankWork (value : Indexed context header) : Nat := R.workEstimate value.size (R.edgeCount value.table)

def Indexed.analyze (value : Indexed context header) (limits : R.Limits) : Except String (R.Checked value.table) :=
  Theory.FiniteProgressRank.check value.table limits

variable {context : Context input} {header : Packet.Header}

theorem Indexed.key_injective (value : Indexed context header) (first second : Fin value.size)
    (same : value.keys.get first = value.keys.get second) : first = second := by
  change value.keys[first.val] = value.keys[second.val] at same
  apply Fin.ext
  apply value.keysNodup.eq_of_getElem_eq
    (by simpa only [Vector.length_toList] using first.isLt)
    (by simpa only [Vector.length_toList] using second.isLt)
  simpa only [Vector.getElem_toList] using same

theorem Indexed.index_get (value : Indexed context header) (index : Fin value.size) :
    findIndex value.keys (value.keys.get index) = some index := by
  have member : value.keys.get index ∈ value.keys.toList := by
    apply Vector.mem_toList_iff.mpr
    exact Vector.mem_of_getElem rfl
  obtain ⟨found, selected⟩ := findIndex_exists value.keys (value.keys.get index) member
  have same := value.key_injective found index (findIndex_sound value.keys _ found selected)
  simpa only [same] using selected

theorem Indexed.lookup (value : Indexed context header) (key : Key input) (member : key ∈ Control.allKeys input) :
    ∃ index, findIndex value.keys key = some index ∧ value.keys.get index = key := by
  have present : key ∈ value.keys.toList := by rw [value.keysExact]; exact member
  obtain ⟨index, selected⟩ := findIndex_exists value.keys key present
  exact ⟨index, selected, findIndex_sound value.keys key index selected⟩

def Indexed.index (value : Indexed context header) (key : Key input) : Fin value.size :=
  (findIndex value.keys key).getD value.table.initial

theorem Indexed.get_index (value : Indexed context header) (key : Key input)
    (member : key ∈ Control.allKeys input) : value.keys.get (value.index key) = key := by
  obtain ⟨index, selected, same⟩ := value.lookup key member
  simpa only [Indexed.index, selected, Option.getD_some] using same

theorem Indexed.index_key (value : Indexed context header) (index : Fin value.size) :
    value.index (value.keys.get index) = index := by
  simp only [Indexed.index, value.index_get index, Option.getD_some]

theorem Indexed.index_initial (value : Indexed context header) :
    value.index (initialKey context) = value.table.initial := by
  rw [← value.initialEq]
  exact value.index_key _

theorem Indexed.progress_iff (value : Indexed context header) (before after : Fin value.size) (move : Move) :
    value.table.system.step before (.progress move) after ↔
      Control.step context header (value.keys.get before) move = some (value.keys.get after) := by
  constructor
  · rintro ⟨edge, present, moveEq, targetEq⟩
    have member : (edge.move, value.keys.get edge.target) ∈ Control.successors context header (value.keys.get before) := by
      rw [← value.rowsExact before]
      exact List.mem_map.mpr ⟨edge, present, rfl⟩
    have selected := (Control.mem_successors context header _ _ _).mp member
    simpa only [moveEq, targetEq] using selected
  · intro selected
    have member := (Control.mem_successors context header _ _ _).mpr selected
    rw [← value.rowsExact before] at member
    obtain ⟨edge, present, same⟩ := List.mem_map.mp member
    have parts := Prod.mk.inj same
    exact ⟨edge, present, parts.1, value.key_injective edge.target after parts.2⟩

theorem Indexed.edge_step (value : Indexed context header) (before : Fin value.size) (edge : R.Edge Move value.size)
    (member : edge ∈ value.table.row before) :
    Control.step context header (value.keys.get before) edge.move = some (value.keys.get edge.target) :=
  (value.progress_iff before edge.target edge.move).mp ⟨edge, member, rfl, rfl⟩

theorem Indexed.step_lift (value : Indexed context header) (before : Fin value.size) (after : Key input) (move : Move)
    (selected : Control.step context header (value.keys.get before) move = some after) :
    ∃ index, value.keys.get index = after ∧ value.table.system.step before (.progress move) index := by
  have member := Control.mem_allKeys after (Control.step_valid context header _ after move selected)
  obtain ⟨index, _, exactKey⟩ := value.lookup after member
  refine ⟨index, exactKey, (value.progress_iff before index move).mpr ?_⟩
  simpa only [exactKey] using selected

theorem Indexed.index_step (value : Indexed context header) (before after : Key input) (move : Move)
    (member : before ∈ Control.allKeys input)
    (selected : Control.step context header before move = some after) :
    value.table.system.step (value.index before) (.progress move) (value.index after) := by
  have afterMember := Control.mem_allKeys after (Control.step_valid context header before after move selected)
  apply (value.progress_iff _ _ move).mpr
  simpa only [value.get_index before member, value.get_index after afterMember] using selected

end Netlib.Federation.InFlight.Graph
