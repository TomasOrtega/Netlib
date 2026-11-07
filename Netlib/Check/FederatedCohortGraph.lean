import Netlib.Check.FederatedCohortComponents
import Netlib.Check.FederatedCohortControl
import Netlib.Check.FederatedCohortCached
import Netlib.Theory.FiniteSuccessorGraph

/-!
# Reachable cohort graphs and inherited packet ranks

Joint rows include FIFO and reservation guards. Component ranks justify
descent; the sparse live-row check separately rules out resource deadlocks.
-/

namespace Netlib.Federation.Cohort.Graph

namespace S
export Theory.FiniteSuccessorGraph (Model Indexed Live Checked Costs Limits)
end S

namespace R
export Theory.FiniteProgressRank (Event)
end R

variable {input : Input} {size : Nat} {context : Context input size}
variable {packet : InFlight.Context input} {header : Packet.Header}

def model (context : Context input size) (headers : Vector Packet.Header size) : S.Model (Key input size) (Move size) :=
  ⟨initialKey context, Control.successors context headers, finished⟩

def candidateCount (input : Input) (size : Nat) : Nat := size * ((InFlight.Control.nodes input).length + 2) + 3

def sourceRows (context : Context input size) : Nat :=
  (input.left.versions ++ input.right.versions).foldl (fun count revision => count + 1 + Native.nativeRows revision +
    revision.projection.length + revision.anchors.length) 0 +
    input.intent.borders.foldl (fun count border => count + 1 + border.cases.length) 0 +
    context.packets.toList.foldl (fun count packet => count +
      packet.profile.leftFences.foldl (fun count names => count + 1 + names.length) 0 +
      packet.profile.rightFences.foldl (fun count names => count + 1 + names.length) 0) 0 + 1

def costs (context : Context input size) : S.Costs :=
  let width := (InFlight.Control.nodes input).length + size + 1
  ⟨candidateCount input size * (sourceRows context + 1) ^ 2 * width ^ 2, width⟩

@[simp] theorem initial_packet (context : Context input size) (index : Fin size) :
    (initialKey context).packet index = InFlight.initialKey (context.packets.get index) := by
  simp [initialKey, Key.packet, InFlight.initialKey, Vector.get, Fin.cast]

def localNetwork (context : Context input size) (headers : Vector Packet.Header size) (index : Fin size) :
    Network (InFlight.Key input) :=
  ⟨fun before after => ∃ move, InFlight.Control.step (context.packets.get index) (headers.get index) before move = some after⟩

theorem local_edge (headers : Vector Packet.Header size) (index : Fin size) (before after : Key input size)
    (edge : (model context headers).network.link before after) :
    (localNetwork context headers index).Reachable (before.packet index) (after.packet index) := by
  obtain ⟨move, member⟩ := edge
  have facts := Control.step_facts context headers before after move ((Control.mem_successors context headers before after move).mp member)
  have selected := facts.localSteps index
  cases chosen : move.local index with
  | none =>
    have same : after.packet index = before.packet index := by simpa only [chosen] using selected
    rw [same]
    exact .refl _
  | some action =>
    exact .single ⟨action, by simpa only [chosen] using selected⟩

theorem local_reachable (headers : Vector Packet.Header size) (key : Key input size)
    (reached : (model context headers).network.Reachable (initialKey context) key) (index : Fin size) :
    (localNetwork context headers index).Reachable (InFlight.initialKey (context.packets.get index)) (key.packet index) := by
  have path := reached.map (fun key => key.packet index) (local_edge headers index)
  simpa only [initial_packet] using path

private theorem local_path (cell : InFlight.RankedCell packet header) {before after : InFlight.Key input}
    (path : (⟨fun source target => ∃ move, InFlight.Control.step packet header source move = some target⟩ :
      Network (InFlight.Key input)).Reachable before after)
    (member : before ∈ InFlight.Control.allKeys input) :
    after ∈ InFlight.Control.allKeys input ∧
      cell.graph.table.network.Reachable (cell.graph.index before) (cell.graph.index after) := by
  induction path with
  | refl => exact ⟨member, .refl _⟩
  | step edge _ ih =>
    obtain ⟨move, selected⟩ := edge
    have nextMember := InFlight.Control.mem_allKeys _ (InFlight.Control.step_valid packet header _ _ move selected)
    obtain ⟨lastMember, tail⟩ := ih nextMember
    have step := cell.graph.index_step _ _ move member selected
    obtain ⟨actual, present, _, same⟩ := step
    exact ⟨lastMember, .step ⟨actual, present, same⟩ tail⟩

structure Position (cell : InFlight.RankedCell packet header) (key : InFlight.Key input) where
  index : Fin cell.graph.size
  keyEq : cell.graph.keys.get index = key
  reached : cell.graph.table.network.Reachable cell.graph.table.initial index

variable (family : Family context) (headers : Vector Packet.Header size) (accepted : Accepted context headers)

theorem component_reachable (key : Key input size)
    (reached : (model context headers).network.Reachable (initialKey context) key) (index : Fin size) :
    key.packet index ∈ InFlight.Control.allKeys input ∧
      (family.cell headers accepted index).graph.table.network.Reachable
        (family.cell headers accepted index).graph.table.initial
        ((family.cell headers accepted index).graph.index (key.packet index)) := by
  let cell := family.cell headers accepted index
  have first : InFlight.initialKey (context.packets.get index) ∈ InFlight.Control.allKeys input := by
    have member : cell.graph.keys.get cell.graph.table.initial ∈ cell.graph.keys.toList :=
      Vector.mem_toList_iff.mpr (Vector.mem_of_getElem rfl)
    rw [cell.graph.initialEq, cell.graph.keysExact] at member
    exact member
  have facts := local_path cell (local_reachable headers key reached index) first
  simpa only [cell.graph.index_initial] using facts

def position (key : Key input size) (reached : (model context headers).network.Reachable (initialKey context) key)
    (index : Fin size) : Position (family.cell headers accepted index) (key.packet index) :=
  let cell := family.cell headers accepted index
  let facts := component_reachable family headers accepted key reached index
  let selected := InFlight.Graph.findIndex cell.graph.keys (key.packet index)
  have present : selected.isSome = true := by
    obtain ⟨found, same⟩ := InFlight.Graph.findIndex_exists cell.graph.keys _ (by rw [cell.graph.keysExact]; exact facts.1)
    simp only [selected, same, Option.isSome_some]
  let current := selected.get present
  have same : cell.graph.keys.get current = key.packet index := by
    exact InFlight.Graph.findIndex_sound cell.graph.keys _ current (Option.some_get present).symm
  have equal : current = cell.graph.index (key.packet index) :=
    cell.graph.key_injective _ _ (same.trans (cell.graph.get_index _ facts.1).symm)
  ⟨current, same, by rw [equal]; exact facts.2⟩

def componentRank (key : Key input size) (reached : (model context headers).network.Reachable (initialKey context) key)
    (index : Fin size) : Nat :=
  (family.cell headers accepted index).ranked.rank (position family headers accepted key reached index).index

def remaining (key : Key input size) : Nat :=
  input.left.updates.length - key.current.1.val + (input.right.updates.length - key.current.2.val)

def potential (key : Key input size) (reached : (model context headers).network.Reachable (initialKey context) key) : Nat :=
  ((List.finRange size).map (componentRank family headers accepted key reached)).sum + remaining key

structure Checked (family : Family context) (headers : Vector Packet.Header size) (accepted : Accepted context headers) where
  sparse : S.Checked (model context headers)
  initialGood : Control.good context (initialKey context) = true

def check (initialGood : Control.good context (initialKey context) = true) (limits : S.Limits) : Except String (Checked family headers accepted) := do
  let cache := Cached.Cache.build family headers accepted
  let optimized : S.Model (Key input size) (Move size) := ⟨initialKey context, Cached.successors cache, finished⟩
  let checked ← Theory.FiniteSuccessorGraph.check optimized (costs context) limits
  let graph : S.Indexed (model context headers) := { checked.graph with
    rowsExact := fun index => (checked.graph.rowsExact index).trans (Cached.successors_eq cache _)
    keySound := fun index => (checked.graph.keySound index).mono (by
      intro source target edge
      obtain ⟨move, present⟩ := edge
      exact ⟨move, by
        change (move, target) ∈ Control.successors context headers source
        rw [← Cached.successors_eq cache source]
        exact present⟩) }
  let sparse : S.Checked (model context headers) := ⟨graph, ⟨checked.live.terminal, checked.live.live⟩⟩
  return ⟨sparse, initialGood⟩

theorem Checked.good_at (value : Checked family headers accepted) (key : Key input size)
    (reached : (model context headers).network.Reachable (initialKey context) key) : Control.good context key = true := by
  have preserve : ∀ {before after}, (model context headers).network.Reachable before after →
      Control.good context before = true → Control.good context after = true := by
    intro before after path
    induction path with
    | refl => exact id
    | step edge _ ih =>
      intro _
      obtain ⟨move, member⟩ := edge
      exact ih (Control.step_facts context headers _ _ move ((Control.mem_successors context headers _ _ move).mp member)).afterGood
  exact preserve reached value.initialGood

def Checked.transport (value : Checked family headers accepted) (nextHeaders : Vector Packet.Header size)
    (nextAccepted : Accepted context nextHeaders)
    (same : ∀ key, Control.successors context headers key = Control.successors context nextHeaders key) :
    Checked family nextHeaders nextAccepted :=
  let graph : S.Indexed (model context nextHeaders) := { value.sparse.graph with
    rowsExact := fun index => (value.sparse.graph.rowsExact index).trans (same _)
    keySound := fun index => (value.sparse.graph.keySound index).mono (by
      intro source target edge
      obtain ⟨move, present⟩ := edge
      exact ⟨move, by
        change (move, target) ∈ Control.successors context nextHeaders source
        rw [← same source]
        exact present⟩) }
  ⟨⟨graph, ⟨value.sparse.live.terminal, value.sparse.live.live⟩⟩, value.initialGood⟩

theorem Checked.transport_table (value : Checked family headers accepted) (nextHeaders : Vector Packet.Header size)
    (nextAccepted : Accepted context nextHeaders)
    (same : ∀ key, Control.successors context headers key = Control.successors context nextHeaders key) :
    (value.transport family headers accepted nextHeaders nextAccepted same).sparse.graph.table = value.sparse.graph.table := rfl

end Netlib.Federation.Cohort.Graph
