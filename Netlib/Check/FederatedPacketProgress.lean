import Netlib.Check.FederatedPacket
import Netlib.Check.FederatedPacketInvariant

/-!
# Checked ranks on actual packet executions

The finite graph supplies the rank and current demand. The model invariant
lifts each listed move to an actual supported action at the current cut.
-/

namespace Netlib.Federation.InFlight.Progress

namespace R
export Theory.FiniteProgressRank (Event serves reachable)
end R

namespace B
export Theory.BoundedProgress (Prefix)
end B

variable {input : Input} {context : Context input} {header : Packet.Header}
variable {deployment : Deployment.Checked input}

def tag (event : InFlight.Event input) : R.Event Move :=
  match event.action.move? with
  | none => .idle
  | some move => .progress move

def pending (cell : RankedCell context header) (state : State input) : Option Move :=
  cell.graph.table.pending (cell.graph.index state.key)

def serves (move : Move) (event : InFlight.Event input) : Bool := R.serves move (tag event)

def rank (cell : RankedCell context header) (state : State input) : Nat :=
  cell.ranked.rank (cell.graph.index state.key)

def deadline (cell : RankedCell context header) (bound : Nat) : Nat :=
  cell.ranked.rank cell.graph.table.initial * bound

def Complete (state : State input) : Prop :=
  (∃ index, state.phase = .delivered index) ∧ state.current.1.val = input.left.updates.length ∧
    state.current.2.val = input.right.updates.length

theorem finished_iff (state : State input) : finished state.key = true ↔ Complete state := by
  cases phase : state.phase <;> simp [finished, State.key, Phase.key, Complete, phase]

theorem valid_at (checked : Context.Validated deployment context)
    (execution : B.Prefix (Execution.system context header))
    (initial : execution.state 0 = initialState context) (slot : Nat) (within : slot ≤ execution.length) :
    (execution.state slot).Valid context header := by
  induction slot with
  | zero => rw [initial]; exact initial_valid checked header
  | succ slot ih =>
    exact Execution.step_valid context header (ih (by omega)) (execution.checked slot (by omega))

theorem clock_at (execution : B.Prefix (Execution.system context header))
    (initial : execution.state 0 = initialState context) (slot : Nat) (within : slot ≤ execution.length) :
    (execution.state slot).nextIndex = slot := by
  induction slot with
  | zero => rw [initial]; rfl
  | succ slot ih =>
    rw [Execution.step_tick context header (execution.checked slot (by omega)), ih (by omega)]

theorem project_step (cell : RankedCell context header) {before after : State input} {event : InFlight.Event input}
    (valid : before.Valid context header) (step : (Execution.system context header).step before event after) :
    cell.graph.table.system.step (cell.graph.index before.key) (tag event) (cell.graph.index after.key) := by
  have selected := Execution.step_key context header step
  cases move : event.action.move? with
  | none =>
    have same : after.key = before.key := by simpa only [Execution.KeyStep, move] using selected
    simpa only [tag, move, Theory.FiniteProgressRank.Table.system] using congrArg cell.graph.index same
  | some moveValue =>
    have control : Control.step context header before.key moveValue = some after.key := by
      simpa only [Execution.KeyStep, move] using selected
    simpa only [tag, move] using cell.graph.index_step before.key after.key moveValue
      (Control.mem_allKeys before.key valid.key) control

def projectedPrefix (checked : Context.Validated deployment context) (cell : RankedCell context header)
    (execution : B.Prefix (Execution.system context header)) (initial : execution.state 0 = initialState context) :
    B.Prefix cell.graph.table.system where
  length := execution.length
  state slot := cell.graph.index (execution.state slot).key
  action slot := tag (execution.action slot)
  checked slot within := project_step cell (valid_at checked execution initial slot (by omega)) (execution.checked slot within)

theorem projected_initial (checked : Context.Validated deployment context) (cell : RankedCell context header)
    (execution : B.Prefix (Execution.system context header)) (initial : execution.state 0 = initialState context) :
    (projectedPrefix checked cell execution initial).state 0 = cell.graph.table.initial := by
  simp only [projectedPrefix, initial, initialState_key, cell.graph.index_initial]

theorem reachable_at (checked : Context.Validated deployment context) (cell : RankedCell context header)
    (execution : B.Prefix (Execution.system context header)) (initial : execution.state 0 = initialState context)
    (slot : Nat) (within : slot ≤ execution.length) :
    cell.graph.index (execution.state slot).key ∈ R.reachable cell.graph.table :=
  cell.ranked.prefix_mem (projectedPrefix checked cell execution initial)
    (projected_initial checked cell execution initial) slot within

theorem zero_iff_complete (checked : Context.Validated deployment context) (cell : RankedCell context header)
    (execution : B.Prefix (Execution.system context header)) (initial : execution.state 0 = initialState context)
    (slot : Nat) (within : slot ≤ execution.length) :
    rank cell (execution.state slot) = 0 ↔ Complete (execution.state slot) := by
  have member := Control.mem_allKeys (execution.state slot).key (valid_at checked execution initial slot within).key
  have zero := cell.ranked.zero_iff _ (reachable_at checked cell execution initial slot within)
  rw [cell.graph.doneEq, cell.graph.get_index _ member] at zero
  exact zero.trans (finished_iff _)

theorem modeled_completion (checked : Context.Validated deployment context) (cell : RankedCell context header)
    (execution : B.Prefix (Execution.system context header)) (initial : execution.state 0 = initialState context)
    (bound : Nat) (_positive : 0 < bound)
    (service : Theory.BoundedServiceCheck.Serviced execution.length
      (fun slot => pending cell (execution.state slot)) execution.action serves bound)
    (enough : deadline cell bound ≤ execution.length) : Complete (execution.state (deadline cell bound)) := by
  have done := cell.ranked.completes_by (projectedPrefix checked cell execution initial)
    (projected_initial checked cell execution initial) bound service enough
  have member := Control.mem_allKeys (execution.state (deadline cell bound)).key
    (valid_at checked execution initial _ enough).key
  change cell.graph.table.done (cell.graph.index (execution.state (deadline cell bound)).key) = true at done
  rw [cell.graph.doneEq, cell.graph.get_index _ member] at done
  exact (finished_iff _).mp done

theorem current_enabled (checked : Context.Validated deployment context) (cell : RankedCell context header)
    (execution : B.Prefix (Execution.system context header)) (initial : execution.state 0 = initialState context)
    (slot : Nat) (within : slot ≤ execution.length) (positive : 0 < rank cell (execution.state slot)) :
    ∃ move, pending cell (execution.state slot) = some move ∧
      ∃ value : Execution.Advanced context header (execution.state slot)
          (canonicalAction context header (execution.state slot) move),
        Execution.advance context header (execution.state slot)
          (canonicalAction context header (execution.state slot) move) = .ok value ∧
        serves move value.event = true ∧ rank cell value.outcome.after < rank cell (execution.state slot) := by
  let state := execution.state slot
  have valid := valid_at checked execution initial slot within
  have keyMember := Control.mem_allKeys state.key valid.key
  obtain ⟨edge, present, selected, _, decrease⟩ := cell.ranked.current (cell.graph.index state.key)
    (reachable_at checked cell execution initial slot within) positive
  have control := cell.graph.edge_step (cell.graph.index state.key) edge present
  rw [cell.graph.get_index state.key keyMember] at control
  obtain ⟨value, succeeded, same⟩ := Execution.canonical_lift context header state valid edge.move
    (cell.graph.keys.get edge.target) control
  refine ⟨edge.move, selected, value, succeeded, ?_, ?_⟩
  · simp only [serves, tag, Execution.Advanced.event, canonicalAction_move, R.serves, decide_true]
  · change cell.ranked.rank (cell.graph.index value.outcome.after.key) < cell.ranked.rank (cell.graph.index state.key)
    rw [same, cell.graph.index_key]
    exact decrease

end Netlib.Federation.InFlight.Progress
