import Netlib.Check.FederatedCohortPotential
import Netlib.Check.FederatedCohortProjection
import Netlib.Theory.BoundedServiceRank

/-!
# Actual cohort progress under one joint service contract

Every recorded cut has an exact sparse index. Numeric lookups outside that
domain return no demand; the modeled prefix never uses a missing index.
-/

namespace Netlib.Federation.Cohort.Progress

namespace B
export Theory.BoundedProgress (Prefix)
end B

namespace R
export Theory.FiniteProgressRank (Event serves)
end R

variable {input : Input} {size : Nat} {context : Context input size}
variable {family : Family context} {headers : Vector Packet.Header size} {accepted : Accepted context headers}

def lookup (value : Graph.Checked family headers accepted) (state : State input size) : Option (Fin value.sparse.graph.size) :=
  Theory.FiniteSuccessorGraph.findIndex value.sparse.graph.keys state.key

def pending (value : Graph.Checked family headers accepted) (state : State input size) : Option (Move size) :=
  (lookup value state).bind value.sparse.graph.table.pending

def rank? (value : Graph.Checked family headers accepted) (state : State input size) : Option Nat :=
  (lookup value state).map (Potential.phi family headers accepted value)

/-- Actual cuts always have a successful lookup; zero totalizes other states. -/
def rank (value : Graph.Checked family headers accepted) (state : State input size) : Nat := (rank? value state).getD 0

def tag (context : Context input size) (event : Cohort.Event input size) : R.Event (Move size) :=
  match actionMove context event.action with
  | .ok (some move) => .progress move
  | _ => .idle

def serves (context : Context input size) (move : Move size) (event : Cohort.Event input size) : Bool :=
  R.serves move (tag context event)

def deadline (value : Graph.Checked family headers accepted) (bound : Nat) : Nat :=
  Potential.phi family headers accepted value value.sparse.graph.table.initial * bound

def Complete (state : State input size) : Prop :=
  (∀ index, ∃ receipt, state.phases.get index = .delivered receipt) ∧
    state.current.1.val = input.left.updates.length ∧ state.current.2.val = input.right.updates.length

private theorem phase_delivered (phase : InFlight.Phase input) :
    phase.key = .delivered ↔ ∃ index, phase = .delivered index := by
  cases phase <;> simp [InFlight.Phase.key]

theorem finished_iff (state : State input size) : finished state.key = true ↔ Complete state := by
  have mapped : ∀ index : Fin size, state.key.phases.get index = (state.phases.get index).key := by
    intro index
    change (state.phases.map InFlight.Phase.key)[index.val] = InFlight.Phase.key state.phases[index.val]
    simp only [Vector.getElem_map]
  constructor
  · intro done
    have facts := (Bool.and_eq_true _ _).mp done
    refine ⟨fun index => ?_, (of_decide_eq_true facts.2)⟩
    have phase := of_decide_eq_true (List.all_eq_true.mp facts.1 index (List.mem_finRange index))
    rw [mapped index] at phase
    exact (phase_delivered _).mp phase
  · rintro ⟨received, cursors⟩
    apply (Bool.and_eq_true _ _).mpr
    refine ⟨List.all_eq_true.mpr (fun index _ => ?_), decide_eq_true cursors⟩
    exact decide_eq_true (by rw [mapped index]; exact (phase_delivered _).mpr (received index))

@[simp] theorem initial_key : (initialState context).key = initialKey context := by
  simp [initialState, State.key, initialKey, Vector.map_map, Function.comp_def, InFlight.Phase.key]

theorem initial_valid (value : Graph.Checked family headers accepted) : (initialState context).Valid context headers := by
  refine ⟨?_, fun index => ?_⟩
  · rw [initial_key]
    exact value.initialGood
  · rw [initialState_packet]
    let component := family.component index
    have valid := InFlight.initial_valid component.certificate.valid (headers.get index)
    simpa only [component.contextEq] using valid

theorem valid_at (value : Graph.Checked family headers accepted) (execution : B.Prefix (Execution.system context headers))
    (initial : execution.state 0 = initialState context) (slot : Nat) (within : slot ≤ execution.length) :
    (execution.state slot).Valid context headers := by
  induction slot with
  | zero => rw [initial]; exact initial_valid value
  | succ slot ih => exact Execution.step_valid context headers (ih (by omega)) (execution.checked slot (by omega))

theorem clock_at (execution : B.Prefix (Execution.system context headers))
    (initial : execution.state 0 = initialState context) (slot : Nat) (within : slot ≤ execution.length) :
    (execution.state slot).nextIndex = slot := by
  induction slot with
  | zero => rw [initial]; rfl
  | succ slot ih => rw [Execution.step_tick context headers (execution.checked slot (by omega)), ih (by omega)]

theorem key_reachable_at (execution : B.Prefix (Execution.system context headers))
    (initial : execution.state 0 = initialState context) (slot : Nat) (within : slot ≤ execution.length) :
    (Graph.model context headers).network.Reachable (initialKey context) (execution.state slot).key := by
  induction slot with
  | zero => rw [initial, initial_key]; exact .refl _
  | succ slot ih =>
    have previous := ih (by omega)
    obtain ⟨outcome, facts, stateEq, _⟩ := Execution.step_facts context headers (execution.checked slot (by omega))
    obtain ⟨move, _, selected⟩ := facts.keyStep
    rw [stateEq] at selected
    cases move with
    | none => exact selected ▸ previous
    | some operation => exact previous.trans (.single ⟨operation, (Control.mem_successors context headers _ _ operation).mpr selected⟩)

def indexAt (value : Graph.Checked family headers accepted) (execution : B.Prefix (Execution.system context headers))
    (initial : execution.state 0 = initialState context) (slot : Nat) : Fin value.sparse.graph.size :=
  if within : slot ≤ execution.length then
    value.sparse.graph.index (execution.state slot).key (key_reachable_at execution initial slot within)
  else value.sparse.graph.table.initial

theorem indexAt_key (value : Graph.Checked family headers accepted) (execution : B.Prefix (Execution.system context headers))
    (initial : execution.state 0 = initialState context) (slot : Nat) (within : slot ≤ execution.length) :
    value.sparse.graph.keys.get (indexAt value execution initial slot) = (execution.state slot).key := by
  simp only [indexAt, dite_eq_left within]
  exact value.sparse.graph.get_index _ _

theorem lookup_known (value : Graph.Checked family headers accepted) (state : State input size)
    (index : Fin value.sparse.graph.size) (same : value.sparse.graph.keys.get index = state.key) : lookup value state = some index := by
  obtain ⟨found, selected⟩ := Theory.FiniteSuccessorGraph.findIndex_exists value.sparse.graph.keys state.key (by
    rw [← same]
    exact value.sparse.graph.key_mem index)
  have equal := value.sparse.graph.key_injective found index
    ((Theory.FiniteSuccessorGraph.findIndex_sound value.sparse.graph.keys state.key found selected).trans same.symm)
  simpa only [lookup, equal] using selected

theorem lookup_at (value : Graph.Checked family headers accepted) (execution : B.Prefix (Execution.system context headers))
    (initial : execution.state 0 = initialState context) (slot : Nat) (within : slot ≤ execution.length) :
    lookup value (execution.state slot) = some (indexAt value execution initial slot) :=
  lookup_known value _ _ (indexAt_key value execution initial slot within)

theorem rank_known (value : Graph.Checked family headers accepted) (state : State input size)
    (index : Fin value.sparse.graph.size) (same : value.sparse.graph.keys.get index = state.key) :
    rank value state = Potential.phi family headers accepted value index := by
  simp only [rank, rank?, lookup_known value state index same, Option.map_some, Option.getD_some]

theorem rank_initial (value : Graph.Checked family headers accepted) :
    rank value (initialState context) = Potential.phi family headers accepted value value.sparse.graph.table.initial :=
  rank_known value _ _ (value.sparse.graph.initialEq.trans initial_key.symm)

theorem reachable_at (value : Graph.Checked family headers accepted) (execution : B.Prefix (Execution.system context headers))
    (initial : execution.state 0 = initialState context) (slot : Nat) (within : slot ≤ execution.length) :
    value.sparse.graph.table.network.Reachable value.sparse.graph.table.initial (indexAt value execution initial slot) := by
  simp only [indexAt, dite_eq_left within]
  exact value.sparse.graph.reachable _

theorem pending_at (value : Graph.Checked family headers accepted) (execution : B.Prefix (Execution.system context headers))
    (initial : execution.state 0 = initialState context) (slot : Nat) (within : slot ≤ execution.length) :
    pending value (execution.state slot) = value.sparse.graph.table.pending (indexAt value execution initial slot) := by
  simp only [pending, lookup_at value execution initial slot within, Option.bind_some]

theorem rank_at (value : Graph.Checked family headers accepted) (execution : B.Prefix (Execution.system context headers))
    (initial : execution.state 0 = initialState context) (slot : Nat) (within : slot ≤ execution.length) :
    rank value (execution.state slot) = Potential.phi family headers accepted value (indexAt value execution initial slot) := by
  simp only [rank, rank?, lookup_at value execution initial slot within, Option.map_some, Option.getD_some]

def projectedPrefix (value : Graph.Checked family headers accepted) (execution : B.Prefix (Execution.system context headers))
    (initial : execution.state 0 = initialState context) : B.Prefix value.sparse.graph.table.system where
  length := execution.length
  state := indexAt value execution initial
  action slot := tag context (execution.action slot)
  checked slot within := by
    obtain ⟨outcome, facts, stateEq, _⟩ := Execution.step_facts context headers (execution.checked slot within)
    obtain ⟨move, classified, selected⟩ := facts.keyStep
    rw [stateEq] at selected
    cases move with
    | none =>
      simp only [tag, classified]
      apply value.sparse.graph.key_injective
      rw [indexAt_key value execution initial (slot + 1) (by omega), indexAt_key value execution initial slot (by omega)]
      exact selected
    | some operation =>
      simp only [tag, classified]
      apply (value.sparse.graph.progress_iff _ _ operation).mpr
      rw [indexAt_key value execution initial slot (by omega), indexAt_key value execution initial (slot + 1) (by omega)]
      exact (Control.mem_successors context headers _ _ operation).mpr selected

theorem projected_initial (value : Graph.Checked family headers accepted) (execution : B.Prefix (Execution.system context headers))
    (initial : execution.state 0 = initialState context) :
    (projectedPrefix value execution initial).state 0 = value.sparse.graph.table.initial := by
  apply value.sparse.graph.key_injective
  change value.sparse.graph.keys.get (indexAt value execution initial 0) = value.sparse.graph.keys.get value.sparse.graph.table.initial
  rw [indexAt_key value execution initial 0 (Nat.zero_le _), initial, initial_key, value.sparse.graph.initialEq]
  rfl

theorem zero_iff_complete (value : Graph.Checked family headers accepted) (execution : B.Prefix (Execution.system context headers))
    (initial : execution.state 0 = initialState context) (slot : Nat) (within : slot ≤ execution.length) :
    rank value (execution.state slot) = 0 ↔ Complete (execution.state slot) := by
  rw [rank_at value execution initial slot within, Potential.phi_zero_iff,
    value.sparse.graph.doneEq, indexAt_key value execution initial slot within]
  exact finished_iff _

theorem modeled_completion (value : Graph.Checked family headers accepted)
    (execution : B.Prefix (Execution.system context headers)) (initial : execution.state 0 = initialState context)
    (bound : Nat) (_positive : 0 < bound)
    (service : Theory.BoundedServiceCheck.Serviced execution.length (fun slot => pending value (execution.state slot))
      execution.action (serves context) bound) (enough : deadline value bound ≤ execution.length) :
    Complete (execution.state (deadline value bound)) := by
  let projected := projectedPrefix value execution initial
  let phi := fun slot => Potential.phi family headers accepted value (projected.state slot)
  have initialIndex : projected.state 0 = value.sparse.graph.table.initial := projected_initial value execution initial
  have serviced : Theory.BoundedServiceCheck.Serviced projected.length
      (fun slot => value.sparse.graph.table.pending (projected.state slot)) projected.action R.serves bound := by
    intro start within move selected persistent
    change start + bound ≤ execution.length at within
    obtain ⟨offset, inside, served⟩ := service start within move
      (by
        change pending value (execution.state start) = some move
        rw [pending_at value execution initial start (by omega)]
        exact selected)
      (fun offset inside => by
        change pending value (execution.state (start + offset)) = some move
        rw [pending_at value execution initial (start + offset) (by omega)]
        exact persistent offset inside)
    exact ⟨offset, inside, served⟩
  have nonincrease : ∀ slot, slot < projected.length → phi (slot + 1) ≤ phi slot := by
    intro slot within
    exact Potential.nonincrease family headers accepted value (projected.checked slot within)
  have demand : ∀ slot, slot ≤ projected.length → 0 < phi slot →
      ∃ move, value.sparse.graph.table.pending (projected.state slot) = some move := by
    intro slot _ positive
    obtain ⟨edge, _, selected, _, _⟩ := Potential.current family headers accepted value (projected.state slot) positive
    exact ⟨edge.move, selected⟩
  have persistent : ∀ slot, slot < projected.length → 0 < phi slot → ∀ move,
      phi (slot + 1) = phi slot → value.sparse.graph.table.pending (projected.state slot) = some move →
        value.sparse.graph.table.pending (projected.state (slot + 1)) = some move := by
    intro slot within _ move equal selected
    have same := Potential.equal_idle family headers accepted value (projected.checked slot within) equal
    rw [same.2]
    exact selected
  have strict : ∀ slot, slot < projected.length → 0 < phi slot → ∀ move,
      value.sparse.graph.table.pending (projected.state slot) = some move → R.serves move (projected.action slot) = true →
        phi (slot + 1) < phi slot := by
    intro slot within _ move _ served
    have step := projected.checked slot within
    cases event : projected.action slot with
    | idle => simp only [event, R.serves, Bool.false_eq_true] at served
    | progress operation =>
      rw [event] at step
      obtain ⟨edge, present, _, same⟩ := step
      have decrease := Potential.edge_strict family headers accepted value (projected.state slot) edge present
      rw [same] at decrease
      exact decrease
  have enoughPhi : phi 0 * bound ≤ projected.length := by
    change Potential.phi family headers accepted value (projected.state 0) * bound ≤ execution.length
    rw [initialIndex]
    exact enough
  have zero := Theory.BoundedServiceRank.zero_by serviced nonincrease demand persistent strict enoughPhi
  have deadlineEq : phi 0 * bound = deadline value bound := by
    change Potential.phi family headers accepted value (projected.state 0) * bound = deadline value bound
    rw [initialIndex]
    rfl
  rw [deadlineEq] at zero
  have actualZero : rank value (execution.state (deadline value bound)) = 0 := by
    rw [rank_at value execution initial _ enough]
    exact zero
  exact (zero_iff_complete value execution initial _ enough).mp actualZero

theorem current_enabled (value : Graph.Checked family headers accepted) (unique : context.Unique)
    (execution : B.Prefix (Execution.system context headers)) (initial : execution.state 0 = initialState context)
    (slot : Nat) (within : slot ≤ execution.length) (positive : 0 < rank value (execution.state slot)) :
    ∃ move, pending value (execution.state slot) = some move ∧
      ∃ advanced : Execution.Advanced context headers (execution.state slot) (canonicalAction context headers (execution.state slot) move),
        Execution.advance context headers (execution.state slot) (canonicalAction context headers (execution.state slot) move) = .ok advanced ∧
        serves context move advanced.event = true ∧ rank value advanced.outcome.after < rank value (execution.state slot) := by
  have positivePhi : 0 < Potential.phi family headers accepted value (indexAt value execution initial slot) := by
    rw [← rank_at value execution initial slot within]
    exact positive
  obtain ⟨edge, _, selected, step, decrease⟩ := Potential.current family headers accepted value (indexAt value execution initial slot) positivePhi
  rw [indexAt_key value execution initial slot within] at step
  obtain ⟨advanced, succeeded, same⟩ := Execution.canonical_lift context unique headers (execution.state slot)
    (valid_at value execution initial slot within) edge.move (value.sparse.graph.keys.get edge.target) step
  refine ⟨edge.move, ?_, advanced, succeeded, ?_, ?_⟩
  · rw [pending_at value execution initial slot within]
    exact selected
  · simp only [serves, tag, Execution.Advanced.event, actionMove_canonical unique, R.serves, decide_true]
  · have found := lookup_known value advanced.outcome.after edge.target same.symm
    rw [rank_at value execution initial slot within]
    simpa only [rank, rank?, found, Option.map_some, Option.getD_some] using decrease

end Netlib.Federation.Cohort.Progress
