import Netlib.Check.FederatedCohortGraph

/-!
# Cohort descent inherited from checked packet components

Component positions carry exact key equality and checked-table reachability.
The remaining-update term also gives progress for an empty cohort.
-/

namespace Netlib.Federation.Cohort.Potential

variable {input : Input} {size : Nat} {context : Context input size}
variable (family : Family context) (headers : Vector Packet.Header size) (accepted : Accepted context headers)

theorem rank_eq (before after : Key input size)
    (beforeReached : (Graph.model context headers).network.Reachable (initialKey context) before)
    (afterReached : (Graph.model context headers).network.Reachable (initialKey context) after)
    (index : Fin size) (same : after.packet index = before.packet index) :
    Graph.componentRank family headers accepted after afterReached index =
      Graph.componentRank family headers accepted before beforeReached index := by
  let first := Graph.position family headers accepted before beforeReached index
  let last := Graph.position family headers accepted after afterReached index
  have positions : last.index = first.index :=
    (family.cell headers accepted index).graph.key_injective _ _ (last.keyEq.trans (same.trans first.keyEq.symm))
  exact congrArg (family.cell headers accepted index).ranked.rank positions

theorem component_strict (before after : Key input size)
    (beforeReached : (Graph.model context headers).network.Reachable (initialKey context) before)
    (afterReached : (Graph.model context headers).network.Reachable (initialKey context) after)
    (index : Fin size) (move : InFlight.Move)
    (selected : InFlight.Control.step (context.packets.get index) (headers.get index)
      (before.packet index) move = some (after.packet index)) :
    Graph.componentRank family headers accepted after afterReached index <
      Graph.componentRank family headers accepted before beforeReached index := by
  let cell := family.cell headers accepted index
  let first := Graph.position family headers accepted before beforeReached index
  let last := Graph.position family headers accepted after afterReached index
  have step := (cell.graph.progress_iff first.index last.index move).mpr (by rw [first.keyEq, last.keyEq]; exact selected)
  have member := (cell.ranked.reachable_exact first.index).mpr first.reached
  obtain ⟨edge, present, _, same⟩ := step
  have decrease := (cell.ranked.progress first.index member edge present).2
  change cell.ranked.rank last.index < cell.ranked.rank first.index
  simpa only [same] using decrease

theorem component_nonincrease (before after : Key input size)
    (beforeReached : (Graph.model context headers).network.Reachable (initialKey context) before)
    (afterReached : (Graph.model context headers).network.Reachable (initialKey context) after)
    (move : Move size) (selected : Control.step context headers before move = some after) (index : Fin size) :
    Graph.componentRank family headers accepted after afterReached index ≤
      Graph.componentRank family headers accepted before beforeReached index := by
  have facts := (Control.step_facts context headers before after move selected).localSteps index
  cases chosen : move.local index with
  | none =>
    have same : after.packet index = before.packet index := by simpa only [chosen] using facts
    exact Nat.le_of_eq (rank_eq family headers accepted before after beforeReached afterReached index same)
  | some action =>
    exact Nat.le_of_lt (component_strict family headers accepted before after beforeReached afterReached index action
      (by simpa only [chosen] using facts))

theorem component_zero_iff (key : Key input size)
    (reached : (Graph.model context headers).network.Reachable (initialKey context) key) (index : Fin size) :
    Graph.componentRank family headers accepted key reached index = 0 ↔ InFlight.finished (key.packet index) = true := by
  let cell := family.cell headers accepted index
  let position := Graph.position family headers accepted key reached index
  have zero := cell.ranked.zero_iff position.index ((cell.ranked.reachable_exact position.index).mpr position.reached)
  rw [cell.graph.doneEq, position.keyEq] at zero
  exact zero

theorem remaining_zero_iff (key : Key input size) : Graph.remaining key = 0 ↔
    key.current.1.val = input.left.updates.length ∧ key.current.2.val = input.right.updates.length := by
  have left := key.current.1.isLt
  have right := key.current.2.isLt
  simp only [Plan.versions, List.length_cons] at left right
  unfold Graph.remaining
  omega

private theorem sum_le (values : List α) (first last : α → Nat)
    (bound : ∀ index ∈ values, first index ≤ last index) : (values.map first).sum ≤ (values.map last).sum := by
  induction values with
  | nil => simp
  | cons index rest ih =>
    have head := bound index (by simp)
    have tail := ih (fun next member => bound next (List.mem_cons_of_mem _ member))
    simp only [List.map_cons, List.sum_cons]
    omega

private theorem sum_strict (values : List α) (first last : α → Nat)
    (bound : ∀ index ∈ values, first index ≤ last index) (chosen : α) (member : chosen ∈ values)
    (strict : first chosen < last chosen) : (values.map first).sum < (values.map last).sum := by
  induction values with
  | nil => simp at member
  | cons index rest ih =>
    have head := bound index (by simp)
    have tail := sum_le rest first last (fun next present => bound next (List.mem_cons_of_mem _ present))
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp member with same | present
    · subst chosen; omega
    · have less := ih (fun next present => bound next (List.mem_cons_of_mem _ present)) present
      omega

theorem zero_iff_finished (key : Key input size)
    (reached : (Graph.model context headers).network.Reachable (initialKey context) key) :
    Graph.potential family headers accepted key reached = 0 ↔ finished key = true := by
  constructor
  · intro zero
    have sumZero : ((List.finRange size).map (Graph.componentRank family headers accepted key reached)).sum = 0 := by
      unfold Graph.potential at zero
      omega
    have remainingZero : Graph.remaining key = 0 := by unfold Graph.potential at zero; omega
    have allZero := List.sum_eq_zero_iff_forall_eq_nat.mp sumZero
    apply (Bool.and_eq_true _ _).mpr
    constructor
    · apply List.all_eq_true.mpr
      intro index member
      have rankZero := allZero _ (List.mem_map.mpr ⟨index, member, rfl⟩)
      have done := (component_zero_iff family headers accepted key reached index).mp rankZero
      have facts : key.phases.get index = .delivered ∧
          key.current.1.val = input.left.updates.length ∧ key.current.2.val = input.right.updates.length := by
        exact of_decide_eq_true done
      exact decide_eq_true facts.1
    · exact decide_eq_true ((remaining_zero_iff key).mp remainingZero)
  · intro done
    have facts : (∀ index ∈ List.finRange size, key.phases.get index = .delivered) ∧
        key.current.1.val = input.left.updates.length ∧ key.current.2.val = input.right.updates.length := by
      simpa only [finished, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] using done
    have sumZero : ((List.finRange size).map (Graph.componentRank family headers accepted key reached)).sum = 0 := by
      apply List.sum_eq_zero_iff_forall_eq_nat.mpr
      intro amount member
      obtain ⟨index, present, same⟩ := List.mem_map.mp member
      rw [← same]
      apply (component_zero_iff family headers accepted key reached index).mpr
      exact decide_eq_true ⟨facts.1 index present, facts.2⟩
    have remainingZero := (remaining_zero_iff key).mpr facts.2
    exact Nat.add_eq_zero_iff.mpr ⟨sumZero, remainingZero⟩

private theorem packet_current (before after : Key input size) (index : Fin size) (move : PacketMove)
    (selected : Control.rawStep context before (.packet index move) = some after) : after.current = before.current := by
  cases move <;> cases phase : before.phases.get index <;> simp only [Control.rawStep, phase] at selected
  all_goals repeat' first | split at selected | (solve | cases selected) | (solve | cases selected; rfl)

def updateCount : Move size → Nat
  | .packet _ _ => 0
  | .updateLeft _ | .updateRight _ => 1
  | .updateBoth _ _ => 2

theorem remaining_step (before after : Key input size) (move : Move size)
    (selected : Control.rawStep context before move = some after) :
    Graph.remaining after + updateCount move = Graph.remaining before := by
  have left := before.current.1.isLt
  have right := before.current.2.isLt
  simp only [Plan.versions, List.length_cons] at left right
  cases move with
  | packet index action =>
    simp only [Graph.remaining, packet_current before after index action selected, updateCount, Nat.add_zero]
  | updateLeft index =>
    cases next : InFlight.Control.nextCursor input.left before.current.1 index with
    | none => simp [Control.rawStep, next] at selected
    | some cursor =>
      have advanced := (InFlight.Control.nextCursor_step input.left before.current.1 cursor index next).2
      have within := cursor.isLt
      simp only [Plan.versions, List.length_cons] at within
      simp [Control.rawStep, next] at selected
      subst after
      simp only [Graph.remaining, updateCount]
      change cursor.val = before.current.1.val + 1 at advanced
      omega
  | updateRight index =>
    cases next : InFlight.Control.nextCursor input.right before.current.2 index with
    | none => simp [Control.rawStep, next] at selected
    | some cursor =>
      have advanced := (InFlight.Control.nextCursor_step input.right before.current.2 cursor index next).2
      have within := cursor.isLt
      simp only [Plan.versions, List.length_cons] at within
      simp [Control.rawStep, next] at selected
      subst after
      simp only [Graph.remaining, updateCount]
      change cursor.val = before.current.2.val + 1 at advanced
      omega
  | updateBoth first second =>
    cases nextLeft : InFlight.Control.nextCursor input.left before.current.1 first with
    | none => simp [Control.rawStep, nextLeft] at selected
    | some leftCursor =>
      cases nextRight : InFlight.Control.nextCursor input.right before.current.2 second with
      | none => simp [Control.rawStep, nextLeft, nextRight] at selected
      | some rightCursor =>
        have advancedLeft := (InFlight.Control.nextCursor_step input.left before.current.1 leftCursor first nextLeft).2
        have advancedRight := (InFlight.Control.nextCursor_step input.right before.current.2 rightCursor second nextRight).2
        have withinLeft := leftCursor.isLt
        have withinRight := rightCursor.isLt
        simp only [Plan.versions, List.length_cons] at withinLeft withinRight
        simp [Control.rawStep, nextLeft, nextRight] at selected
        subst after
        simp only [Graph.remaining, updateCount]
        change leftCursor.val = before.current.1.val + 1 at advancedLeft
        change rightCursor.val = before.current.2.val + 1 at advancedRight
        omega

theorem step_strict (before after : Key input size)
    (beforeReached : (Graph.model context headers).network.Reachable (initialKey context) before)
    (afterReached : (Graph.model context headers).network.Reachable (initialKey context) after)
    (move : Move size) (selected : Control.step context headers before move = some after) :
    Graph.potential family headers accepted after afterReached < Graph.potential family headers accepted before beforeReached := by
  have bound := component_nonincrease family headers accepted before after beforeReached afterReached move selected
  have sums := sum_le (List.finRange size) _ _ (fun index _ => bound index)
  have updates := remaining_step before after move (Control.step_facts context headers before after move selected).raw
  unfold Graph.potential
  cases move with
  | packet index action =>
    have localStep := (Control.step_facts context headers before after (.packet index action) selected).localSteps index
    have strict := component_strict family headers accepted before after beforeReached afterReached index action.local
      (by simpa only [Move.local, ↓reduceIte] using localStep)
    have less := sum_strict (List.finRange size) _ _ (fun index _ => bound index) index (List.mem_finRange index) strict
    simp only [updateCount, Nat.add_zero] at updates
    omega
  | updateLeft index => simp only [updateCount] at updates; omega
  | updateRight index => simp only [updateCount] at updates; omega
  | updateBoth first second => simp only [updateCount] at updates; omega

theorem idle_preserves (before after : Key input size)
    (beforeReached : (Graph.model context headers).network.Reachable (initialKey context) before)
    (afterReached : (Graph.model context headers).network.Reachable (initialKey context) after) (idle : after = before) :
    Graph.potential family headers accepted after afterReached = Graph.potential family headers accepted before beforeReached := by
  subst after
  rfl

def phi (value : Graph.Checked family headers accepted) (index : Fin value.sparse.graph.size) : Nat :=
  Graph.potential family headers accepted (value.sparse.graph.keys.get index) (value.sparse.graph.keySound index)

theorem phi_zero_iff (value : Graph.Checked family headers accepted) (index : Fin value.sparse.graph.size) :
    phi family headers accepted value index = 0 ↔ value.sparse.graph.table.done index = true := by
  rw [value.sparse.graph.doneEq]
  exact zero_iff_finished family headers accepted _ _

theorem edge_strict (value : Graph.Checked family headers accepted) (before : Fin value.sparse.graph.size)
    (edge : Theory.FiniteProgressRank.Edge (Move size) value.sparse.graph.size)
    (present : edge ∈ value.sparse.graph.table.row before) :
    phi family headers accepted value edge.target < phi family headers accepted value before := by
  have member := value.sparse.graph.edge_sound before edge present
  exact step_strict family headers accepted _ _ _ _ edge.move
    ((Control.mem_successors context headers _ _ edge.move).mp member)

theorem nonincrease (value : Graph.Checked family headers accepted) {before after : Fin value.sparse.graph.size}
    {event : Theory.FiniteProgressRank.Event (Move size)} (step : value.sparse.graph.table.system.step before event after) :
    phi family headers accepted value after ≤ phi family headers accepted value before := by
  cases event with
  | idle => exact step ▸ Nat.le_refl _
  | progress move =>
    obtain ⟨edge, present, _, same⟩ := step
    have decrease := edge_strict family headers accepted value before edge present
    rw [same] at decrease
    exact Nat.le_of_lt decrease

theorem equal_idle (value : Graph.Checked family headers accepted) {before after : Fin value.sparse.graph.size}
    {event : Theory.FiniteProgressRank.Event (Move size)} (step : value.sparse.graph.table.system.step before event after)
    (same : phi family headers accepted value after = phi family headers accepted value before) :
    event = .idle ∧ after = before := by
  cases event with
  | idle => exact ⟨rfl, step⟩
  | progress move =>
    obtain ⟨edge, present, _, target⟩ := step
    have decrease := edge_strict family headers accepted value before edge present
    rw [target] at decrease
    omega

theorem current (value : Graph.Checked family headers accepted) (index : Fin value.sparse.graph.size)
    (positive : 0 < phi family headers accepted value index) :
    ∃ edge ∈ value.sparse.graph.table.row index, value.sparse.graph.table.pending index = some edge.move ∧
      Control.step context headers (value.sparse.graph.keys.get index) edge.move =
        some (value.sparse.graph.keys.get edge.target) ∧
      phi family headers accepted value edge.target < phi family headers accepted value index := by
  have unfinished : value.sparse.graph.table.done index = false := by
    cases done : value.sparse.graph.table.done index with
    | false => rfl
    | true => have zero := (phi_zero_iff family headers accepted value index).mpr done; omega
  obtain ⟨edge, present, pending, selected⟩ := value.sparse.live.current index unfinished
  exact ⟨edge, present, pending, (Control.mem_successors context headers _ _ edge.move).mp selected,
    edge_strict family headers accepted value index edge present⟩

end Netlib.Federation.Cohort.Potential
