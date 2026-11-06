import Netlib.Theory.BoundedProgress

namespace NetlibTest.BoundedProgress

open Netlib.Theory.BoundedProgress

private def advance (state : Nat) (service : Bool) : Nat := if service then state - 1 else state

private def system : Netlib.Protocol.Transition Nat Bool := .ofFunction advance

private def adapter : Adapter Nat Bool Nat where
  system := system
  invariant _ := True
  pending state value := 0 < state ∧ value = state
  enabled state value := 0 < state ∧ value = state
  serves _ action := action = true
  rank := id
  complete state := state = 0
  preserve := by intro before action after safe step; trivial
  nonincrease := by
    intro before action after _ step
    change advance before action = after at step
    change after ≤ before
    cases action <;> simp only [advance, Bool.false_eq_true, ↓reduceIte] at step <;> omega
  demand := by intro state _ positive; exact ⟨state, positive, rfl⟩
  pending_enabled := by intro state value _ pending; exact pending
  persistent := by
    intro before action after value _ _ same pending
    change after = before at same
    simpa only [same] using pending
  advance := by
    intro before action after value _ step pending _ served
    change action = true at served
    change advance before action = after at step
    subst action
    simp only [advance, ↓reduceIte] at step
    have positive := pending.1
    change after < before
    omega
  finished := by intro state _ zero; exact zero

private def alternate (initial : Nat) : Execution system where
  state slot := initial - slot / 2
  action slot := decide (slot % 2 = 1)
  checked := by
    intro slot
    change advance (initial - slot / 2) (decide (slot % 2 = 1)) = initial - (slot + 1) / 2
    by_cases served : slot % 2 = 1
    · simp only [served, decide_true, advance, ↓reduceIte]
      omega
    · simp only [served, decide_false, advance, Bool.false_eq_true, ↓reduceIte]
      omega

private theorem alternate_service (initial : Nat) : (alternate initial : Execution adapter.system).ServiceBound (adapter := adapter) 2 := by
  intro start _ value _ _
  by_cases served : start % 2 = 1
  · exact ⟨0, by omega, by simpa only [adapter, alternate, Nat.add_zero, decide_eq_true_eq] using served⟩
  · refine ⟨1, by omega, ?_⟩
    change decide ((start + 1) % 2 = 1) = true
    simp only [decide_eq_true_eq]
    omega

theorem every_alternating_counter_finishes (initial : Nat) :
    adapter.complete ((alternate initial).state (initial * 2)) := by
  have result := (alternate initial : Execution adapter.system).completes_by (adapter := adapter)
    (by trivial) (alternate_service initial) 0 (Nat.zero_le 0)
  simpa only [adapter, alternate, Nat.zero_add, Nat.zero_div, Nat.sub_zero, id_eq] using result

private def stalled : Execution system where
  state _ := 3
  action _ := false
  checked _ := rfl

theorem stopped_service_is_not_admitted : ¬(stalled : Execution adapter.system).ServiceBound (adapter := adapter) 2 := by
  intro service
  obtain ⟨offset, _, served⟩ := service 0 (Nat.zero_le 0) 3 ⟨by change 0 < 3; decide, rfl⟩
    (by intro offset _; exact ⟨by change 0 < 3; decide, rfl⟩)
  change false = true at served
  contradiction

private def completed : Execution system where
  state _ := 0
  action _ := false
  checked _ := rfl

theorem completed_task_admits_zero_bound : completed.ServiceBound (adapter := adapter) 0 := by
  intro start _ value pending
  have positive := pending.1
  change 0 < 0 at positive
  omega

theorem pending_task_rejects_zero_bound : ¬stalled.ServiceBound (adapter := adapter) 0 := by
  intro service
  obtain ⟨offset, within, _⟩ := service 0 (Nat.zero_le 0) 3 ⟨by change 0 < 3; decide, rfl⟩
    (by intro offset within; omega)
  omega

private def completedPrefix : Prefix system :=
  ⟨0, completed.state, completed.action, fun slot within => False.elim (by omega)⟩

private def pendingPrefix : Prefix system :=
  ⟨0, stalled.state, stalled.action, fun slot within => False.elim (by omega)⟩

theorem completed_empty_prefix_admits_zero_bound : completedPrefix.ServiceBound (adapter := adapter) 0 := by
  intro start _ _ value pending
  have positive := pending.1
  change 0 < 0 at positive
  omega

theorem pending_empty_prefix_rejects_zero_bound : ¬pendingPrefix.ServiceBound (adapter := adapter) 0 := by
  intro service
  obtain ⟨offset, within, _⟩ := service 0 (Nat.zero_le 0) (Nat.le_refl 0) 3
    ⟨by change 0 < 3; decide, rfl⟩ (by intro offset within; omega)
  omega

theorem zero_bound_completes_inside_the_checked_empty_prefix : adapter.complete (completedPrefix.state 0) := by
  exact completedPrefix.completes_by (adapter := adapter) (by trivial)
    completed_empty_prefix_admits_zero_bound 0 (Nat.zero_le 0) (Nat.le_refl 0)

private def pairAdvance (state : Nat × Nat) (action : Bool × Bool) : Nat × Nat :=
  (advance state.1 action.1, advance state.2 action.2)

private def pairSystem : Netlib.Protocol.Transition (Nat × Nat) (Bool × Bool) := .ofFunction pairAdvance

private def leftTask : Adapter (Nat × Nat) (Bool × Bool) Nat :=
  adapter.pullback pairSystem Prod.fst Prod.fst (by
    intro before action after step
    change pairAdvance before action = after at step
    change advance before.1 action.1 = after.1
    exact congrArg Prod.fst step)

private def rightTask : Adapter (Nat × Nat) (Bool × Bool) Nat :=
  adapter.pullback pairSystem Prod.snd Prod.snd (by
    intro before action after step
    change pairAdvance before action = after at step
    change advance before.2 action.2 = after.2
    exact congrArg Prod.snd step)

private def paired : Execution pairSystem where
  state slot := (3 - slot / 2, 2 - slot / 3)
  action slot := (decide (slot % 2 = 1), decide (slot % 3 = 2))
  checked := by
    intro slot
    change pairAdvance (3 - slot / 2, 2 - slot / 3)
      (decide (slot % 2 = 1), decide (slot % 3 = 2)) = (3 - (slot + 1) / 2, 2 - (slot + 1) / 3)
    apply Prod.ext
    · change advance (3 - slot / 2) (decide (slot % 2 = 1)) = 3 - (slot + 1) / 2
      by_cases selected : slot % 2 = 1
      · simp only [selected, decide_true, advance, ↓reduceIte]; omega
      · simp only [selected, decide_false, advance, Bool.false_eq_true, ↓reduceIte]; omega
    · change advance (2 - slot / 3) (decide (slot % 3 = 2)) = 2 - (slot + 1) / 3
      by_cases selected : slot % 3 = 2
      · simp only [selected, decide_true, advance, ↓reduceIte]; omega
      · simp only [selected, decide_false, advance, Bool.false_eq_true, ↓reduceIte]; omega

private theorem paired_left_service : paired.ServiceBound (adapter := leftTask) 2 := by
  intro start _ value _ _
  by_cases selected : start % 2 = 1
  · refine ⟨0, by omega, ?_⟩
    change decide ((start + 0) % 2 = 1) = true
    simp only [decide_eq_true_eq]
    omega
  · refine ⟨1, by omega, ?_⟩
    change decide ((start + 1) % 2 = 1) = true
    simp only [decide_eq_true_eq]
    omega

private theorem paired_right_service : paired.ServiceBound (adapter := rightTask) 3 := by
  intro start _ value _ _
  refine ⟨2 - start % 3, by omega, ?_⟩
  change decide ((start + (2 - start % 3)) % 3 = 2) = true
  simp only [decide_eq_true_eq]
  omega

theorem independent_tasks_finish_by_the_larger_bound :
    leftTask.complete (paired.state 6) ∧ rightTask.complete (paired.state 6) := by
  have result := concurrent leftTask rightTask rfl paired (by trivial) (by trivial)
    paired_left_service paired_right_service
  change leftTask.complete (paired.state 6) ∧ rightTask.complete (paired.state 6) at result
  exact result

private def staged : Execution pairSystem where
  state slot := (3 - slot / 2, 2 - (slot - 6) / 3)
  action slot := (decide (slot % 2 = 1), decide (6 ≤ slot ∧ (slot - 6) % 3 = 2))
  checked := by
    intro slot
    change pairAdvance (3 - slot / 2, 2 - (slot - 6) / 3)
      (decide (slot % 2 = 1), decide (6 ≤ slot ∧ (slot - 6) % 3 = 2)) =
      (3 - (slot + 1) / 2, 2 - (slot + 1 - 6) / 3)
    apply Prod.ext
    · change advance (3 - slot / 2) (decide (slot % 2 = 1)) = 3 - (slot + 1) / 2
      by_cases selected : slot % 2 = 1
      · simp only [selected, decide_true, advance, ↓reduceIte]; omega
      · simp only [selected, decide_false, advance, Bool.false_eq_true, ↓reduceIte]; omega
    · change advance (2 - (slot - 6) / 3) (decide (6 ≤ slot ∧ (slot - 6) % 3 = 2)) =
        2 - (slot + 1 - 6) / 3
      by_cases selected : 6 ≤ slot ∧ (slot - 6) % 3 = 2
      · simp [advance, selected]; omega
      · simp [advance, selected]; omega

private theorem staged_left_service : staged.ServiceBound (adapter := leftTask) 2 := by
  intro start _ value _ _
  by_cases selected : start % 2 = 1
  · refine ⟨0, by omega, ?_⟩
    change decide ((start + 0) % 2 = 1) = true
    simp only [decide_eq_true_eq]
    omega
  · refine ⟨1, by omega, ?_⟩
    change decide ((start + 1) % 2 = 1) = true
    simp only [decide_eq_true_eq]
    omega

private theorem staged_right_service : staged.ServiceFrom (adapter := rightTask) 3 6 := by
  intro start begun value _ _
  refine ⟨2 - (start - 6) % 3, by omega, ?_⟩
  change decide (6 ≤ start + (2 - (start - 6) % 3) ∧
    (start + (2 - (start - 6) % 3) - 6) % 3 = 2) = true
  simp only [decide_eq_true_eq]
  omega

theorem sequential_service_adds_the_bounds :
    leftTask.complete (staged.state 12) ∧ rightTask.complete (staged.state 12) := by
  have result := sequential leftTask rightTask rfl staged (by trivial) (by trivial)
    staged_left_service staged_right_service
  change leftTask.complete (staged.state 12) ∧ rightTask.complete (staged.state 12) at result
  exact result

private def pairedPrefix : Prefix pairSystem :=
  ⟨6, paired.state, paired.action, fun slot _ => paired.checked slot⟩

theorem finite_independent_tasks_finish_inside_the_prefix :
    leftTask.complete (pairedPrefix.state 6) ∧ rightTask.complete (pairedPrefix.state 6) := by
  have leftService : pairedPrefix.ServiceBound (adapter := leftTask) 2 := by
    intro start begun _ value initialPending pending
    exact paired_left_service start begun value initialPending pending
  have rightService : pairedPrefix.ServiceBound (adapter := rightTask) 3 := by
    intro start begun _ value initialPending pending
    exact paired_right_service start begun value initialPending pending
  have result := Prefix.concurrent leftTask rightTask rfl pairedPrefix (by trivial) (by trivial)
    leftService rightService (by decide)
  change leftTask.complete (pairedPrefix.state 6) ∧ rightTask.complete (pairedPrefix.state 6) at result
  exact result

private def stagedPrefix : Prefix pairSystem :=
  ⟨12, staged.state, staged.action, fun slot _ => staged.checked slot⟩

theorem finite_sequential_tasks_finish_inside_the_prefix :
    leftTask.complete (stagedPrefix.state 12) ∧ rightTask.complete (stagedPrefix.state 12) := by
  have leftService : stagedPrefix.ServiceBound (adapter := leftTask) 2 := by
    intro start begun _ value initialPending pending
    exact staged_left_service start begun value initialPending pending
  have rightService : stagedPrefix.ServiceFrom (adapter := rightTask) 3 6 := by
    intro start begun _ value initialPending pending
    exact staged_right_service start begun value initialPending pending
  have result := Prefix.sequential leftTask rightTask rfl stagedPrefix (by trivial) (by trivial)
    leftService rightService (by decide)
  change leftTask.complete (stagedPrefix.state 12) ∧ rightTask.complete (stagedPrefix.state 12) at result
  exact result

theorem finite_second_rank_comes_from_the_actual_cut :
    leftTask.complete (stagedPrefix.state 12) ∧ rightTask.complete (stagedPrefix.state 12) := by
  have leftService : stagedPrefix.ServiceBound (adapter := leftTask) 2 := by
    intro start begun _ value initialPending pending
    exact staged_left_service start begun value initialPending pending
  have rightService : (stagedPrefix.suffix 6).ServiceBound (adapter := rightTask) 3 := by
    intro start _ _ value initialPending pending
    have selected := staged_right_service (6 + start) (by omega) value
      (by simpa only [Prefix.suffix, Nat.add_zero, stagedPrefix] using initialPending) (by
      intro offset within
      simpa only [Prefix.suffix, Nat.add_assoc, stagedPrefix] using pending offset within)
    simpa only [Prefix.suffix, Nat.add_assoc, stagedPrefix] using selected
  have result := Prefix.sequential_at_cut leftTask rightTask rfl stagedPrefix (by trivial) leftService
    (by trivial) rightService (by decide)
  change leftTask.complete (stagedPrefix.state 12) ∧ rightTask.complete (stagedPrefix.state 12) at result
  exact result

private def sample (initial : Nat) (actions : List Bool) : Prefix system where
  length := actions.length
  state slot := (actions.take slot).foldl advance initial
  action slot := actions[slot]?.getD false
  checked := by
    intro slot within
    change advance ((actions.take slot).foldl advance initial) (actions[slot]?.getD false) =
      (actions.take (slot + 1)).foldl advance initial
    rw [List.take_succ_eq_append_getElem within, List.getElem?_eq_getElem within, List.foldl_append]
    rfl

example (initial : Nat) (actions : List Bool) (service : (sample initial actions : Prefix adapter.system).ServiceBound (adapter := adapter) 2)
    (longEnough : initial * 2 ≤ actions.length) :
    (sample initial actions).state (initial * 2) = 0 := by
  have complete := (sample initial actions : Prefix adapter.system).completes_by (adapter := adapter)
    (by trivial) service 0 (Nat.zero_le 0)
    (by simpa only [sample, adapter, List.take_zero, List.foldl_nil, id_eq, Nat.zero_add] using longEnough)
  simpa only [adapter, sample, Nat.zero_add, List.take_zero, List.foldl_nil, id_eq] using complete

private def serviceCheck (initial : Nat) (actions : List Bool) (bound : Nat) : Bool :=
  let execution := sample initial actions
  (List.range (actions.length + 1)).all fun start =>
    if start + bound ≤ actions.length then
      (List.range initial).all fun index =>
        let value := index + 1
        let pending := decide (0 < execution.state start ∧ value = execution.state start) &&
          (List.range bound).all fun offset =>
            decide (0 < execution.state (start + offset) ∧ value = execution.state (start + offset))
        !pending || (List.range bound).any fun offset => execution.action (start + offset)
    else true

private def schedules : Nat → List (List Bool)
  | 0 => [[]]
  | count + 1 => (schedules count).flatMap fun tail => [false :: tail, true :: tail]

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  ensure (serviceCheck 0 [] 0 && !serviceCheck 3 [] 0 && !serviceCheck 3 (List.replicate 6 false) 0)
    "A zero-slot bound must admit an empty task and reject pending work."
  ensure (paired.state 6 == (0, 0) && staged.state 6 == (0, 2) && staged.state 12 == (0, 0))
    "Concurrent service must use the larger bound; service in sequence must add the bounds."
  let samples := schedules 6
  let admitted := samples.filter (serviceCheck 3 · 2)
  ensure (samples.length == 64 && !admitted.isEmpty && admitted.length < samples.length)
    "The bounded-service test must accept and reject actual finite schedules."
  for actions in admitted do
    ensure ((sample 3 actions).state 6 == 0)
      "Every admitted six-slot schedule must finish the three-step task."
  ensure (!serviceCheck 3 (List.replicate 6 false) 2 && (sample 3 (List.replicate 6 false)).state 6 == 3)
    "Omitted service must leave actual work pending and fail the service condition."
  ensure (serviceCheck 3 [false, true, false, true, false, true] 2 &&
      !serviceCheck 3 [false, true, false, true, false, true] 1)
    "The same schedule can satisfy a two-slot bound and fail a one-slot bound."
  ensure ((sample 3 [true]).state 1 == 2 && 3 * 2 > (sample 3 [true]).length)
    "A short execution must not establish a completion bound beyond its checked sample."
  ensure ((sample 3 [true, true, true, false, false, false]).state 6 == 0 &&
      serviceCheck 3 [true, true, true, false, false, false] 2)
    "A completed task must permit later idle slots without a new demand."

end NetlibTest.BoundedProgress
