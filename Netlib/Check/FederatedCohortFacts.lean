import Netlib.Check.FederatedCohortProjection

/-!
# Queue conservation and exact FIFO operations

Flights reserve receiver slots. Only a queue head can send or receive, and
arrival appends that packet index to the receiver queue.
-/

namespace Netlib.Federation.Cohort

variable {input : Input} {size : Nat}

theorem nodeIndex_sound (node : InFlight.Node) (index : Fin (InFlight.Control.nodes input).length)
    (found : nodeIndex input node = some index) : nodeAt input index = node :=
  of_decide_eq_true (List.find?_some (p := fun index => decide (nodeAt input index = node)) found)

theorem nodeIndex_exists (node : InFlight.Node) (present : node ∈ InFlight.Control.nodes input) :
    ∃ index, nodeIndex input node = some index := by
  obtain ⟨position, within, selected⟩ := List.mem_iff_getElem.mp present
  let index : Fin (InFlight.Control.nodes input).length := ⟨position, within⟩
  have same : nodeAt input index = node := selected
  cases found : nodeIndex input node with
  | some index => exact ⟨index, rfl⟩
  | none =>
    have absent := List.find?_eq_none.mp found index (List.mem_finRange index)
    exact False.elim (absent (decide_eq_true same))

theorem queueAt_putQueue (queues : Queues input size) (node : InFlight.Node) (values : List (Fin size))
    (present : node ∈ InFlight.Control.nodes input) : queueAt (putQueue queues node values) node = values := by
  obtain ⟨index, found⟩ := nodeIndex_exists node present
  simp [queueAt, putQueue, found, Vector.get, Fin.cast]

namespace Control

theorem good_iff (context : Context input size) (key : Key input size) : good context key = true ↔
    (∀ index, match key.phases.get index with
      | .held node => InFlight.Control.known input key.current node = true ∧
          occurrences key index = 1 ∧ index ∈ queueAt key.queues node
      | .flight node => InFlight.Control.known input key.current node = true ∧ occurrences key index = 0
      | .delivered => occurrences key index = 0) ∧
    ∀ node, (key.queues.get node).Nodup ∧
      (∀ index ∈ key.queues.get node, key.phases.get index = .held (nodeAt input node)) ∧
      (key.queues.get node).length + reservations key (nodeAt input node) ≤ context.capacities.get node := by
  simp only [good, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const]
  constructor
  · rintro ⟨packets, queues⟩
    constructor
    · intro index
      have checked := packets index
      cases phase : key.phases.get index <;> simpa only [phase, Bool.and_eq_true, decide_eq_true_eq] using checked
    · intro node
      have checked := queues node
      simpa only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc] using checked
  · rintro ⟨packets, queues⟩
    constructor
    · intro index
      have checked := packets index
      cases phase : key.phases.get index <;> simpa only [phase, Bool.and_eq_true, decide_eq_true_eq] using checked
    · intro node
      have checked := queues node
      simpa only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc] using checked

theorem held_conserved (context : Context input size) (key : Key input size) (good : good context key = true)
    (index : Fin size) (node : InFlight.Node) (held : key.phases.get index = .held node) :
    InFlight.Control.known input key.current node = true ∧ occurrences key index = 1 ∧ index ∈ queueAt key.queues node := by
  simpa only [held] using ((good_iff context key).mp good).1 index

theorem flight_conserved (context : Context input size) (key : Key input size) (good : good context key = true)
    (index : Fin size) (node : InFlight.Node) (flight : key.phases.get index = .flight node) :
    InFlight.Control.known input key.current node = true ∧ occurrences key index = 0 := by
  simpa only [flight] using ((good_iff context key).mp good).1 index

theorem delivered_conserved (context : Context input size) (key : Key input size) (good : good context key = true)
    (index : Fin size) (delivered : key.phases.get index = .delivered) : occurrences key index = 0 := by
  simpa only [delivered] using ((good_iff context key).mp good).1 index

theorem queue_facts (context : Context input size) (key : Key input size) (good : good context key = true)
    (node : Fin (InFlight.Control.nodes input).length) :
    (key.queues.get node).Nodup ∧
      (∀ index ∈ key.queues.get node, key.phases.get index = .held (nodeAt input node)) ∧
      (key.queues.get node).length + reservations key (nodeAt input node) ≤ context.capacities.get node :=
  ((good_iff context key).mp good).2 node

theorem occupancy_le_capacity (context : Context input size) (key : Key input size) (good : good context key = true)
    (node : InFlight.Node) (present : node ∈ InFlight.Control.nodes input) : occupancy key node ≤ capacity context node := by
  obtain ⟨index, found⟩ := nodeIndex_exists node present
  have same := nodeIndex_sound node index found
  have bounded := (queue_facts context key good index).2.2
  simpa only [occupancy, queueAt, capacity, found, Option.map_some, Option.getD_some, same] using bounded

theorem queue_membership (context : Context input size) (key : Key input size) (good : good context key = true)
    (index : Fin size) (node : InFlight.Node) : index ∈ queueAt key.queues node ↔ key.phases.get index = .held node := by
  constructor
  · intro member
    cases found : nodeIndex input node with
    | none => simp [queueAt, found] at member
    | some selected =>
      have queued : index ∈ key.queues.get selected := by simpa only [queueAt, found, Option.map_some, Option.getD_some] using member
      have held := (queue_facts context key good selected).2.1 index queued
      simpa only [nodeIndex_sound node selected found] using held
  · intro held
    exact (held_conserved context key good index node held).2.2

theorem send_fifo (context : Context input size) (headers : Vector Packet.Header size)
    (before after : Key input size) (index : Fin size) (target : InFlight.Node)
    (selected : step context headers before (.packet index (.send target)) = some after) :
    ∃ source, before.phases.get index = .held source ∧ (queueAt before.queues source).head? = some index ∧
      after.current = before.current ∧ after.phases = before.phases.set index.val (.flight target) index.isLt ∧
      after.queues = putQueue before.queues source (queueAt before.queues source).tail ∧
      occupancy ({ before with queues := putQueue before.queues source (queueAt before.queues source).tail }) target + 1 ≤
        capacity context target := by
  have raw := (step_facts context headers before after _ selected).raw
  cases phase : before.phases.get index with
  | flight receiver => simp [rawStep, phase] at raw
  | delivered => simp [rawStep, phase] at raw
  | held source =>
    simp only [rawStep, phase] at raw
    split at raw
    · rename_i head
      split at raw
      · rename_i space
        cases raw
        exact ⟨source, rfl, head, rfl, rfl, rfl, space⟩
      · cases raw
    · cases raw

theorem arrival_fifo (context : Context input size) (headers : Vector Packet.Header size)
    (before after : Key input size) (index : Fin size)
    (selected : step context headers before (.packet index .arrive) = some after) :
    ∃ receiver, before.phases.get index = .flight receiver ∧ after.current = before.current ∧
      after.phases = before.phases.set index.val (.held receiver) index.isLt ∧
      after.queues = putQueue before.queues receiver (queueAt before.queues receiver ++ [index]) ∧
      queueAt after.queues receiver = queueAt before.queues receiver ++ [index] := by
  have facts := step_facts context headers before after _ selected
  have raw := facts.raw
  cases phase : before.phases.get index with
  | held source => simp [rawStep, phase] at raw
  | delivered => simp [rawStep, phase] at raw
  | flight receiver =>
    simp only [rawStep, phase, Option.some.injEq] at raw
    subst after
    have known := (flight_conserved context before facts.beforeGood index receiver phase).1
    exact ⟨receiver, rfl, rfl, rfl, rfl, queueAt_putQueue _ _ _ (InFlight.Control.known_mem_nodes _ _ known)⟩

theorem receive_fifo (context : Context input size) (headers : Vector Packet.Header size)
    (before after : Key input size) (index : Fin size)
    (selected : step context headers before (.packet index .receive) = some after) :
    ∃ node, before.phases.get index = .held node ∧ (queueAt before.queues node).head? = some index ∧
      after.current = before.current ∧ after.phases = before.phases.set index.val .delivered index.isLt ∧
      after.queues = putQueue before.queues node (queueAt before.queues node).tail := by
  have raw := (step_facts context headers before after _ selected).raw
  cases phase : before.phases.get index with
  | flight receiver => simp [rawStep, phase] at raw
  | delivered => simp [rawStep, phase] at raw
  | held node =>
    simp only [rawStep, phase] at raw
    split at raw
    · rename_i head
      cases raw
      exact ⟨node, rfl, head, rfl, rfl, rfl⟩
    · cases raw

theorem update_queues (context : Context input size) (headers : Vector Packet.Header size)
    (before after : Key input size) (move : Move size)
    (updating : (∃ index, move = .updateLeft index) ∨ (∃ index, move = .updateRight index) ∨
      (∃ first second, move = .updateBoth first second))
    (selected : step context headers before move = some after) :
    after.phases = before.phases ∧ after.queues = before.queues := by
  have raw := (step_facts context headers before after move selected).raw
  rcases updating with ⟨index, rfl⟩ | ⟨index, rfl⟩ | ⟨first, second, rfl⟩
  · cases next : InFlight.Control.nextCursor input.left before.current.1 index with
    | none => simp [rawStep, next] at raw
    | some cursor => simp [rawStep, next] at raw; cases raw; exact ⟨rfl, rfl⟩
  · cases next : InFlight.Control.nextCursor input.right before.current.2 index with
    | none => simp [rawStep, next] at raw
    | some cursor => simp [rawStep, next] at raw; cases raw; exact ⟨rfl, rfl⟩
  · cases left : InFlight.Control.nextCursor input.left before.current.1 first with
    | none => simp [rawStep, left] at raw
    | some firstCursor =>
      cases right : InFlight.Control.nextCursor input.right before.current.2 second with
      | none => simp [rawStep, left, right] at raw
      | some secondCursor => simp [rawStep, left, right] at raw; cases raw; exact ⟨rfl, rfl⟩

end Control

namespace Execution

theorem step_good (context : Context input size) (headers : Vector Packet.Header size)
    {before after : State input size} {event : Event input size}
    (step : (system context headers).step before event after) : Control.good context after.key = true := by
  obtain ⟨outcome, facts, rfl, _⟩ := step_facts context headers step
  exact facts.afterGood

theorem trace_good (context : Context input size) (headers : Vector Packet.Header size)
    {before after : State input size} {events : List (Event input size)}
    (good : Control.good context before.key = true) (trace : (system context headers).Trace before events after) :
    Control.good context after.key = true := by
  induction trace with
  | nil => exact good
  | cons step _ ih => exact ih (step_good context headers step)

end Execution
end Netlib.Federation.Cohort
