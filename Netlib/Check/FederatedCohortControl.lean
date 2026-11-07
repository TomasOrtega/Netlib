import Netlib.Model.FederatedCohort

/-!
# Shared FIFO and receiver reservation decisions

The control key retains all queue orders. Native guards run for every packet
on shared updates, including held queue tails and pending receivers.
-/

namespace Netlib.Federation.Cohort.Control

variable {input : Input} {size : Nat}

def occurrences (key : Key input size) (index : Fin size) : Nat :=
  key.queues.toList.flatten.count index

def reservations (key : Key input size) (node : I.Node) : Nat :=
  ((List.finRange size).filter fun index => decide (key.phases.get index = .flight node)).length

def occupancy (key : Key input size) (node : I.Node) : Nat :=
  (queueAt key.queues node).length + reservations key node

def capacity (context : Context input size) (node : I.Node) : Nat :=
  ((nodeIndex input node).map context.capacities.get).getD 0

def good (context : Context input size) (key : Key input size) : Bool :=
  (List.finRange size).all (fun index =>
    match key.phases.get index with
    | .held node => InFlight.Control.known input key.current node &&
        decide (occurrences key index = 1 ∧ index ∈ queueAt key.queues node)
    | .flight node => InFlight.Control.known input key.current node && decide (occurrences key index = 0)
    | .delivered => decide (occurrences key index = 0)) &&
  (List.finRange (InFlight.Control.nodes input).length).all (fun node =>
    decide (key.queues.get node).Nodup &&
    (key.queues.get node).all (fun index => decide (key.phases.get index = .held (nodeAt input node))) &&
    decide ((key.queues.get node).length + reservations key (nodeAt input node) ≤ context.capacities.get node))

def localChecks (context : Context input size) (headers : Vector Packet.Header size)
    (before after : Key input size) (move : Move size) : Bool :=
  (List.finRange size).all fun index =>
    match move.local index with
    | none => decide (after.packet index = before.packet index)
    | some selected => decide (InFlight.Control.step (context.packets.get index) (headers.get index)
        (before.packet index) selected = some (after.packet index))

def rawStep (context : Context input size) (key : Key input size) : Move size → Option (Key input size)
  | .packet index (.send target) =>
    match key.phases.get index with
    | .held source =>
      if (queueAt key.queues source).head? = some index then
        let queues := putQueue key.queues source (queueAt key.queues source).tail
        let released : Key input size := { key with queues := queues }
        if occupancy released target + 1 ≤ capacity context target then
          some ⟨key.current, key.phases.set index.val (.flight target) index.isLt, queues⟩
        else none
      else none
    | _ => none
  | .packet index .arrive =>
    match key.phases.get index with
    | .flight receiver =>
      some ⟨key.current, key.phases.set index.val (.held receiver) index.isLt,
        putQueue key.queues receiver (queueAt key.queues receiver ++ [index])⟩
    | _ => none
  | .packet index .receive =>
    match key.phases.get index with
    | .held node =>
      if (queueAt key.queues node).head? = some index then
        some ⟨key.current, key.phases.set index.val .delivered index.isLt,
          putQueue key.queues node (queueAt key.queues node).tail⟩
      else none
    | _ => none
  | .updateLeft index => do
    let next ← InFlight.Control.nextCursor input.left key.current.1 index
    return { key with current := (next, key.current.2) }
  | .updateRight index => do
    let next ← InFlight.Control.nextCursor input.right key.current.2 index
    return { key with current := (key.current.1, next) }
  | .updateBoth first second => do
    let left ← InFlight.Control.nextCursor input.left key.current.1 first
    let right ← InFlight.Control.nextCursor input.right key.current.2 second
    return { key with current := (left, right) }

def candidates (input : Input) (key : Key input size) : List (Move size) :=
  (List.finRange size).flatMap (fun index =>
    (InFlight.Control.nodes input).map (fun target => .packet index (.send target)) ++
      [.packet index .arrive, .packet index .receive]) ++
    [.updateLeft key.current.1.val, .updateRight key.current.2.val,
      .updateBoth key.current.1.val key.current.2.val]

def step (context : Context input size) (headers : Vector Packet.Header size)
    (before : Key input size) (move : Move size) : Option (Key input size) :=
  if good context before && decide (move ∈ candidates input before) then
    match rawStep context before move with
    | none => none
    | some after => if good context after && localChecks context headers before after move then some after else none
  else none

def successors (context : Context input size) (headers : Vector Packet.Header size)
    (key : Key input size) : List (Move size × Key input size) :=
  (candidates input key).filterMap fun move => (step context headers key move).map (move, ·)

structure Facts (context : Context input size) (headers : Vector Packet.Header size)
    (before after : Key input size) (move : Move size) : Prop where
  beforeGood : good context before = true
  candidate : move ∈ candidates input before
  raw : rawStep context before move = some after
  afterGood : good context after = true
  localSteps : ∀ index, match move.local index with
    | none => after.packet index = before.packet index
    | some selected => InFlight.Control.step (context.packets.get index) (headers.get index)
        (before.packet index) selected = some (after.packet index)

theorem step_facts (context : Context input size) (headers : Vector Packet.Header size)
    (before after : Key input size) (move : Move size)
    (selected : step context headers before move = some after) : Facts context headers before after move := by
  unfold step at selected
  split at selected
  · rename_i beforeChecked
    cases raw : rawStep context before move with
    | none => simp only [raw] at selected; cases selected
    | some actual =>
      simp only [raw] at selected
      split at selected
      · rename_i afterChecked
        cases selected
        have previous := (Bool.and_eq_true _ _).mp beforeChecked
        have next := (Bool.and_eq_true _ _).mp afterChecked
        refine ⟨previous.1, of_decide_eq_true previous.2, raw, next.1, ?_⟩
        intro index
        have checked := List.all_eq_true.mp next.2 index (List.mem_finRange index)
        cases selected : move.local index <;> simpa only [selected, decide_eq_true_eq] using checked
      · cases selected
  · cases selected

theorem mem_successors (context : Context input size) (headers : Vector Packet.Header size)
    (before after : Key input size) (move : Move size) :
    (move, after) ∈ successors context headers before ↔ step context headers before move = some after := by
  simp only [successors, List.mem_filterMap, Option.map_eq_some_iff]
  constructor
  · rintro ⟨candidate, _, next, selected, same⟩
    rcases Prod.mk.inj same with ⟨rfl, rfl⟩
    exact selected
  · intro selected
    exact ⟨move, (step_facts context headers before after move selected).candidate, after, selected, rfl⟩

end Netlib.Federation.Cohort.Control
