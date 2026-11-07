import Netlib.Theory.BoundedServiceRank

/-!
# Computed ranks for finite sparse progress tables

Every progress successor must decrease the generated rank. Literal idle is an
implicit self-loop. The checker derives current demands from actual rows.
-/

namespace Netlib.Theory.FiniteProgressRank

universe u

structure Edge (Move : Type u) (size : Nat) where
  move : Move
  target : Fin size
  deriving DecidableEq

structure Table (Move : Type u) (size : Nat) where
  initial : Fin size
  rows : Vector (List (Edge Move size)) size
  terminal : Vector Bool size

inductive Event (Move : Type u) where
  | idle
  | progress (move : Move)
  deriving DecidableEq

variable {Move : Type u} {size : Nat}

def Table.row (table : Table Move size) (state : Fin size) : List (Edge Move size) := table.rows.get state

def Table.done (table : Table Move size) (state : Fin size) : Bool := table.terminal.get state

def Table.network (table : Table Move size) : Network (Fin size) :=
  ⟨fun source target => ∃ edge ∈ table.row source, edge.target = target⟩

def Table.system (table : Table Move size) : Protocol.Transition (Fin size) (Event Move) where
  step before event after := match event with
    | .idle => after = before
    | .progress move => ∃ edge ∈ table.row before, edge.move = move ∧ edge.target = after

def Table.pending (table : Table Move size) (state : Fin size) : Option Move :=
  (table.row state).head?.map (·.move)

def serves [DecidableEq Move] (demand : Move) : Event Move → Bool
  | .idle => false
  | .progress move => decide (move = demand)

private structure Search (table : Table Move size) where
  known : List (Fin size)
  todo : List (Fin size)
  knownSound : ∀ state ∈ known, table.network.Reachable table.initial state
  todoSound : ∀ state ∈ todo, table.network.Reachable table.initial state

private def addEdges (table : Table Move size) (source : Fin size)
    (reached : table.network.Reachable table.initial source) :
    (edges : List (Edge Move size)) → (∀ edge ∈ edges, edge ∈ table.row source) → Search table → Search table
  | [], _, current => current
  | edge :: rest, members, current =>
    let next : Search table :=
      if edge.target ∈ current.known then current
      else {
        known := edge.target :: current.known
        todo := edge.target :: current.todo
        knownSound := by
          intro state member
          rcases List.mem_cons.mp member with same | previous
          · subst state
            exact reached.trans (.single ⟨edge, members edge (by simp), rfl⟩)
          · exact current.knownSound state previous
        todoSound := by
          intro state member
          rcases List.mem_cons.mp member with same | previous
          · subst state
            exact reached.trans (.single ⟨edge, members edge (by simp), rfl⟩)
          · exact current.todoSound state previous }
    addEdges table source reached rest (fun edge member => members edge (List.mem_cons_of_mem _ member)) next

private def search (table : Table Move size) : Nat → Search table → Search table
  | 0, current => current
  | remaining + 1, current =>
    match todoEq : current.todo with
    | [] => current
    | source :: rest =>
      let reached := current.todoSound source (by rw [todoEq]; simp)
      let tail : Search table := {
        known := current.known
        todo := rest
        knownSound := current.knownSound
        todoSound := by
          intro state member
          exact current.todoSound state (by rw [todoEq]; exact List.mem_cons_of_mem _ member) }
      search table remaining (addEdges table source reached (table.row source) (fun _ member => member) tail)

private def discovery (table : Table Move size) : Search table :=
  search table size {
    known := [table.initial]
    todo := [table.initial]
    knownSound := by intro state member; exact (List.mem_singleton.mp member) ▸ .refl _
    todoSound := by intro state member; exact (List.mem_singleton.mp member) ▸ .refl _ }

def reachable (table : Table Move size) : List (Fin size) := (discovery table).known

theorem reachable_sound (table : Table Move size) (state : Fin size) (member : state ∈ reachable table) :
    table.network.Reachable table.initial state := (discovery table).knownSound state member

private def closureValid (table : Table Move size) (states : List (Fin size)) : Bool :=
  decide (table.initial ∈ states) && states.all fun source =>
    (table.row source).all fun edge => decide (edge.target ∈ states)

private def initialRanks (table : Table Move size) : Vector (Option Nat) size :=
  Vector.ofFn fun state => if table.done state then some 0 else none

private def rankRound (table : Table Move size) (states : List (Fin size))
    (prior : Vector (Option Nat) size) : Vector (Option Nat) size :=
  states.foldl (fun after state =>
    match prior.get state with
    | some _ => after
    | none =>
      if !(table.row state).isEmpty && (table.row state).all (fun edge => (prior.get edge.target).isSome) then
        let largest := (table.row state).foldl (fun rank edge => max rank ((prior.get edge.target).getD 0)) 0
        after.set state.val (some (largest + 1)) state.isLt
      else after) prior

private def rankRounds (table : Table Move size) (states : List (Fin size)) : Nat → Vector (Option Nat) size
  | 0 => initialRanks table
  | rounds + 1 => rankRound table states (rankRounds table states rounds)

def candidate (table : Table Move size) : Vector (Option Nat) size := rankRounds table (reachable table) size

def rankAt (ranks : Vector (Option Nat) size) (state : Fin size) : Nat := (ranks.get state).getD 0

private def rankValid (table : Table Move size) (states : List (Fin size))
    (ranks : Vector (Option Nat) size) : Bool :=
  closureValid table states && states.all fun state =>
    (ranks.get state).isSome &&
      decide (rankAt ranks state ≤ size) &&
      decide (rankAt ranks state = 0 ↔ table.done state = true) &&
      (if table.done state then (table.row state).isEmpty else !(table.row state).isEmpty) &&
      (table.row state).all (fun edge => decide (rankAt ranks edge.target < rankAt ranks state))

structure Laws (table : Table Move size) (states : List (Fin size)) (ranks : Vector (Option Nat) size) : Prop where
  initial : table.initial ∈ states
  closed : ∀ source ∈ states, ∀ edge ∈ table.row source, edge.target ∈ states
  assigned : ∀ state ∈ states, (ranks.get state).isSome = true
  bounded : ∀ state ∈ states, rankAt ranks state ≤ size
  zero : ∀ state ∈ states, rankAt ranks state = 0 ↔ table.done state = true
  live : ∀ state ∈ states, table.done state = false → table.row state ≠ []
  terminal : ∀ state ∈ states, table.done state = true → table.row state = []
  decrease : ∀ source ∈ states, ∀ edge ∈ table.row source, rankAt ranks edge.target < rankAt ranks source

private theorem rankValid_sound (table : Table Move size) (states : List (Fin size))
    (ranks : Vector (Option Nat) size) (checked : rankValid table states ranks = true) : Laws table states ranks := by
  have checked : closureValid table states = true ∧ ∀ state ∈ states,
      ((((ranks.get state).isSome = true ∧ rankAt ranks state ≤ size) ∧
        (rankAt ranks state = 0 ↔ table.done state = true)) ∧
        (if table.done state then (table.row state).isEmpty else !(table.row state).isEmpty) = true) ∧
        ∀ edge ∈ table.row state, rankAt ranks edge.target < rankAt ranks state := by
    simpa only [rankValid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] using checked
  have closure : table.initial ∈ states ∧
      ∀ source ∈ states, ∀ edge ∈ table.row source, edge.target ∈ states := by
    simpa only [closureValid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] using checked.1
  refine ⟨closure.1, closure.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro state member; exact (checked.2 state member).1.1.1.1
  · intro state member; exact (checked.2 state member).1.1.1.2
  · intro state member; exact (checked.2 state member).1.1.2
  · intro state member unfinished
    have shape := (checked.2 state member).1.2
    have nonempty : (table.row state).isEmpty = false := by
      cases empty : (table.row state).isEmpty <;> simp_all
    exact List.isEmpty_eq_false_iff.mp nonempty
  · intro state member finished
    have shape := (checked.2 state member).1.2
    simpa only [finished, ↓reduceIte, List.isEmpty_iff] using shape
  · intro state member; exact (checked.2 state member).2

structure Limits where
  states : Nat
  edges : Nat
  work : Nat
  deriving Repr

def edgeCount (table : Table Move size) : Nat :=
  (table.rows.toArray.toList.map List.length).sum

/-- An input-size work estimate, not a processor-time bound. -/
def workEstimate (states edges : Nat) : Nat := (states + 1) ^ 2 * (states + edges + 1)

def preflight (states edges : Nat) (limits : Limits) : Except String Unit := do
  if states > limits.states then throw s!"Progress states {states} exceed budget {limits.states}."
  if edges > limits.edges then throw s!"Progress successors {edges} exceed budget {limits.edges}."
  if workEstimate states edges > limits.work then
    throw s!"Progress work estimate {workEstimate states edges} exceeds budget {limits.work}."

structure Checked (table : Table Move size) where
  limits : Limits
  stateBound : size ≤ limits.states
  edgeBound : edgeCount table ≤ limits.edges
  workBound : workEstimate size (edgeCount table) ≤ limits.work
  states : List (Fin size)
  statesComputed : states = reachable table
  ranks : Vector (Option Nat) size
  ranksComputed : ranks = candidate table
  valid : Laws table (reachable table) ranks

variable {table : Table Move size} {before after : Fin size} {event : Event Move} {demand : Move}

private theorem preflight_sound (states edges : Nat) (limits : Limits)
    (checked : preflight states edges limits = .ok ()) :
    states ≤ limits.states ∧ edges ≤ limits.edges ∧ workEstimate states edges ≤ limits.work := by
  unfold preflight at checked
  repeat' first
    | (split at checked)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at checked)
    | (solve | cases checked)
    | (solve | omega)

def check (table : Table Move size) (limits : Limits) : Except String (Checked table) := do
  match bounded : preflight size (edgeCount table) limits with
  | .error reason => throw reason
  | .ok () =>
    let states := reachable table
    let ranks := rankRounds table states size
    if accepted : rankValid table states ranks = true then
      let bounds := preflight_sound size (edgeCount table) limits bounded
      return ⟨limits, bounds.1, bounds.2.1, bounds.2.2, states, rfl, ranks, rfl, rankValid_sound table _ _ accepted⟩
    else throw "The reachable progress table has a dead end, progress cycle, or invalid rank certificate."

def Checked.rank (value : Checked table) (state : Fin size) : Nat := rankAt value.ranks state

theorem Checked.initial_mem (value : Checked table) : table.initial ∈ reachable table := value.valid.initial

theorem Checked.rank_bound (value : Checked table) (state : Fin size) (member : state ∈ reachable table) :
    value.rank state ≤ size := value.valid.bounded state member

theorem Checked.reachable_exact (value : Checked table) (state : Fin size) :
    state ∈ reachable table ↔ table.network.Reachable table.initial state := by
  constructor
  · exact reachable_sound table state
  · intro path
    have preserve : ∀ {source target}, table.network.Reachable source target →
        source ∈ reachable table → target ∈ reachable table := by
      intro source target path
      induction path with
      | refl => exact id
      | step edge rest ih =>
        intro sourceMem
        obtain ⟨selected, member, same⟩ := edge
        apply ih
        rw [← same]
        exact value.valid.closed _ sourceMem selected member
    exact preserve path value.initial_mem

theorem Checked.states_exact (value : Checked table) (state : Fin size) :
    state ∈ value.states ↔ table.network.Reachable table.initial state := by
  rw [value.statesComputed]
  exact value.reachable_exact state

theorem Checked.zero_iff (value : Checked table) (state : Fin size) (member : state ∈ reachable table) :
    value.rank state = 0 ↔ table.done state = true := value.valid.zero state member

theorem Checked.progress (value : Checked table) (source : Fin size) (member : source ∈ reachable table)
    (edge : Edge Move size) (present : edge ∈ table.row source) :
    edge.target ∈ reachable table ∧ value.rank edge.target < value.rank source :=
  ⟨value.valid.closed source member edge present, value.valid.decrease source member edge present⟩

theorem Checked.current (value : Checked table) (state : Fin size) (member : state ∈ reachable table)
    (positive : 0 < value.rank state) :
    ∃ edge ∈ table.row state, table.pending state = some edge.move ∧
      table.system.step state (.progress edge.move) edge.target ∧ value.rank edge.target < value.rank state := by
  have unfinished : table.done state = false := by
    cases done : table.done state with
    | false => rfl
    | true => have zero := (value.zero_iff state member).mpr done; omega
  have live := value.valid.live state member unfinished
  cases row : table.row state with
  | nil => exact False.elim (live row)
  | cons edge rest =>
    have present : edge ∈ table.row state := by rw [row]; simp
    exact ⟨edge, by simp, by simp only [Table.pending, row, List.head?_cons, Option.map_some],
      ⟨edge, present, rfl, rfl⟩, (value.progress state member edge present).2⟩

theorem Checked.preserve (value : Checked table) (member : before ∈ reachable table)
    (step : table.system.step before event after) : after ∈ reachable table := by
  cases event with
  | idle => exact step ▸ member
  | progress move =>
    obtain ⟨edge, present, _, same⟩ := step
    exact same ▸ (value.progress before member edge present).1

theorem Checked.nonincrease (value : Checked table) (member : before ∈ reachable table)
    (step : table.system.step before event after) : value.rank after ≤ value.rank before := by
  cases event with
  | idle => exact step ▸ Nat.le_refl _
  | progress move =>
    obtain ⟨edge, present, _, same⟩ := step
    exact same ▸ Nat.le_of_lt (value.progress before member edge present).2

theorem Checked.equal_idle (value : Checked table) (member : before ∈ reachable table)
    (step : table.system.step before event after) (equal : value.rank after = value.rank before) :
    event = .idle ∧ after = before := by
  cases event with
  | idle => exact ⟨rfl, step⟩
  | progress move =>
    obtain ⟨edge, present, _, same⟩ := step
    have decrease := (value.progress before member edge present).2
    rw [same] at decrease
    omega

theorem Checked.strict [DecidableEq Move] (value : Checked table) (member : before ∈ reachable table)
    (step : table.system.step before event after) (served : serves demand event = true) :
    value.rank after < value.rank before := by
  cases event with
  | idle => cases served
  | progress move =>
    obtain ⟨edge, present, _, same⟩ := step
    exact same ▸ (value.progress before member edge present).2

theorem Checked.prefix_mem (value : Checked table) (trace : BoundedProgress.Prefix table.system)
    (initial : trace.state 0 = table.initial) (slot : Nat) (within : slot ≤ trace.length) :
    trace.state slot ∈ reachable table := by
  induction slot with
  | zero => rw [initial]; exact value.initial_mem
  | succ slot ih => exact value.preserve (ih (by omega)) (trace.checked slot (by omega))

theorem Checked.completes_by [DecidableEq Move] (value : Checked table) (trace : BoundedProgress.Prefix table.system)
    (initial : trace.state 0 = table.initial) (bound : Nat)
    (service : BoundedServiceCheck.Serviced trace.length (fun slot => table.pending (trace.state slot)) trace.action serves bound)
    (enough : value.rank table.initial * bound ≤ trace.length) :
    table.done (trace.state (value.rank table.initial * bound)) = true := by
  let rank := fun slot => value.rank (trace.state slot)
  have nonincrease : ∀ slot, slot < trace.length → rank (slot + 1) ≤ rank slot := by
    intro slot inside
    exact value.nonincrease (value.prefix_mem trace initial slot (by omega)) (trace.checked slot inside)
  have demand : ∀ slot, slot ≤ trace.length → 0 < rank slot → ∃ demand, table.pending (trace.state slot) = some demand := by
    intro slot inside positive
    obtain ⟨edge, _, selected, _, _⟩ := value.current (trace.state slot) (value.prefix_mem trace initial slot inside) positive
    exact ⟨edge.move, selected⟩
  have persistent : ∀ slot, slot < trace.length → 0 < rank slot → ∀ demand,
      rank (slot + 1) = rank slot → table.pending (trace.state slot) = some demand →
      table.pending (trace.state (slot + 1)) = some demand := by
    intro slot inside _ demand equal selected
    have same := value.equal_idle (value.prefix_mem trace initial slot (by omega)) (trace.checked slot inside) equal
    rw [same.2]
    exact selected
  have strict : ∀ slot, slot < trace.length → 0 < rank slot → ∀ demand,
      table.pending (trace.state slot) = some demand → serves demand (trace.action slot) = true → rank (slot + 1) < rank slot := by
    intro slot inside _ demand _ served
    exact value.strict (value.prefix_mem trace initial slot (by omega)) (trace.checked slot inside) served
  have zero := BoundedServiceRank.zero_by service nonincrease demand persistent strict
    (by simpa only [rank, initial] using enough)
  have done := (value.zero_iff (trace.state (value.rank table.initial * bound))
    (value.prefix_mem trace initial _ enough)).mp
  apply done
  simpa only [rank, initial] using zero

end Netlib.Theory.FiniteProgressRank
