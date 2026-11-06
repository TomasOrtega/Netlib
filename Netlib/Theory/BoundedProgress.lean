import Netlib.Protocol.Transition

/-!
# Bounded service and progress

A demand comes from the state before an operation.
Every step uses the selected transition relation.
A bound on persistent demand service gives a bound on task completion.
The adapter laws must be proved for each concrete system.
-/

namespace Netlib.Theory.BoundedProgress

universe u v w x

structure Adapter (State : Type u) (Action : Type v) (Demand : Type w) where
  system : Protocol.Transition State Action
  invariant : State → Prop
  pending : State → Demand → Prop
  enabled : State → Demand → Prop
  serves : Demand → Action → Prop
  rank : State → Nat
  complete : State → Prop
  preserve : system.Invariant invariant
  nonincrease : ∀ {before action after}, invariant before → system.step before action after →
    rank after ≤ rank before
  demand : ∀ {state}, invariant state → 0 < rank state → ∃ value, pending state value
  pending_enabled : ∀ {state value}, invariant state → pending state value → enabled state value
  persistent : ∀ {before action after value}, invariant before → system.step before action after →
    rank after = rank before → pending before value → pending after value
  advance : ∀ {before action after value}, invariant before → system.step before action after →
    pending before value → enabled before value → serves value action → rank after < rank before
  finished : ∀ {state}, invariant state → rank state = 0 → complete state

/-- A concrete operation projects to one actual abstract operation. -/
def Adapter.pullback {State : Type u} {Action : Type v} {Demand : Type w}
    (adapter : Adapter State Action Demand)
    (system : Protocol.Transition Concrete ConcreteAction)
    (project : Concrete → State) (event : ConcreteAction → Action)
    (simulate : ∀ before action after, system.step before action after →
      adapter.system.step (project before) (event action) (project after)) :
    Adapter Concrete ConcreteAction Demand where
  system := system
  invariant state := adapter.invariant (project state)
  pending state value := adapter.pending (project state) value
  enabled state value := adapter.enabled (project state) value
  serves value action := adapter.serves value (event action)
  rank state := adapter.rank (project state)
  complete state := adapter.complete (project state)
  preserve := by
    intro before action after initial step
    exact adapter.preserve _ _ _ initial (simulate _ _ _ step)
  nonincrease := by intro before action after initial step; exact adapter.nonincrease initial (simulate _ _ _ step)
  demand := adapter.demand
  pending_enabled := adapter.pending_enabled
  persistent := by
    intro before action after value initial step same pending
    exact adapter.persistent initial (simulate _ _ _ step) same pending
  advance := by
    intro before action after value initial step pending enabled served
    exact adapter.advance initial (simulate _ _ _ step) pending enabled served
  finished := adapter.finished

structure Execution (system : Protocol.Transition State Action) where
  state : Nat → State
  action : Nat → Action
  checked : ∀ slot, system.step (state slot) (action slot) (state (slot + 1))

namespace Execution

def shift {system : Protocol.Transition State Action} (execution : Execution system) (first : Nat) : Execution system where
  state slot := execution.state (first + slot)
  action slot := execution.action (first + slot)
  checked slot := by simpa only [Nat.add_assoc] using execution.checked (first + slot)

def cast {left right : Protocol.Transition State Action} (execution : Execution left)
    (same : left = right) : Execution right := same ▸ execution

@[simp] theorem cast_state {left right : Protocol.Transition State Action}
    (execution : Execution left) (same : left = right) :
    (execution.cast same).state = execution.state := by cases same; rfl

variable {State : Type u} {Action : Type v} {Demand : Type w}
variable {adapter : Adapter State Action Demand}

/-- The bound applies after `first`. Each selected block has `bound` slots. -/
def ServiceFrom (execution : Execution adapter.system) (bound first : Nat) : Prop :=
  ∀ start, first ≤ start → ∀ value, adapter.pending (execution.state start) value →
    (∀ offset, offset < bound → adapter.pending (execution.state (start + offset)) value) →
    ∃ offset, offset < bound ∧ adapter.serves value (execution.action (start + offset))

def ServiceBound (execution : Execution adapter.system) (bound : Nat) : Prop :=
  execution.ServiceFrom bound 0

theorem invariant (execution : Execution adapter.system)
    (initial : adapter.invariant (execution.state 0)) (slot : Nat) :
    adapter.invariant (execution.state slot) := by
  induction slot with
  | zero => exact initial
  | succ slot ih => exact adapter.preserve _ _ _ ih (execution.checked slot)

theorem rank_le (execution : Execution adapter.system)
    (initial : adapter.invariant (execution.state 0)) (start count : Nat) :
    adapter.rank (execution.state (start + count)) ≤ adapter.rank (execution.state start) := by
  induction count with
  | zero => simp
  | succ count ih =>
    have step := adapter.nonincrease (execution.invariant initial (start + count))
      (execution.checked (start + count))
    exact Nat.le_trans step ih

theorem rank_mono (execution : Execution adapter.system)
    (initial : adapter.invariant (execution.state 0)) {first last : Nat} (order : first ≤ last) :
    adapter.rank (execution.state last) ≤ adapter.rank (execution.state first) := by
  obtain ⟨count, rfl⟩ := Nat.exists_eq_add_of_le order
  exact execution.rank_le initial first count

theorem block_decreases (execution : Execution adapter.system)
    (initial : adapter.invariant (execution.state 0))
    (service : execution.ServiceFrom bound first) (start : Nat) (begun : first ≤ start)
    (positive : 0 < adapter.rank (execution.state start)) :
    adapter.rank (execution.state (start + bound)) < adapter.rank (execution.state start) := by
  by_cases decreased : adapter.rank (execution.state (start + bound)) < adapter.rank (execution.state start)
  · exact decreased
  · have whole := execution.rank_le initial start bound
    have same : adapter.rank (execution.state (start + bound)) = adapter.rank (execution.state start) := by omega
    have equal : ∀ offset, offset ≤ bound →
        adapter.rank (execution.state (start + offset)) = adapter.rank (execution.state start) := by
      intro offset within
      have lower := execution.rank_mono initial (show start + offset ≤ start + bound by omega)
      have upper := execution.rank_le initial start offset
      omega
    obtain ⟨value, pending⟩ := adapter.demand (execution.invariant initial start) positive
    have retained : ∀ offset, offset ≤ bound → adapter.pending (execution.state (start + offset)) value := by
      intro offset
      induction offset with
      | zero => simpa using pending
      | succ offset ih =>
        intro within
        have previous := ih (by omega)
        have beforeEq := equal offset (by omega)
        have afterEq := equal (offset + 1) within
        exact adapter.persistent (execution.invariant initial (start + offset))
          (execution.checked (start + offset)) (by simpa only [Nat.add_assoc] using afterEq.trans beforeEq.symm) previous
    obtain ⟨offset, within, served⟩ := service start begun value pending (fun offset within => retained offset (by omega))
    have decrease := adapter.advance (execution.invariant initial (start + offset))
      (execution.checked (start + offset)) (retained offset (by omega))
      (adapter.pending_enabled (execution.invariant initial (start + offset)) (retained offset (by omega))) served
    have beforeEq := equal offset (by omega)
    have afterEq := equal (offset + 1) (by omega)
    simp only [Nat.add_assoc] at decrease
    omega

theorem rank_after_blocks (execution : Execution adapter.system)
    (initial : adapter.invariant (execution.state 0))
    (service : execution.ServiceFrom bound first) (start : Nat) (begun : first ≤ start) (blocks : Nat) :
    adapter.rank (execution.state (start + blocks * bound)) ≤ adapter.rank (execution.state start) - blocks := by
  induction blocks with
  | zero => simp
  | succ blocks ih =>
    have next := execution.rank_le initial (start + blocks * bound) bound
    by_cases empty : adapter.rank (execution.state (start + blocks * bound)) = 0
    · have zero : adapter.rank (execution.state (start + blocks * bound + bound)) = 0 := by omega
      have target : adapter.rank (execution.state (start + blocks * bound + bound)) ≤
          adapter.rank (execution.state start) - (blocks + 1) := by omega
      simpa only [Nat.succ_mul, Nat.add_assoc] using target
    · have positive : 0 < adapter.rank (execution.state (start + blocks * bound)) := by omega
      have decrease := execution.block_decreases initial service (start + blocks * bound) (by omega) positive
      have target : adapter.rank (execution.state (start + blocks * bound + bound)) ≤
          adapter.rank (execution.state start) - (blocks + 1) := by omega
      simpa only [Nat.succ_mul, Nat.add_assoc] using target

theorem zero_by (execution : Execution adapter.system)
    (initial : adapter.invariant (execution.state 0))
    (service : execution.ServiceFrom bound first) (start : Nat) (begun : first ≤ start) :
    adapter.rank (execution.state (start + adapter.rank (execution.state start) * bound)) = 0 := by
  have reduced := execution.rank_after_blocks initial service start begun (adapter.rank (execution.state start))
  omega

theorem completes_by (execution : Execution adapter.system)
    (initial : adapter.invariant (execution.state 0))
    (service : execution.ServiceFrom bound first) (start : Nat) (begun : first ≤ start) :
    adapter.complete (execution.state (start + adapter.rank (execution.state start) * bound)) :=
  adapter.finished (execution.invariant initial _) (execution.zero_by initial service start begun)

theorem zero_after (execution : Execution adapter.system)
    (initial : adapter.invariant (execution.state 0))
    (service : execution.ServiceFrom bound first) (start : Nat) (begun : first ≤ start)
    (slot : Nat) (later : start + adapter.rank (execution.state start) * bound ≤ slot) :
    adapter.rank (execution.state slot) = 0 := by
  have zero := execution.zero_by initial service start begun
  have order := execution.rank_mono initial later
  omega

theorem completes_after (execution : Execution adapter.system)
    (initial : adapter.invariant (execution.state 0))
    (service : execution.ServiceFrom bound first) (start : Nat) (begun : first ≤ start)
    (slot : Nat) (later : start + adapter.rank (execution.state start) * bound ≤ slot) :
    adapter.complete (execution.state slot) :=
  adapter.finished (execution.invariant initial slot) (execution.zero_after initial service start begun slot later)

end Execution

/-- Only the first `length` operations belong to this execution. -/
structure Prefix (system : Protocol.Transition State Action) where
  length : Nat
  state : Nat → State
  action : Nat → Action
  checked : ∀ slot, slot < length → system.step (state slot) (action slot) (state (slot + 1))

namespace Prefix

def suffix {system : Protocol.Transition State Action} (execution : Prefix system) (first : Nat) : Prefix system where
  length := execution.length - first
  state slot := execution.state (first + slot)
  action slot := execution.action (first + slot)
  checked slot within := by
    have selected : first + slot < execution.length := by omega
    simpa only [Nat.add_assoc] using execution.checked (first + slot) selected

def cast {left right : Protocol.Transition State Action} (execution : Prefix left)
    (same : left = right) : Prefix right := same ▸ execution

@[simp] theorem cast_state {left right : Protocol.Transition State Action}
    (execution : Prefix left) (same : left = right) :
    (execution.cast same).state = execution.state := by cases same; rfl

@[simp] theorem cast_length {left right : Protocol.Transition State Action}
    (execution : Prefix left) (same : left = right) :
    (execution.cast same).length = execution.length := by cases same; rfl

variable {State : Type u} {Action : Type v} {Demand : Type w}
variable {adapter : Adapter State Action Demand}

def ServiceFrom (execution : Prefix adapter.system) (bound first : Nat) : Prop :=
  ∀ start, first ≤ start → start + bound ≤ execution.length → ∀ value,
    adapter.pending (execution.state start) value → (∀ offset, offset < bound → adapter.pending (execution.state (start + offset)) value) →
    ∃ offset, offset < bound ∧ adapter.serves value (execution.action (start + offset))

def ServiceBound (execution : Prefix adapter.system) (bound : Nat) : Prop :=
  execution.ServiceFrom bound 0

theorem invariant (execution : Prefix adapter.system)
    (initial : adapter.invariant (execution.state 0)) (slot : Nat) (within : slot ≤ execution.length) :
    adapter.invariant (execution.state slot) := by
  induction slot with
  | zero => exact initial
  | succ slot ih =>
    exact adapter.preserve _ _ _ (ih (by omega)) (execution.checked slot (by omega))

theorem rank_mono (execution : Prefix adapter.system)
    (initial : adapter.invariant (execution.state 0)) {first last : Nat}
    (order : first ≤ last) (within : last ≤ execution.length) :
    adapter.rank (execution.state last) ≤ adapter.rank (execution.state first) := by
  obtain ⟨count, rfl⟩ := Nat.exists_eq_add_of_le order
  induction count with
  | zero => simp
  | succ count ih =>
    have step := adapter.nonincrease (execution.invariant initial (first + count) (by omega))
      (execution.checked (first + count) (by omega))
    exact Nat.le_trans step (ih (by omega) (by omega))

theorem block_decreases (execution : Prefix adapter.system)
    (initial : adapter.invariant (execution.state 0))
    (service : execution.ServiceFrom bound first) (start : Nat) (begun : first ≤ start)
    (within : start + bound ≤ execution.length)
    (positive : 0 < adapter.rank (execution.state start)) :
    adapter.rank (execution.state (start + bound)) < adapter.rank (execution.state start) := by
  by_cases decreased : adapter.rank (execution.state (start + bound)) < adapter.rank (execution.state start)
  · exact decreased
  · have whole := execution.rank_mono initial (show start ≤ start + bound by omega) within
    have same : adapter.rank (execution.state (start + bound)) = adapter.rank (execution.state start) := by omega
    have equal : ∀ offset, offset ≤ bound →
        adapter.rank (execution.state (start + offset)) = adapter.rank (execution.state start) := by
      intro offset selected
      have lower := execution.rank_mono initial (show start + offset ≤ start + bound by omega) within
      have upper := execution.rank_mono initial (show start ≤ start + offset by omega) (by omega)
      omega
    obtain ⟨value, pending⟩ := adapter.demand (execution.invariant initial start (by omega)) positive
    have retained : ∀ offset, offset ≤ bound → adapter.pending (execution.state (start + offset)) value := by
      intro offset
      induction offset with
      | zero => simpa using pending
      | succ offset ih =>
        intro selected
        have previous := ih (by omega)
        have beforeEq := equal offset (by omega)
        have afterEq := equal (offset + 1) selected
        exact adapter.persistent (execution.invariant initial (start + offset) (by omega))
          (execution.checked (start + offset) (by omega))
          (by simpa only [Nat.add_assoc] using afterEq.trans beforeEq.symm) previous
    obtain ⟨offset, selected, served⟩ := service start begun within value pending
      (fun offset selected => retained offset (by omega))
    have decrease := adapter.advance (execution.invariant initial (start + offset) (by omega))
      (execution.checked (start + offset) (by omega)) (retained offset (by omega))
      (adapter.pending_enabled (execution.invariant initial (start + offset) (by omega))
        (retained offset (by omega))) served
    have beforeEq := equal offset (by omega)
    have afterEq := equal (offset + 1) (by omega)
    simp only [Nat.add_assoc] at decrease
    omega

theorem rank_after_blocks (execution : Prefix adapter.system)
    (initial : adapter.invariant (execution.state 0))
    (service : execution.ServiceFrom bound first) (start : Nat) (begun : first ≤ start)
    (blocks : Nat) (within : start + blocks * bound ≤ execution.length) :
    adapter.rank (execution.state (start + blocks * bound)) ≤ adapter.rank (execution.state start) - blocks := by
  induction blocks with
  | zero => simp
  | succ blocks ih =>
    have index : start + (blocks + 1) * bound = start + blocks * bound + bound := by
      simp only [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
    rw [index] at within ⊢
    have previous := ih (by omega)
    have next := execution.rank_mono initial (show start + blocks * bound ≤ start + blocks * bound + bound by omega) within
    by_cases empty : adapter.rank (execution.state (start + blocks * bound)) = 0
    · omega
    · have positive : 0 < adapter.rank (execution.state (start + blocks * bound)) := by omega
      have decrease := execution.block_decreases initial service (start + blocks * bound) (by omega) within positive
      omega

theorem zero_by (execution : Prefix adapter.system)
    (initial : adapter.invariant (execution.state 0))
    (service : execution.ServiceFrom bound first) (start : Nat) (begun : first ≤ start)
    (within : start + adapter.rank (execution.state start) * bound ≤ execution.length) :
    adapter.rank (execution.state (start + adapter.rank (execution.state start) * bound)) = 0 := by
  have reduced := execution.rank_after_blocks initial service start begun (adapter.rank (execution.state start)) within
  omega

theorem completes_by (execution : Prefix adapter.system)
    (initial : adapter.invariant (execution.state 0))
    (service : execution.ServiceFrom bound first) (start : Nat) (begun : first ≤ start)
    (within : start + adapter.rank (execution.state start) * bound ≤ execution.length) :
    adapter.complete (execution.state (start + adapter.rank (execution.state start) * bound)) :=
  adapter.finished (execution.invariant initial _ within) (execution.zero_by initial service start begun within)

theorem completes_after (execution : Prefix adapter.system)
    (initial : adapter.invariant (execution.state 0))
    (service : execution.ServiceFrom bound first) (start : Nat) (begun : first ≤ start)
    (slot : Nat) (later : start + adapter.rank (execution.state start) * bound ≤ slot)
    (within : slot ≤ execution.length) : adapter.complete (execution.state slot) := by
  have zero := execution.zero_by initial service start begun (by omega)
  have reduced := execution.rank_mono initial later within
  exact adapter.finished (execution.invariant initial slot within) (by omega)

/-- Read the second task's rank from the actual state at the first bound. -/
theorem sequential_at_cut {LeftDemand : Type w} {RightDemand : Type x}
    (left : Adapter State Action LeftDemand) (right : Adapter State Action RightDemand)
    (same : left.system = right.system) (execution : Prefix left.system)
    (leftInitial : left.invariant (execution.state 0))
    (leftService : execution.ServiceBound leftBound)
    (rightInitial : right.invariant (execution.state (left.rank (execution.state 0) * leftBound)))
    (rightService : ((execution.cast same).suffix (left.rank (execution.state 0) * leftBound)).ServiceBound rightBound)
    (within : left.rank (execution.state 0) * leftBound +
      right.rank (execution.state (left.rank (execution.state 0) * leftBound)) * rightBound ≤ execution.length) :
    let cut := left.rank (execution.state 0) * leftBound
    let finish := cut + right.rank (execution.state cut) * rightBound
    left.complete (execution.state finish) ∧ right.complete (execution.state finish) := by
  dsimp only
  constructor
  · exact execution.completes_after leftInitial leftService 0 (by omega) _ (by omega) within
  · have initial : right.invariant (((execution.cast same).suffix (left.rank (execution.state 0) * leftBound)).state 0) := by
      simpa only [suffix, cast_state, Nat.add_zero] using rightInitial
    have complete := ((execution.cast same).suffix (left.rank (execution.state 0) * leftBound)).completes_by
      initial rightService 0 (Nat.zero_le 0) (by
        simp only [suffix, cast_state, cast_length, Nat.add_zero, Nat.zero_add]
        omega)
    simpa only [suffix, cast_state, Nat.add_zero, Nat.zero_add] using complete

theorem sequential {LeftDemand : Type w} {RightDemand : Type x}
    (left : Adapter State Action LeftDemand) (right : Adapter State Action RightDemand)
    (same : left.system = right.system) (execution : Prefix left.system)
    (leftInitial : left.invariant (execution.state 0))
    (rightInitial : right.invariant (execution.state 0))
    (leftService : execution.ServiceBound leftBound)
    (rightService : (execution.cast same).ServiceFrom rightBound (left.rank (execution.state 0) * leftBound))
    (within : left.rank (execution.state 0) * leftBound + right.rank (execution.state 0) * rightBound ≤ execution.length) :
    let finish := left.rank (execution.state 0) * leftBound + right.rank (execution.state 0) * rightBound
    left.complete (execution.state finish) ∧ right.complete (execution.state finish) := by
  dsimp only
  constructor
  · exact execution.completes_after leftInitial leftService 0 (by omega) _ (by omega) within
  · have initial : right.invariant ((execution.cast same).state 0) := by simpa using rightInitial
    have cutWithin : left.rank (execution.state 0) * leftBound ≤ (execution.cast same).length := by
      simpa only [cast_length] using (show left.rank (execution.state 0) * leftBound ≤ execution.length by omega)
    have reduced := (execution.cast same).rank_mono initial (Nat.zero_le _) cutWithin
    simp only [cast_state] at reduced
    have products := Nat.mul_le_mul_right rightBound reduced
    simpa only [cast_state] using
      (execution.cast same).completes_after initial rightService
        (left.rank (execution.state 0) * leftBound) (Nat.le_refl _) _
        (by simpa only [cast_state] using Nat.add_le_add_left products _)
        (by simpa only [cast_length] using within)

theorem concurrent {LeftDemand : Type w} {RightDemand : Type x}
    (left : Adapter State Action LeftDemand) (right : Adapter State Action RightDemand)
    (same : left.system = right.system) (execution : Prefix left.system)
    (leftInitial : left.invariant (execution.state 0))
    (rightInitial : right.invariant (execution.state 0))
    (leftService : execution.ServiceBound leftBound)
    (rightService : (execution.cast same).ServiceBound rightBound)
    (within : max (left.rank (execution.state 0) * leftBound) (right.rank (execution.state 0) * rightBound) ≤ execution.length) :
    let finish := max (left.rank (execution.state 0) * leftBound) (right.rank (execution.state 0) * rightBound)
    left.complete (execution.state finish) ∧ right.complete (execution.state finish) := by
  dsimp only
  constructor
  · exact execution.completes_after leftInitial leftService 0 (by omega) _
      (by simpa using Nat.le_max_left _ _) within
  · have initial : right.invariant ((execution.cast same).state 0) := by simpa using rightInitial
    simpa only [cast_state] using
      (execution.cast same).completes_after initial rightService 0 (by omega) _
        (by simpa only [cast_state, Nat.zero_add] using (Nat.le_max_right
          (left.rank (execution.state 0) * leftBound) (right.rank (execution.state 0) * rightBound)))
        (by simpa only [cast_length] using within)

end Prefix

/-- The second adapter is required only from the actual cut state. -/
theorem sequential_at_cut {State : Type u} {Action : Type v} {LeftDemand : Type w} {RightDemand : Type x}
    (left : Adapter State Action LeftDemand) (right : Adapter State Action RightDemand)
    (same : left.system = right.system) (execution : Execution left.system)
    (leftInitial : left.invariant (execution.state 0))
    (leftService : execution.ServiceBound leftBound)
    (rightInitial : right.invariant (execution.state (left.rank (execution.state 0) * leftBound)))
    (rightService : ((execution.cast same).shift (left.rank (execution.state 0) * leftBound)).ServiceBound rightBound) :
    let cut := left.rank (execution.state 0) * leftBound
    let finish := cut + right.rank (execution.state cut) * rightBound
    left.complete (execution.state finish) ∧ right.complete (execution.state finish) := by
  dsimp only
  constructor
  · exact execution.completes_after leftInitial leftService 0 (by omega) _ (by omega)
  · have initial : right.invariant (((execution.cast same).shift (left.rank (execution.state 0) * leftBound)).state 0) := by
      simpa only [Execution.shift, Execution.cast_state, Nat.add_zero] using rightInitial
    have complete := ((execution.cast same).shift (left.rank (execution.state 0) * leftBound)).completes_by
      initial rightService 0 (Nat.zero_le 0)
    simpa only [Execution.shift, Execution.cast_state, Nat.add_zero, Nat.zero_add] using complete

/-- The second task receives its service bound after the first task's bound. -/
theorem sequential {State : Type u} {Action : Type v} {LeftDemand : Type w} {RightDemand : Type x}
    (left : Adapter State Action LeftDemand) (right : Adapter State Action RightDemand)
    (same : left.system = right.system) (execution : Execution left.system)
    (leftInitial : left.invariant (execution.state 0))
    (rightInitial : right.invariant (execution.state 0))
    (leftService : execution.ServiceBound leftBound)
    (rightService : (execution.cast same).ServiceFrom rightBound (left.rank (execution.state 0) * leftBound)) :
    let finish := left.rank (execution.state 0) * leftBound + right.rank (execution.state 0) * rightBound
    left.complete (execution.state finish) ∧ right.complete (execution.state finish) := by
  dsimp only
  constructor
  · exact execution.completes_after leftInitial leftService 0 (by omega) _ (by omega)
  · have initial : right.invariant ((execution.cast same).state 0) := by simpa using rightInitial
    have reduced := (execution.cast same).rank_le initial 0 (left.rank (execution.state 0) * leftBound)
    simp only [Execution.cast_state, Nat.zero_add] at reduced
    have products := Nat.mul_le_mul_right rightBound reduced
    simpa only [Execution.cast_state] using
      (execution.cast same).completes_after initial rightService
        (left.rank (execution.state 0) * leftBound) (Nat.le_refl _) _ (by simpa only [Execution.cast_state] using Nat.add_le_add_left products _)

/-- Each task has its own service bound on the same actual execution. -/
theorem concurrent {State : Type u} {Action : Type v} {LeftDemand : Type w} {RightDemand : Type x}
    (left : Adapter State Action LeftDemand) (right : Adapter State Action RightDemand)
    (same : left.system = right.system) (execution : Execution left.system)
    (leftInitial : left.invariant (execution.state 0))
    (rightInitial : right.invariant (execution.state 0))
    (leftService : execution.ServiceBound leftBound)
    (rightService : (execution.cast same).ServiceBound rightBound) :
    let finish := max (left.rank (execution.state 0) * leftBound) (right.rank (execution.state 0) * rightBound)
    left.complete (execution.state finish) ∧ right.complete (execution.state finish) := by
  dsimp only
  constructor
  · exact execution.completes_after leftInitial leftService 0 (by omega) _ (by simpa using Nat.le_max_left _ _)
  · have initial : right.invariant ((execution.cast same).state 0) := by simpa using rightInitial
    simpa only [Execution.cast_state] using
      (execution.cast same).completes_after initial rightService 0 (by omega) _
        (by simpa only [Execution.cast_state, Nat.zero_add] using (Nat.le_max_right
          (left.rank (execution.state 0) * leftBound) (right.rank (execution.state 0) * rightBound)))

end Netlib.Theory.BoundedProgress
