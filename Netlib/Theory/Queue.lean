import Std

namespace Netlib.Theory.Queue

universe u

structure State (Packet : Type u) where
  delivered : List Packet := []
  pending : List Packet := []
  deriving Repr, DecidableEq

structure Tick (Packet : Type u) where
  arrivals : List Packet
  capacity : Nat
  deriving Repr, DecidableEq

structure Result (Packet : Type u) where
  served : List Packet
  next : State Packet
  deriving Repr, DecidableEq

/-- Arrivals enter an unbounded FIFO before the tick's service. -/
def step (state : State Packet) (tick : Tick Packet) : Result Packet :=
  let available := state.pending ++ tick.arrivals
  let served := available.take tick.capacity
  ⟨served, ⟨state.delivered ++ served, available.drop tick.capacity⟩⟩

def advance (state : State Packet) (tick : Tick Packet) : State Packet :=
  (step state tick).next

def run (initial : State Packet) (ticks : List (Tick Packet)) : State Packet :=
  ticks.foldl advance initial

/-- The complete ordered sequence is retained, including repeated packet values. -/
theorem step_conservation (state : State Packet) (tick : Tick Packet) :
    (step state tick).next.delivered ++ (step state tick).next.pending =
      state.delivered ++ state.pending ++ tick.arrivals := by
  simp only [step]
  rw [List.append_assoc, List.take_append_drop, List.append_assoc]

theorem advance_conservation (state : State Packet) (tick : Tick Packet) :
    (advance state tick).delivered ++ (advance state tick).pending =
      state.delivered ++ state.pending ++ tick.arrivals := step_conservation state tick

theorem run_conservation (initial : State Packet) (ticks : List (Tick Packet)) :
    (run initial ticks).delivered ++ (run initial ticks).pending =
      initial.delivered ++ initial.pending ++ ticks.flatMap Tick.arrivals := by
  induction ticks generalizing initial with
  | nil => simp [run]
  | cons tick ticks ih =>
    change (run (advance initial tick) ticks).delivered ++
      (run (advance initial tick) ticks).pending = _
    rw [ih, advance_conservation]
    simp [List.append_assoc]

theorem served_prefix (state : State Packet) (tick : Tick Packet) :
    (step state tick).served ++ (step state tick).next.pending = state.pending ++ tick.arrivals :=
  List.take_append_drop _ _

theorem delivered_append (state : State Packet) (tick : Tick Packet) :
    (step state tick).next.delivered = state.delivered ++ (step state tick).served := rfl

theorem delivered_mono (state : State Packet) (tick : Tick Packet) :
    state.delivered.length ≤ (advance state tick).delivered.length := by
  simp [advance, step]

theorem backlog (state : State Packet) (tick : Tick Packet) :
    (advance state tick).pending.length =
      (state.pending.length + tick.arrivals.length) - tick.capacity := by
  simp [advance, step]

theorem service (state : State Packet) (tick : Tick Packet) :
    (step state tick).served.length = min tick.capacity (state.pending.length + tick.arrivals.length) := by
  simp [step]

theorem service_bounded (state : State Packet) (tick : Tick Packet) :
    (step state tick).served.length ≤ tick.capacity := by
  rw [service]
  exact Nat.min_le_left _ _

theorem backlog_bounded (state : State Packet) (tick : Tick Packet) :
    (advance state tick).pending.length ≤ state.pending.length + tick.arrivals.length := by
  rw [backlog]
  exact Nat.sub_le _ _

theorem backlog_nonincrease (state : State Packet) (tick : Tick Packet)
    (withinService : tick.arrivals.length ≤ tick.capacity) :
    (advance state tick).pending.length ≤ state.pending.length := by
  rw [backlog]
  omega

theorem backlog_decreases (state : State Packet) (tick : Tick Packet)
    (nonempty : 0 < state.pending.length) (spareService : tick.arrivals.length < tick.capacity) :
    (advance state tick).pending.length < state.pending.length := by
  rw [backlog]
  omega

theorem run_backlog_bounded (initial : State Packet) (ticks : List (Tick Packet))
    (withinService : ∀ tick ∈ ticks, tick.arrivals.length ≤ tick.capacity) :
    (run initial ticks).pending.length ≤ initial.pending.length := by
  induction ticks generalizing initial with
  | nil => exact Nat.le_refl _
  | cons tick ticks ih =>
    exact Nat.le_trans
      (ih (advance initial tick) (fun next member => withinService next (by simp [member])))
      (backlog_nonincrease initial tick (withinService tick (by simp)))

/-- Spare service removes at least one queued packet in each nonempty tick. -/
theorem run_backlog_progress (initial : State Packet) (ticks : List (Tick Packet))
    (spareService : ∀ tick ∈ ticks, tick.arrivals.length < tick.capacity) :
    (run initial ticks).pending.length ≤ initial.pending.length - ticks.length := by
  induction ticks generalizing initial with
  | nil => exact Nat.le_refl _
  | cons tick ticks ih =>
    have tail := ih (advance initial tick)
      (fun next member => spareService next (by simp [member]))
    have capacity := spareService tick (by simp)
    have queue := backlog initial tick
    change (run (advance initial tick) ticks).pending.length ≤ _
    simp only [List.length_cons]
    omega

theorem run_drained (initial : State Packet) (ticks : List (Tick Packet))
    (spareService : ∀ tick ∈ ticks, tick.arrivals.length < tick.capacity)
    (enoughTicks : initial.pending.length ≤ ticks.length) : (run initial ticks).pending = [] := by
  have progress := run_backlog_progress initial ticks spareService
  have empty : (run initial ticks).pending.length = 0 := by omega
  exact List.length_eq_zero_iff.mp empty

def drain (initial : State Packet) (capacity rounds : Nat) : State Packet :=
  run initial (List.replicate rounds ⟨[], capacity⟩)

theorem drain_pending (initial : State Packet) (capacity rounds : Nat) :
    (drain initial capacity rounds).pending = initial.pending.drop (rounds * capacity) := by
  induction rounds generalizing initial with
  | zero => simp [drain, run]
  | succ rounds ih =>
    change (drain (advance initial ⟨[], capacity⟩) capacity rounds).pending = _
    rw [ih]
    simp only [advance, step, List.append_nil, List.drop_drop]
    congr 1
    simp [Nat.succ_mul, Nat.add_comm]

theorem drain_delivered (initial : State Packet) (capacity rounds : Nat) :
    (drain initial capacity rounds).delivered =
      initial.delivered ++ initial.pending.take (rounds * capacity) := by
  induction rounds generalizing initial with
  | zero => simp [drain, run]
  | succ rounds ih =>
    change (drain (advance initial ⟨[], capacity⟩) capacity rounds).delivered = _
    rw [ih]
    simp only [advance, step, List.append_nil, List.append_assoc, ← List.take_add]
    congr 2
    simp [Nat.succ_mul, Nat.add_comm]

theorem drain_backlog (initial : State Packet) (capacity rounds : Nat) :
    (drain initial capacity rounds).pending.length = initial.pending.length - rounds * capacity := by
  rw [drain_pending, List.length_drop]

theorem drain_complete (initial : State Packet) (capacity rounds : Nat)
    (enoughService : initial.pending.length ≤ rounds * capacity) :
    (drain initial capacity rounds).pending = [] := by
  rw [drain_pending]
  exact List.drop_eq_nil_iff.mpr enoughService

/-- With no arrivals, positive service drains a finite queue in finitely many ticks. -/
theorem eventually_drained (initial : State Packet) (capacity : Nat) (positive : 0 < capacity) :
    ∃ rounds, (drain initial capacity rounds).pending = [] := by
  refine ⟨initial.pending.length, drain_complete initial capacity initial.pending.length ?_⟩
  exact Nat.le_mul_of_pos_right _ positive

/-- The second FIFO receives only packets served by the first FIFO. -/
def tandem (upstream downstream : State Packet) (arrivals : List Packet)
    (upstreamCapacity downstreamCapacity : Nat) : State Packet × State Packet :=
  let first := step upstream ⟨arrivals, upstreamCapacity⟩
  let second := step downstream ⟨first.served, downstreamCapacity⟩
  (first.next, second.next)

theorem tandem_conservation (upstream downstream : State Packet) (arrivals : List Packet)
    (upstreamCapacity downstreamCapacity : Nat) :
    let result := tandem upstream downstream arrivals upstreamCapacity downstreamCapacity
    result.2.delivered ++ result.2.pending ++ result.1.pending =
      downstream.delivered ++ downstream.pending ++ upstream.pending ++ arrivals := by
  dsimp only [tandem]
  rw [step_conservation]
  rw [List.append_assoc, served_prefix]
  simp only [List.append_assoc]

end Netlib.Theory.Queue
