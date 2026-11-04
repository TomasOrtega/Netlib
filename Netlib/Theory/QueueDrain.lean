import Netlib.Theory.Queue

/-!
# Clearing an old FIFO prefix

Clean arrivals cannot overtake the initial prefix, even under sustained overload.
Capacity counts service opportunities, not elapsed time or delivered history.
-/

namespace Netlib.Theory.QueueDrain

universe u
variable {Packet : Type u}

open Queue

def Clean (property : Packet → Prop) (packets : List Packet) : Prop :=
  ∀ packet ∈ packets, property packet

def CleanTail (property : Packet → Prop) (oldBound : Nat) (pending : List Packet) : Prop :=
  Clean property (pending.drop oldBound)

def CleanPending (property : Packet → Prop) (state : State Packet) : Prop :=
  Clean property state.pending

def CleanArrivals (property : Packet → Prop) (ticks : List (Tick Packet)) : Prop :=
  ∀ tick ∈ ticks, Clean property tick.arrivals

def totalCapacity (ticks : List (Tick Packet)) : Nat := (ticks.map Tick.capacity).sum

theorem CleanTail.mono (property : Packet → Prop) (pending : List Packet) (oldBound later : Nat)
    (clean : CleanTail property oldBound pending) (beyond : oldBound ≤ later) :
    CleanTail property later pending := by
  intro packet member
  have split : pending.drop later = (pending.drop oldBound).drop (later - oldBound) := by
    rw [List.drop_drop]
    congr 1
    omega
  rw [split] at member
  exact clean packet (List.mem_of_mem_drop member)

theorem step_tail_bound (property : Packet → Prop) (state : State Packet) (tick : Tick Packet)
    (oldBound : Nat) (pending : CleanTail property oldBound state.pending)
    (arrivals : Clean property tick.arrivals) :
    CleanTail property (oldBound - tick.capacity) (advance state tick).pending := by
  have available : CleanTail property oldBound (state.pending ++ tick.arrivals) := by
    intro packet member
    rw [List.drop_append] at member
    rcases List.mem_append.mp member with prior | arrived
    · exact pending packet prior
    · exact arrivals packet (List.mem_of_mem_drop arrived)
  have later := available.mono property _ _ (tick.capacity + (oldBound - tick.capacity)) (by omega)
  simpa only [CleanTail, advance, step, List.drop_drop] using later

theorem run_tail_bound (property : Packet → Prop) (initial : State Packet) (ticks : List (Tick Packet))
    (oldBound : Nat) (pending : CleanTail property oldBound initial.pending)
    (arrivals : CleanArrivals property ticks) :
    CleanTail property (oldBound - totalCapacity ticks) (Queue.run initial ticks).pending := by
  induction ticks generalizing initial oldBound with
  | nil => simpa [Queue.run, totalCapacity] using pending
  | cons tick ticks ih =>
    have next := step_tail_bound property initial tick oldBound pending (arrivals tick (by simp))
    have tail := ih (advance initial tick) (oldBound - tick.capacity) next
      (fun later member => arrivals later (List.mem_cons_of_mem _ member))
    simpa [Queue.run, totalCapacity, Nat.sub_sub] using tail

theorem run_pending_clean (property : Packet → Prop) (initial : State Packet) (ticks : List (Tick Packet))
    (arrivals : CleanArrivals property ticks) (enough : initial.pending.length ≤ totalCapacity ticks) :
    CleanPending property (Queue.run initial ticks) := by
  have initialTail : CleanTail property initial.pending.length initial.pending := by
    simp [CleanTail, Clean]
  have result := run_tail_bound property initial ticks initial.pending.length initialTail arrivals
  simpa [CleanTail, CleanPending, Nat.sub_eq_zero_of_le enough] using result

theorem step_clean (property : Packet → Prop) (state : State Packet) (tick : Tick Packet)
    (pending : CleanPending property state) (arrivals : Clean property tick.arrivals) :
    Clean property (step state tick).served ∧ CleanPending property (advance state tick) := by
  have available : Clean property (state.pending ++ tick.arrivals) := by
    intro packet member
    rcases List.mem_append.mp member with prior | arrived
    · exact pending packet prior
    · exact arrivals packet arrived
  constructor
  · intro packet member
    exact available packet (List.mem_of_mem_take member)
  · intro packet member
    exact available packet (List.mem_of_mem_drop member)

/-- Only service performed during these ticks, excluding earlier delivered history. -/
def served (initial : State Packet) : List (Tick Packet) → List Packet
  | [] => []
  | tick :: ticks => (step initial tick).served ++ served (advance initial tick) ticks

theorem run_delivered (initial : State Packet) (ticks : List (Tick Packet)) :
    (Queue.run initial ticks).delivered = initial.delivered ++ served initial ticks := by
  induction ticks generalizing initial with
  | nil => simp [Queue.run, served]
  | cons tick ticks ih =>
    change (Queue.run (advance initial tick) ticks).delivered = _
    rw [ih]
    simp [advance, Queue.delivered_append, served, List.append_assoc]

theorem served_pending (initial : State Packet) (ticks : List (Tick Packet)) :
    served initial ticks ++ (Queue.run initial ticks).pending =
      initial.pending ++ ticks.flatMap Tick.arrivals := by
  have conserved := Queue.run_conservation initial ticks
  rw [run_delivered] at conserved
  simp only [List.append_assoc] at conserved
  exact List.append_cancel_left conserved

theorem served_append (initial : State Packet) (prior future : List (Tick Packet)) :
    served initial (prior ++ future) =
      served initial prior ++ served (Queue.run initial prior) future := by
  induction prior generalizing initial with
  | nil => simp [served, Queue.run]
  | cons tick prior ih =>
    simp only [List.cons_append, served]
    rw [ih]
    simp only [List.append_assoc]
    rfl

theorem served_length_le_capacity (initial : State Packet) (ticks : List (Tick Packet)) :
    (served initial ticks).length ≤ totalCapacity ticks := by
  induction ticks generalizing initial with
  | nil => simp [served, totalCapacity]
  | cons tick ticks ih =>
    have head := Queue.service_bounded initial tick
    have tail := ih (advance initial tick)
    simp only [served, List.length_append, totalCapacity, List.map_cons, List.sum_cons]
    exact Nat.add_le_add head tail

theorem served_length_lower (initial : State Packet) (ticks : List (Tick Packet)) :
    min initial.pending.length (totalCapacity ticks) ≤ (served initial ticks).length := by
  induction ticks generalizing initial with
  | nil => simp [served, totalCapacity]
  | cons tick ticks ih =>
    have tail := ih (advance initial tick)
    simp only [totalCapacity] at tail
    have service := Queue.service initial tick
    have backlog := Queue.backlog initial tick
    simp only [served, List.length_append, totalCapacity, List.map_cons, List.sum_cons]
    omega

theorem pending_after_old_prefix (initial : State Packet) (ticks : List (Tick Packet))
    (enough : initial.pending.length ≤ totalCapacity ticks) :
    (Queue.run initial ticks).pending =
      (ticks.flatMap Tick.arrivals).drop ((served initial ticks).length - initial.pending.length) := by
  have servedEnough := served_length_lower initial ticks
  rw [Nat.min_eq_left enough] at servedEnough
  have remaining := congrArg (fun packets => packets.drop (served initial ticks).length)
    (served_pending initial ticks)
  rw [List.drop_left, List.drop_append, List.drop_eq_nil_iff.mpr servedEnough, List.nil_append] at remaining
  exact remaining

theorem served_clean (property : Packet → Prop) (initial : State Packet) (ticks : List (Tick Packet))
    (pending : CleanPending property initial) (arrivals : CleanArrivals property ticks) :
    Clean property (served initial ticks) := by
  induction ticks generalizing initial with
  | nil => simp [served, Clean]
  | cons tick ticks ih =>
    obtain ⟨head, next⟩ := step_clean property initial tick pending (arrivals tick (by simp))
    have tail := ih (advance initial tick) next
      (fun later member => arrivals later (List.mem_cons_of_mem _ member))
    intro packet member
    rcases List.mem_append.mp member with early | later
    · exact head packet early
    · exact tail packet later

theorem served_after_prefix (property : Packet → Prop) (initial : State Packet)
    (prior future : List (Tick Packet)) (prefixArrivals : CleanArrivals property prior)
    (suffixArrivals : CleanArrivals property future)
    (enough : initial.pending.length ≤ totalCapacity prior) :
    Clean property (served (Queue.run initial prior) future) :=
  served_clean property _ future (run_pending_clean property initial prior prefixArrivals enough) suffixArrivals

theorem minCapacity_totalCapacity (ticks : List (Tick Packet)) (minimum : Nat)
    (service : ∀ tick ∈ ticks, minimum ≤ tick.capacity) :
    ticks.length * minimum ≤ totalCapacity ticks := by
  induction ticks with
  | nil => simp [totalCapacity]
  | cons tick ticks ih =>
    have head := service tick (by simp)
    have tail := ih (fun later member => service later (List.mem_cons_of_mem _ member))
    simp only [totalCapacity] at tail
    simp only [List.length_cons, Nat.succ_mul, totalCapacity, List.map_cons, List.sum_cons]
    omega

end Netlib.Theory.QueueDrain
