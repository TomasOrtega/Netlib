import Netlib.Theory.Queue

namespace NetlibTest.Queue

open Netlib.Theory.Queue

private def initial : State Nat := ⟨[99], [10, 11, 12, 13]⟩

private def burst : List (Tick Nat) := [⟨[14, 15], 2⟩, ⟨[], 1⟩, ⟨[16], 1⟩]

example : (step initial ⟨[14, 15], 2⟩).served = [10, 11] := by decide

example : run initial burst = ⟨[99, 10, 11, 12, 13], [14, 15, 16]⟩ := by decide

example : drain (run initial burst) 2 2 = ⟨[99, 10, 11, 12, 13, 14, 15, 16], []⟩ := by decide

example : (run initial burst).delivered ++ (run initial burst).pending =
    initial.delivered ++ initial.pending ++ burst.flatMap Tick.arrivals := run_conservation _ _

example : (step (⟨[], [1, 1, 2]⟩ : State Nat) ⟨[2, 3], 3⟩).served = [1, 1, 2] := by decide

example : (step (⟨[], [1, 1, 2]⟩ : State Nat) ⟨[2, 3], 3⟩).next.pending = [2, 3] := by decide

example : (step (⟨[], [1, 2]⟩ : State Nat) ⟨[3], 20⟩).served = [1, 2, 3] := by decide

example : (step initial ⟨[14, 15], 0⟩).next = ⟨[99], [10, 11, 12, 13, 14, 15]⟩ := by decide

example : (run initial [⟨[14, 15], 3⟩, ⟨[16], 2⟩]).pending.length ≤ initial.pending.length :=
  run_backlog_bounded initial [⟨[14, 15], 3⟩, ⟨[16], 2⟩] (by
    intro tick member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide)

example : (run initial [⟨[14], 2⟩, ⟨[15], 2⟩, ⟨[], 1⟩, ⟨[], 1⟩]).pending = [] :=
  run_drained initial [⟨[14], 2⟩, ⟨[15], 2⟩, ⟨[], 1⟩, ⟨[], 1⟩] (by
    intro tick member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide) (by decide)

example : (drain initial 2 2).pending = [] := drain_complete initial 2 2 (by decide)

example : ∃ rounds, (drain initial 1 rounds).pending = [] := eventually_drained initial 1 (by decide)

theorem zero_service_stalls (state : State Packet) (rounds : Nat) :
    (drain state 0 rounds).pending = state.pending := by simp [drain_pending]

private def overloaded : Tick Nat := ⟨[7, 8], 1⟩

/-- Two arrivals and one service slot add one pending packet per tick. -/
theorem overload_grows (state : State Nat) (rounds : Nat) :
    (run state (List.replicate rounds overloaded)).pending.length = state.pending.length + rounds := by
  induction rounds generalizing state with
  | zero => simp [run]
  | succ rounds ih =>
    change (run (advance state overloaded) (List.replicate rounds overloaded)).pending.length = _
    rw [ih, backlog]
    simp only [overloaded, List.length_cons, List.length_nil]
    omega

example : ∀ rounds, (run (⟨[], [0]⟩ : State Nat) (List.replicate rounds overloaded)).pending ≠ [] := by
  intro rounds empty
  have size := overload_grows (⟨[], [0]⟩ : State Nat) rounds
  simp [empty] at size
  omega

private def distinctOverload : List (Tick Nat) :=
  (List.range 5).map fun round => ⟨[2 * round, 2 * round + 1], 1⟩

example : run ({} : State Nat) distinctOverload = ⟨[0, 1, 2, 3, 4], [5, 6, 7, 8, 9]⟩ := by decide

private def upstream : State Nat := ⟨[], [2, 3, 4]⟩
private def downstream : State Nat := ⟨[0], [1]⟩

example : tandem upstream downstream [5, 6] 2 1 =
    (⟨[2, 3], [4, 5, 6]⟩, ⟨[0, 1], [2, 3]⟩) := by decide

example :
    let result := tandem upstream downstream [5, 6] 2 1
    result.2.delivered ++ result.2.pending ++ result.1.pending = [0, 1, 2, 3, 4, 5, 6] := by
  dsimp only
  rw [tandem_conservation]
  rfl

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  let result := Netlib.Theory.Queue.run initial burst
  ensure (result.delivered == [99, 10, 11, 12, 13] && result.pending == [14, 15, 16])
    "The FIFO must retain arrival order across service ticks."
  let drained := drain result 2 2
  ensure (drained.delivered == [99, 10, 11, 12, 13, 14, 15, 16] && drained.pending.isEmpty)
    "Positive service must drain the finite burst without further arrivals."
  ensure ((drain initial 0 100).pending == initial.pending)
    "Zero service must retain the pending packets."
  for rounds in List.range 20 do
    let result := Netlib.Theory.Queue.run ({} : State Nat) (List.replicate rounds overloaded)
    ensure (result.pending.length == rounds) "Sustained overload must grow the queue."
    ensure (result.delivered ++ result.pending == (List.replicate rounds overloaded).flatMap Tick.arrivals)
      "An overloaded FIFO must still conserve the complete packet sequence."
  let chained := tandem upstream downstream [5, 6] 2 1
  ensure (chained.2.delivered ++ chained.2.pending ++ chained.1.pending == [0, 1, 2, 3, 4, 5, 6])
    "FIFO composition must conserve the end-to-end packet sequence."
  IO.println "Queue tests passed."

end NetlibTest.Queue
