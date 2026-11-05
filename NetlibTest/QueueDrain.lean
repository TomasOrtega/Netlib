import Netlib.Theory.QueueDrain

namespace NetlibTest.QueueDrain

open Netlib.Theory.Queue Netlib.Theory.QueueDrain

private def good (packet : Nat) : Prop := 10 ≤ packet
private def initial : State Nat := ⟨[0], [1, 1, 2]⟩
private def overloaded : Tick Nat := ⟨[10, 10], 1⟩

private theorem arrivals_clean (rounds : Nat) : CleanArrivals good (List.replicate rounds overloaded) := by
  intro tick member
  have same := List.eq_of_mem_replicate member
  subst tick
  simp [Clean, overloaded, good]

example (rounds : Nat) :
    CleanTail good (3 - rounds) (Netlib.Theory.Queue.run initial (List.replicate rounds overloaded)).pending := by
  have tail := run_tail_bound good initial (List.replicate rounds overloaded) 3
    (by simp [CleanTail, Clean, initial]) (arrivals_clean rounds)
  simpa [totalCapacity, overloaded] using tail

example : CleanPending good (Netlib.Theory.Queue.run initial (List.replicate 3 overloaded)) :=
  run_pending_clean good initial _ (arrivals_clean 3) (by decide)

example : Clean good (served (Netlib.Theory.Queue.run initial (List.replicate 3 overloaded))
    (List.replicate 4 overloaded)) :=
  served_after_prefix good initial _ _ (arrivals_clean 3) (arrivals_clean 4) (by decide)

example : served initial (List.replicate 3 overloaded) = [1, 1, 2] := by decide

example : (Netlib.Theory.Queue.run initial (List.replicate 3 overloaded)).delivered = [0, 1, 1, 2] := by decide

example : (Netlib.Theory.Queue.run initial (List.replicate 3 overloaded)).pending = [10, 10, 10, 10, 10, 10] := by decide

example : ¬Clean good (Netlib.Theory.Queue.run initial (List.replicate 3 overloaded)).delivered := by
  intro clean
  have impossible := clean 0 (by decide)
  exact Nat.not_succ_le_zero _ impossible

example : ¬CleanPending good (Netlib.Theory.Queue.run initial (List.replicate 2 overloaded)) := by
  intro clean
  have impossible := clean 2 (by decide)
  simp [good] at impossible

private theorem overload_size (state : State Nat) (rounds : Nat) :
    (Netlib.Theory.Queue.run state (List.replicate rounds overloaded)).pending.length = state.pending.length + rounds := by
  induction rounds generalizing state with
  | zero => simp [Netlib.Theory.Queue.run]
  | succ rounds ih =>
    change (Netlib.Theory.Queue.run (advance state overloaded) (List.replicate rounds overloaded)).pending.length = _
    rw [ih, backlog]
    simp only [overloaded, List.length_cons, List.length_nil]
    omega

example : ∀ rounds, (Netlib.Theory.Queue.run initial (List.replicate rounds overloaded)).pending ≠ [] := by
  intro rounds empty
  have length := overload_size initial rounds
  rw [empty] at length
  have impossible : 3 + rounds = 0 := by simpa [initial] using length.symm
  omega

example (rounds : Nat) (enough : 3 ≤ rounds) :
    (Netlib.Theory.Queue.run initial (List.replicate rounds overloaded)).pending =
      ((List.replicate rounds overloaded).flatMap Tick.arrivals).drop
        ((served initial (List.replicate rounds overloaded)).length - 3) :=
  pending_after_old_prefix initial _ (by simpa [initial, totalCapacity, overloaded] using enough)

example (ticks : List (Tick Nat)) (service : ∀ tick ∈ ticks, 2 ≤ tick.capacity) :
    ticks.length * 2 ≤ totalCapacity ticks := minCapacity_totalCapacity ticks 2 service

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  let clean := fun packet : Nat => decide (10 ≤ packet)
  for rounds in List.range 15 do
    let ticks := List.replicate rounds overloaded
    let after := Netlib.Theory.Queue.run initial ticks
    ensure (after.pending.length == 3 + rounds && !after.pending.isEmpty)
      "Sustained clean overload must not drain the whole queue."
    ensure ((after.pending.drop (3 - totalCapacity ticks)).all clean)
      "Only the remaining old prefix may contain a bad packet."
    ensure (after.pending.all clean == (3 ≤ rounds))
      "The exact service boundary must clear old packets without a premature claim."
    ensure ((served initial ticks).length == rounds)
      "The nonempty old/backlogged queue must use every service opportunity."
  let before := Netlib.Theory.Queue.run initial (List.replicate 2 overloaded)
  let boundary := step before overloaded
  ensure (boundary.served == [2] && !(boundary.served.all clean) && boundary.next.pending.all clean)
    "The batch clearing the last old packet can itself deliver that bad packet."
  let future := List.replicate 4 overloaded
  ensure ((served boundary.next future).all clean)
    "Only service after the clearing interval receives the clean-delivery guarantee."
  let after := Netlib.Theory.Queue.run boundary.next future
  ensure (!(after.delivered.all clean) && (after.delivered.drop boundary.next.delivered.length).all clean)
    "Earlier bad delivered history must remain distinct from clean future deliveries."
  let stalled := List.replicate 5 (⟨[10, 10], 0⟩ : Tick Nat)
  let stationary := Netlib.Theory.Queue.run initial stalled
  ensure ((served initial stalled).isEmpty && stationary.delivered == initial.delivered &&
      !(stationary.pending.all clean) && stationary.pending.length == 13)
    "Zero capacity must retain the old bad prefix while appending clean arrivals."
  let duplicates : State Nat := ⟨[], [10, 10, 10]⟩
  let duplicateResult := Netlib.Theory.Queue.run duplicates (List.replicate 3 overloaded)
  ensure (duplicateResult.delivered == [10, 10, 10] && duplicateResult.pending == List.replicate 6 10)
    "Identical packet values must retain FIFO multiplicity and the exact old-prefix count."
  let opportunities : List (Tick Nat) := [⟨[], 100⟩, ⟨[10, 10], 0⟩]
  let sparse : State Nat := ⟨[], [1]⟩
  ensure (totalCapacity opportunities == 100 && (served sparse opportunities).length == 1 &&
      (Netlib.Theory.Queue.run sparse opportunities).pending == [10, 10])
    "Unused capacity is not delivered traffic or service credit for later ticks."
  IO.println "Old-prefix queue drain tests passed."

end NetlibTest.QueueDrain
