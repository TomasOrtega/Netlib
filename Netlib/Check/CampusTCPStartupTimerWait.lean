import Netlib.Check.CampusTCPStartupSelection
import Netlib.Check.CampusTCPRecoveryRoundRank

/-!
# Service distance for a protected startup timer

The distance counts the full clock targets and one current-generation expiry.
A full target reduces the distance and preserves the actual pending flight.
-/

namespace Netlib.Check.CampusTCPStartupTimerWait

open Protocol.TCP CampusTCPModel

namespace W
export CampusTCPRecoveryRoundMonitor (waitSlots waitSlots_zero waitSlots_mono waitSlots_tick timer_tick_distance)
end W
namespace T
export HandshakeTimer (State Flight)
end T

def remaining (state : T.State) : Nat :=
  match state.status with
  | .pending flight => flight.deadline - state.now
  | _ => 0

def distance (quantum : Nat) (state : T.State) : Nat := W.waitSlots quantum (remaining state) + 1

variable {state next : T.State} {flight : T.Flight} {quantum horizon : Nat}

theorem remaining_pending (pending : state.status = .pending flight) : remaining state = flight.deadline - state.now := by
  rw [remaining, pending]

theorem remaining_le (valid : state.Valid) (pending : state.status = .pending flight) : remaining state ≤ state.rto := by
  have fields := valid.2
  rw [pending] at fields
  rw [remaining_pending pending, fields.2.2.1]
  omega

theorem distance_le (valid : state.Valid) (pending : state.status = .pending flight) :
    distance quantum state ≤ W.waitSlots quantum state.rto + 1 :=
  Nat.add_le_add_right (W.waitSlots_mono (remaining_le valid pending)) 1

theorem elapsed_distance_le (valid : state.Valid) (pending : state.status = .pending flight)
    (bounded : state.BoundedStartup) (clock : state.now ≤ horizon) :
    distance quantum state ≤ W.waitSlots quantum (1000 + horizon) + 1 := by
  have interval := HandshakeTimer.pending_interval_clock valid bounded.1 pending
  have initial := bounded.2
  rw [pending] at initial
  rw [initial.1] at interval
  have times : state.rto ≤ 1000 + horizon := by omega
  exact Nat.le_trans (distance_le valid pending) (Nat.add_le_add_right (W.waitSlots_mono times) 1)

theorem target_monotone (early : state.now < flight.deadline) :
    state.now ≤ min (state.now + quantum) flight.deadline := by omega

theorem target_remaining (pending : state.status = .pending flight) :
    remaining { state with now := min (state.now + quantum) flight.deadline } = remaining state - quantum := by
  simp only [remaining, pending]
  exact W.timer_tick_distance state.now flight.deadline quantum

theorem target_strict (positive : 0 < quantum) (pending : state.status = .pending flight)
    (early : state.now < flight.deadline) :
    distance quantum { state with now := min (state.now + quantum) flight.deadline } < distance quantum state := by
  have before : 0 < remaining state := by rw [remaining_pending pending]; omega
  unfold distance
  rw [target_remaining pending]
  exact Nat.add_lt_add_right (W.waitSlots_tick positive before) 1

theorem due_distance (positive : 0 < quantum) (pending : state.status = .pending flight)
    (due : flight.deadline ≤ state.now) : distance quantum state = 1 := by
  rw [distance, remaining_pending pending, Nat.sub_eq_zero_of_le due, W.waitSlots_zero positive]

end Netlib.Check.CampusTCPStartupTimerWait
