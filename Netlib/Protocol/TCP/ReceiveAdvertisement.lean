import Netlib.Protocol.TCP.SequenceSpace

/-!
# Receiver window advertisement

The byte frontier and offered right edge use one local receive epoch.
Receiving data holds that edge. Application reads change free space separately.
Only successful output commits a larger offered edge.
The selected SWS threshold is half the capacity, rounded up, or the outgoing MSS.
-/

namespace Netlib.Protocol.TCP.ReceiveAdvertisement

structure State where
  frontier : Nat
  edge : Nat
  deriving Repr, BEq, DecidableEq

def State.window (state : State) : Nat := state.edge - state.frontier

def State.Valid (state : State) (free : Nat) : Prop :=
  state.frontier ≤ state.edge ∧ state.window ≤ free

instance (state : State) (free : Nat) : Decidable (state.Valid free) := by
  unfold State.Valid
  infer_instance

def initial (capacity : Nat) : State := ⟨0, capacity⟩

def threshold (capacity outgoingMSS : Nat) : Nat :=
  min ((capacity + 1) / 2) outgoingMSS

def candidate (state : State) (capacity free outgoingMSS : Nat) : Nat :=
  if threshold capacity outgoingMSS ≤ free - state.window then free else state.window

def growth (state : State) (capacity free outgoingMSS : Nat) : Bool :=
  decide (state.window < candidate state capacity free outgoingMSS)

def consume (state : State) (count : Nat) : State :=
  { state with frontier := state.frontier + count }

def commit (state : State) (capacity free outgoingMSS : Nat) : State :=
  { state with edge := state.frontier + candidate state capacity free outgoingMSS }

theorem initial_valid (capacity : Nat) : (initial capacity).Valid capacity := by
  simp [initial, State.Valid, State.window]

theorem initial_window (capacity : Nat) : (initial capacity).window = capacity := rfl

theorem consume_edge (state : State) (count : Nat) : (consume state count).edge = state.edge := rfl

theorem consume_window (state : State) (count : Nat) :
    (consume state count).window = state.window - count := by
  simp only [consume, State.window]
  omega

theorem consume_valid (state : State) (free count : Nat) (valid : state.Valid free)
    (fits : count ≤ state.window) : (consume state count).Valid (free - count) := by
  obtain ⟨edge, room⟩ := valid
  refine ⟨?_, ?_⟩
  · change state.frontier + count ≤ state.edge
    unfold State.window at fits
    omega
  · rw [consume_window]
    omega

theorem more_free_valid (state : State) (before after : Nat) (valid : state.Valid before)
    (released : before ≤ after) : state.Valid after := ⟨valid.1, Nat.le_trans valid.2 released⟩

theorem candidate_bounds (state : State) (capacity free outgoingMSS : Nat) (valid : state.Valid free) :
    state.window ≤ candidate state capacity free outgoingMSS ∧
      candidate state capacity free outgoingMSS ≤ free := by
  have room := valid.2
  unfold candidate
  split <;> exact ⟨by omega, by omega⟩

theorem candidate_suppressed (state : State) (capacity free outgoingMSS : Nat)
    (small : free - state.window < threshold capacity outgoingMSS) :
    candidate state capacity free outgoingMSS = state.window := by
  simp only [candidate, Nat.not_le.mpr small, ite_false]

theorem candidate_full (state : State) (capacity free outgoingMSS : Nat)
    (ready : threshold capacity outgoingMSS ≤ free - state.window) :
    candidate state capacity free outgoingMSS = free := by
  simp only [candidate, ready, ite_true]

theorem candidate_growth (state : State) (capacity free outgoingMSS : Nat)
    (grew : state.window < candidate state capacity free outgoingMSS) :
    threshold capacity outgoingMSS ≤ free - state.window ∧
      candidate state capacity free outgoingMSS = free := by
  unfold candidate at grew ⊢
  split at grew
  · rename_i ready
    exact ⟨ready, ite_eq_left ready⟩
  · omega

theorem commit_frontier (state : State) (capacity free outgoingMSS : Nat) :
    (commit state capacity free outgoingMSS).frontier = state.frontier := rfl

theorem commit_window (state : State) (capacity free outgoingMSS : Nat) :
    (commit state capacity free outgoingMSS).window = candidate state capacity free outgoingMSS := by
  simp [commit, State.window]

theorem commit_valid (state : State) (capacity free outgoingMSS : Nat) (valid : state.Valid free) :
    (commit state capacity free outgoingMSS).Valid free := by
  exact ⟨by simp [commit], by rw [commit_window]; exact (candidate_bounds state capacity free outgoingMSS valid).2⟩

theorem commit_edge_monotone (state : State) (capacity free outgoingMSS : Nat) (valid : state.Valid free) :
    state.edge ≤ (commit state capacity free outgoingMSS).edge := by
  have size := (candidate_bounds state capacity free outgoingMSS valid).1
  have edge := valid.1
  change state.edge ≤ state.frontier + candidate state capacity free outgoingMSS
  unfold State.window at size
  omega

theorem threshold_positive (capacity outgoingMSS : Nat) (buffer : 0 < capacity) (mss : 0 < outgoingMSS) :
    0 < threshold capacity outgoingMSS := by
  unfold threshold
  have half : 0 < (capacity + 1) / 2 := by omega
  exact Nat.lt_min.mpr ⟨half, mss⟩

end Netlib.Protocol.TCP.ReceiveAdvertisement
