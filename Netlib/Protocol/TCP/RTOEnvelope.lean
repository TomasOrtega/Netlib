import Netlib.Protocol.TCP.Recovery
import Netlib.Protocol.TCP.RTOBound

/-!
# An RTO envelope from the current clock

The finite sample cap uses elapsed time since the selected start.
Each actual timeout contributes one factor of two.
-/

namespace Netlib.Protocol.TCP.RTOEnvelope

def cap (initialRTO : Nat) (estimator : Option RTO.Estimator) (age : Nat) : Nat :=
  max initialRTO (RTO.sampleCap estimator age)

theorem cap_mono (initialRTO : Nat) (estimator : Option RTO.Estimator) (first last : Nat) (ages : first ≤ last) :
    cap initialRTO estimator first ≤ cap initialRTO estimator last := by
  apply Nat.max_le.mpr
  exact ⟨Nat.le_max_left _ _, Nat.le_trans (RTO.sampleCap_mono estimator first last ages) (Nat.le_max_right _ _)⟩

theorem cap_floor (initialRTO : Nat) (estimator : Option RTO.Estimator) (age : Nat) :
    1000 ≤ cap initialRTO estimator age :=
  Nat.le_trans (RTO.sampleCap_floor estimator age) (Nat.le_max_right _ _)

def Bound (initialRTO : Nat) (estimator : Option RTO.Estimator) (start retries : Nat) (state : Recovery.State) : Prop :=
  state.rto ≤ 2 ^ retries * cap initialRTO estimator (state.now - start)

variable {initialRTO start retries : Nat} {estimator : Option RTO.Estimator} {state after : Recovery.State}

theorem of_power (rto : state.rto = 2 ^ retries * initialRTO) : Bound initialRTO estimator start retries state := by
  unfold Bound
  rw [rto]
  exact Nat.mul_le_mul_left _ (Nat.le_max_left _ _)

theorem transport (prior : Bound initialRTO estimator start retries state)
    (rto : after.rto = state.rto) (now : after.now = state.now) : Bound initialRTO estimator start retries after := by
  unfold Bound at *
  rw [rto, now]
  exact prior

theorem sent (count : Nat) (prior : Bound initialRTO estimator start retries state) :
    Bound initialRTO estimator start retries (Recovery.sent state count) := prior

theorem advance (millis : Nat) (prior : Bound initialRTO estimator start retries state) (monotone : state.now ≤ millis) :
    Bound initialRTO estimator start retries { state with now := millis } :=
  Nat.le_trans prior (Nat.mul_le_mul_left _ (cap_mono initialRTO estimator _ _ (Nat.sub_le_sub_right monotone start)))

theorem timeout (head : Recovery.Outstanding) (rest : List Recovery.Outstanding)
    (prior : Bound initialRTO estimator start retries state) :
    Bound initialRTO estimator start (retries + 1) (Recovery.timeoutState state head rest) := by
  change 2 * state.rto ≤ 2 ^ (retries + 1) * cap initialRTO estimator (state.now - start)
  calc
    2 * state.rto ≤ 2 * (2 ^ retries * cap initialRTO estimator (state.now - start)) := Nat.mul_le_mul_left 2 prior
    _ = 2 ^ (retries + 1) * cap initialRTO estimator (state.now - start) := by
      rw [Nat.pow_succ]
      simp only [Nat.mul_assoc, Nat.mul_left_comm]

theorem observed (sample : Nat)
    (rto : state.rto = RTO.interval (RTO.observe estimator sample)) (elapsed : sample ≤ state.now - start) :
    Bound initialRTO estimator start retries state := by
  have sampleBound := RTO.interval_observe_le_sampleCap estimator sample (state.now - start) elapsed
  have capped : state.rto ≤ cap initialRTO estimator (state.now - start) :=
    rto ▸ Nat.le_trans sampleBound (Nat.le_max_right _ _)
  exact Nat.le_trans capped (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide)))

end Netlib.Protocol.TCP.RTOEnvelope
