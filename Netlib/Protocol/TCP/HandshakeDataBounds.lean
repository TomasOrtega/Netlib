import Netlib.Protocol.TCP.HandshakeTimerBounds

/-!
# Data timer bounds after actual startup samples

The finite maximum covers the absent estimator and each possible startup sample.
It permits later RTT updates without a monotonicity assumption on the estimator.
-/

namespace Netlib.Protocol.TCP.HandshakeTimer

private theorem max_mono {a b c d : Nat} (first : a ≤ c) (second : b ≤ d) : max a b ≤ max c d := by omega

def estimatorCap : Nat → Nat → Nat
  | 0, span => max (RTO.sampleCap none span) (RTO.sampleCap (some (RTO.observe none 0)) span)
  | horizon + 1, span => max (estimatorCap horizon span) (RTO.sampleCap (some (RTO.observe none (horizon + 1))) span)

theorem sampleCap_none_le (horizon span : Nat) : RTO.sampleCap none span ≤ estimatorCap horizon span := by
  induction horizon with
  | zero => exact Nat.le_max_left _ _
  | succ horizon ih => exact Nat.le_trans ih (Nat.le_max_left _ _)

theorem sampleCap_observed_le (sample horizon span : Nat) (bounded : sample ≤ horizon) :
    RTO.sampleCap (some (RTO.observe none sample)) span ≤ estimatorCap horizon span := by
  induction horizon with
  | zero =>
    have zero : sample = 0 := by omega
    subst sample
    exact Nat.le_max_right _ _
  | succ horizon ih =>
    by_cases earlier : sample ≤ horizon
    · exact Nat.le_trans (ih earlier) (Nat.le_max_left _ _)
    · have last : sample = horizon + 1 := by omega
      subst sample
      exact Nat.le_max_right _ _

theorem sampleCap_le (estimator : Option RTO.Estimator) (horizon span : Nat)
    (recorded : estimator = none ∨ ∃ sample, sample ≤ horizon ∧ estimator = some (RTO.observe none sample)) :
    RTO.sampleCap estimator span ≤ estimatorCap horizon span := by
  rcases recorded with absent | ⟨sample, bounded, present⟩
  · rw [absent]
    exact sampleCap_none_le horizon span
  · rw [present]
    exact sampleCap_observed_le sample horizon span bounded

theorem estimatorCap_mono_horizon (span : Nat) (bounded : first ≤ last) :
    estimatorCap first span ≤ estimatorCap last span := by
  induction last with
  | zero =>
    have zero : first = 0 := by omega
    subst first
    exact Nat.le_refl _
  | succ last ih =>
    by_cases earlier : first ≤ last
    · exact Nat.le_trans (ih earlier) (Nat.le_max_left _ _)
    · have same : first = last + 1 := by omega
      subst first
      exact Nat.le_refl _

theorem estimatorCap_mono_span (horizon : Nat) (bounded : first ≤ last) :
    estimatorCap horizon first ≤ estimatorCap horizon last := by
  induction horizon with
  | zero =>
    exact max_mono (RTO.sampleCap_mono none _ _ bounded) (RTO.sampleCap_mono _ _ _ bounded)
  | succ horizon ih =>
    exact max_mono ih (RTO.sampleCap_mono _ _ _ bounded)

def dataCapacity (horizon span : Nat) : Nat :=
  max (max 3000 (clockEnvelope horizon)) (estimatorCap horizon span)

theorem dataCapacity_bound (data : Data)
    (interval : data.rto ≤ max 3000 (clockEnvelope horizon))
    (recorded : data.estimator = none ∨ ∃ sample, sample ≤ horizon ∧ data.estimator = some (RTO.observe none sample)) :
    max data.rto (RTO.sampleCap data.estimator span) ≤ dataCapacity horizon span :=
  max_mono interval (sampleCap_le data.estimator horizon span recorded)

theorem dataCapacity_mono (horizons : firstHorizon ≤ lastHorizon) (spans : firstSpan ≤ lastSpan) :
    dataCapacity firstHorizon firstSpan ≤ dataCapacity lastHorizon lastSpan := by
  apply max_mono
  · exact max_mono (Nat.le_refl _) (clockEnvelope_mono horizons)
  · exact Nat.le_trans (estimatorCap_mono_horizon firstSpan horizons) (estimatorCap_mono_span lastHorizon spans)

end Netlib.Protocol.TCP.HandshakeTimer
