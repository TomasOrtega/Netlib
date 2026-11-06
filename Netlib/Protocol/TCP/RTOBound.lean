import Netlib.Protocol.TCP.RTO

/-!
# A finite cap for bounded RTT samples

The cap includes every sample within the supplied age.
It does not require the estimator update to be monotone.
-/

namespace Netlib.Protocol.TCP.RTO

def sampleCap (before : Option Estimator) : Nat → Nat
  | 0 => interval (observe before 0)
  | age + 1 => max (sampleCap before age) (interval (observe before (age + 1)))

theorem interval_observe_le_sampleCap (before : Option Estimator) (sample age : Nat)
    (bounded : sample ≤ age) : interval (observe before sample) ≤ sampleCap before age := by
  induction age with
  | zero =>
    have zero : sample = 0 := by omega
    subst sample
    exact Nat.le_refl _
  | succ age ih =>
    by_cases earlier : sample ≤ age
    · exact Nat.le_trans (ih earlier) (Nat.le_max_left _ _)
    · have last : sample = age + 1 := by omega
      subst sample
      exact Nat.le_max_right _ _

theorem sampleCap_floor (before : Option Estimator) (age : Nat) :
    1000 ≤ sampleCap before age :=
  Nat.le_trans (interval_floor (observe before 0) 1)
    (interval_observe_le_sampleCap before 0 age (Nat.zero_le _))

theorem sampleCap_mono (before : Option Estimator) (first last : Nat) (ages : first ≤ last) :
    sampleCap before first ≤ sampleCap before last := by
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

end Netlib.Protocol.TCP.RTO
