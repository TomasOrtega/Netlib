import Init.Data.Rat.Lemmas

/-!
# Exact RTT estimates and millisecond retransmission intervals

The selected coefficients are those of RFC 6298.
The final interval rounds up to milliseconds and has a one-second floor.
An RTT sample requires separate transmission and ACK evidence.
-/

namespace Netlib.Protocol.TCP.RTO

structure Estimator where
  srtt : Rat
  variance : Rat
  deriving Repr, DecidableEq

instance : BEq Estimator := ⟨fun first second => decide (first = second)⟩

def first (sample : Nat) : Estimator :=
  ⟨sample, (sample : Rat) / 2⟩

def update (before : Estimator) (sample : Nat) : Estimator := {
  srtt := (7 : Rat) / 8 * before.srtt + (sample : Rat) / 8
  variance := (3 : Rat) / 4 * before.variance + (before.srtt - sample).abs / 4 }

def observe (before : Option Estimator) (sample : Nat) : Estimator :=
  match before with
  | none => first sample
  | some value => update value sample

def exact (estimate : Estimator) (granularity : Nat := 1) : Rat :=
  estimate.srtt + max (granularity : Rat) (4 * estimate.variance)

def interval (estimate : Estimator) (granularity : Nat := 1) : Nat :=
  max 1000 (exact estimate granularity).ceil.toNat

theorem interval_floor (estimate : Estimator) (granularity : Nat) :
    1000 ≤ interval estimate granularity := Nat.le_max_left _ _

theorem interval_conservative (estimate : Estimator) (granularity : Nat) :
    exact estimate granularity ≤ (interval estimate granularity : Rat) := by
  have rounded : exact estimate granularity ≤ ((exact estimate granularity).ceil.toNat : Rat) := by
    apply Rat.le_trans Rat.le_ceil
    apply Rat.intCast_le_intCast.mpr
    exact Int.self_le_toNat _
  apply Rat.le_trans rounded
  apply Rat.natCast_le_natCast.mpr
  exact Nat.le_max_right _ _

theorem first_values (sample : Nat) :
    (first sample).srtt = (sample : Rat) ∧ (first sample).variance = (sample : Rat) / 2 :=
  ⟨rfl, rfl⟩

theorem update_values (before : Estimator) (sample : Nat) :
    (update before sample).variance =
      (3 : Rat) / 4 * before.variance + (before.srtt - sample).abs / 4 ∧
    (update before sample).srtt = (7 : Rat) / 8 * before.srtt + (sample : Rat) / 8 :=
  ⟨rfl, rfl⟩

end Netlib.Protocol.TCP.RTO
