import Netlib.Check.CampusTCPTwoProgressRecoveryBounded

/-!
# A static bound for two consecutive legs

Each leg uses its initial RTO and estimator.
Unused drop credit can only reduce the reverse leg's bound.
-/

namespace Netlib.Check.CampusTCPTwoExchangeBound

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart

def legCapacity (rto : Nat) (estimator : Option RTO.Estimator) (quantum bound : Nat) : Nat :=
  max rto (RTO.sampleCap estimator ((16 * bound) * quantum))

def legSlots (rto : Nat) (estimator : Option RTO.Estimator) (quantum allowance bound : Nat) : Nat :=
  16 * bound + ((allowance + 1) * CampusTCPTwoProgressTimer.waitSlots quantum
    (2 ^ allowance * legCapacity rto estimator quantum bound) + 8 * allowance + 7) * bound

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}

theorem legSlots_eq_boundSlots (initial : TwoWriteInitial cut sender gateway lower upper) (quantum allowance bound : Nat) :
    legSlots initial.senderState.idle.recovery.rto initial.senderState.idle.recovery.estimator quantum allowance bound =
      CampusTCPTwoProgressRecoveryBounded.boundSlots initial quantum allowance bound := rfl

theorem boundSlots_eq_legSlots (initial : TwoWriteInitial cut sender gateway lower upper) (quantum allowance bound : Nat) :
    CampusTCPTwoProgressRecoveryBounded.boundSlots initial quantum allowance bound =
      legSlots initial.senderState.idle.recovery.rto initial.senderState.idle.recovery.estimator quantum allowance bound := rfl

theorem coarse_mono_allowance (quantum capacity : Nat) {first last : Nat} (counts : first ≤ last) :
    CampusTCPTwoProgressRecoveryBounded.coarse quantum first capacity ≤
      CampusTCPTwoProgressRecoveryBounded.coarse quantum last capacity := by
  have powers : 2 ^ first * capacity ≤ 2 ^ last * capacity :=
    Nat.mul_le_mul_right capacity (Nat.pow_le_pow_of_le (by decide) counts)
  have slots := CampusTCPRecoveryRoundMonitor.waitSlots_mono (quantum := quantum) powers
  have reserve := Nat.mul_le_mul (Nat.add_le_add_right counts 1) slots
  have timeouts := Nat.mul_le_mul_left 8 counts
  unfold CampusTCPTwoProgressRecoveryBounded.coarse
  exact Nat.add_le_add_right (Nat.add_le_add reserve timeouts) 7

theorem legSlots_mono_allowance (rto : Nat) (estimator : Option RTO.Estimator) (quantum bound : Nat)
    {first last : Nat} (counts : first ≤ last) :
    legSlots rto estimator quantum first bound ≤ legSlots rto estimator quantum last bound := by
  change 16 * bound + CampusTCPTwoProgressRecoveryBounded.coarse quantum first
    (legCapacity rto estimator quantum bound) * bound ≤ _
  exact Nat.add_le_add_left (Nat.mul_le_mul_right bound (coarse_mono_allowance quantum _ counts)) _

theorem remaining_legSlots (rto : Nat) (estimator : Option RTO.Estimator) (quantum allowance bound spent : Nat) :
    legSlots rto estimator quantum (allowance - spent) bound ≤ legSlots rto estimator quantum allowance bound :=
  legSlots_mono_allowance rto estimator quantum bound (Nat.sub_le allowance spent)

def wholeSlots (forwardRTO : Nat) (forwardEstimator : Option RTO.Estimator)
    (reverseRTO : Nat) (reverseEstimator : Option RTO.Estimator) (quantum allowance bound : Nat) : Nat :=
  legSlots forwardRTO forwardEstimator quantum allowance bound + bound +
    legSlots reverseRTO reverseEstimator quantum allowance bound

theorem wholeSlots_mono_allowance (forwardRTO : Nat) (forwardEstimator : Option RTO.Estimator)
    (reverseRTO : Nat) (reverseEstimator : Option RTO.Estimator) (quantum bound : Nat)
    {first last : Nat} (counts : first ≤ last) :
    wholeSlots forwardRTO forwardEstimator reverseRTO reverseEstimator quantum first bound ≤
      wholeSlots forwardRTO forwardEstimator reverseRTO reverseEstimator quantum last bound :=
  Nat.add_le_add
    (Nat.add_le_add_right (legSlots_mono_allowance forwardRTO forwardEstimator quantum bound counts) bound)
    (legSlots_mono_allowance reverseRTO reverseEstimator quantum bound counts)

end Netlib.Check.CampusTCPTwoExchangeBound
