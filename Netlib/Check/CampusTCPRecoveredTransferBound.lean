import Netlib.Check.CampusTCPRecoveredTimerBound
import Netlib.Check.CampusTCPTwoTransferExchangeBound

/-!
# Transfer slots from the raw startup horizon

Both legs use the finite maximum over actual startup estimator states.
The remaining data allowance is at most the whole execution allowance.
-/

namespace Netlib.Check.CampusTCPRecoveredTransferBound

open Protocol.TCP CampusTCPModel CampusTCPRecoveredSetup

namespace P
export CampusTCPRecoveredTransferTask (Task)
end P
namespace E
export CampusTCPRecoveredTwoWriteEndpoints (cut)
end E
namespace C
export CampusTCPTwoTransferRecoveryBounded (coarse)
end C
namespace B
export CampusTCPTwoTransferExchangeBound (wholeSlots)
end B

def capacity (quantum setupSlots bound : Nat) : Nat :=
  HandshakeTimer.dataCapacity (quantum * setupSlots) ((24 * bound) * quantum)

def slots (quantum allowance setupSlots bound : Nat) : Nat :=
  (41 + 2 * C.coarse quantum allowance (capacity quantum setupSlots bound)) * bound

private theorem coarse_mono {firstAllowance lastAllowance firstCapacity lastCapacity : Nat}
    (quantum : Nat) (counts : firstAllowance ≤ lastAllowance) (sizes : firstCapacity ≤ lastCapacity) :
    C.coarse quantum firstAllowance firstCapacity ≤ C.coarse quantum lastAllowance lastCapacity := by
  have powers := Nat.mul_le_mul (Nat.pow_le_pow_of_le (by decide : 1 < 2) counts) sizes
  have waits := CampusTCPRecoveryRoundMonitor.waitSlots_mono (quantum := quantum) powers
  have reserves := Nat.mul_le_mul (Nat.add_le_add_right counts 1) waits
  have retries := Nat.mul_le_mul_left 8 counts
  unfold C.coarse
  exact Nat.add_le_add_right (Nat.add_le_add reserves retries) 7

variable {input : Input} {events : List Event} {report : Report input events}
variable {ready : DrainReady report} {lower upper reverseLower reverseUpper : List UInt8}
variable (task : P.Task ready lower upper reverseLower reverseUpper)
variable {quantum allowance setupSlots bound : Nat}

theorem Task.whole_slots_le
    (actions : CampusTCPStartupClockBounds.Actions quantum (E.cut task.prepared).report.steps)
    (within : (E.cut task.prepared).report.steps.length ≤ setupSlots) :
    B.wholeSlots task.built.initial quantum
      (allowance - report.final.custody.dropped) bound ≤ slots quantum allowance setupSlots bound := by
  have sender := CampusTCPRecoveredTimerBound.Task.sender_capacity task actions within
    (span := (24 * bound) * quantum)
  have receiver := CampusTCPRecoveredTimerBound.Task.receiver_capacity task actions within
    (span := (16 * bound) * quantum)
  have spans : (16 * bound) * quantum ≤ (24 * bound) * quantum := by
    exact Nat.mul_le_mul_right quantum (Nat.mul_le_mul_right bound (by decide : 16 ≤ 24))
  have widened := HandshakeTimer.dataCapacity_mono (Nat.le_refl (quantum * setupSlots)) spans
  have reverse := Nat.le_trans receiver widened
  have forwardCoarse := coarse_mono quantum (Nat.sub_le allowance report.final.custody.dropped) sender
  have reverseCoarse := coarse_mono quantum (Nat.sub_le allowance report.final.custody.dropped) reverse
  have forwardTimes := Nat.mul_le_mul_right bound forwardCoarse
  have reverseTimes := Nat.mul_le_mul_right bound reverseCoarse
  change 24 * bound + C.coarse quantum (allowance - report.final.custody.dropped)
      (max task.built.initial.senderState.idle.recovery.rto
        (RTO.sampleCap task.built.initial.senderState.idle.recovery.estimator ((24 * bound) * quantum))) * bound + bound +
    (16 * bound + C.coarse quantum (allowance - report.final.custody.dropped)
      (max task.built.initial.receiverState.idle.recovery.rto
        (RTO.sampleCap task.built.initial.receiverState.idle.recovery.estimator ((16 * bound) * quantum))) * bound) ≤ _
  unfold slots capacity
  simp only [Nat.mul_assoc] at forwardTimes reverseTimes
  simp only [Nat.add_mul, Nat.mul_assoc]
  omega

end Netlib.Check.CampusTCPRecoveredTransferBound
