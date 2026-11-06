import Netlib.Check.CampusTCPTwoExchangeBound
import Netlib.Check.CampusTCPTwoReverseGeometry

/-!
# The exchange deadline from the initial endpoints

The static reverse allowance uses the original global allowance.
The actual reverse bound can only be smaller.
-/

namespace Netlib.Check.CampusTCPTwoExchangeBoundSetup

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoExchangeBound

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}

def forwardSlots (initial : TwoWriteInitial cut sender gateway lower upper) (quantum allowance bound : Nat) : Nat :=
  CampusTCPTwoProgressRecoveryBounded.boundSlots initial quantum allowance bound

def reverseSlots (initial : TwoWriteInitial cut sender gateway lower upper) (quantum allowance bound : Nat) : Nat :=
  legSlots initial.receiverState.idle.recovery.rto initial.receiverState.idle.recovery.estimator quantum allowance bound

def boundSlots (initial : TwoWriteInitial cut sender gateway lower upper) (quantum allowance bound : Nat) : Nat :=
  forwardSlots initial quantum allowance bound + bound + reverseSlots initial quantum allowance bound

theorem boundSlots_eq_wholeSlots (initial : TwoWriteInitial cut sender gateway lower upper) (quantum allowance bound : Nat) :
    boundSlots initial quantum allowance bound =
      wholeSlots initial.senderState.idle.recovery.rto initial.senderState.idle.recovery.estimator
        initial.receiverState.idle.recovery.rto initial.receiverState.idle.recovery.estimator quantum allowance bound := rfl

variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance bound : Nat}
variable {monitor : CampusTCPTwoProgressMonitor.Monitor} {reverseLower reverseUpper : List UInt8} {actual : Step input}
variable {forward : CampusTCPTwoProgressEvidence.Complete initial native quantum allowance current monitor}

theorem actual_reverse_le (start : CampusTCPTwoReverseGeometry.Started forward reverseLower reverseUpper actual) :
    CampusTCPTwoProgressRecoveryBounded.boundSlots start.reverseInitial quantum (allowance - monitor.drops.length) bound ≤
      reverseSlots initial quantum allowance bound := by
  rw [boundSlots_eq_legSlots, start.reverse_rto, start.reverse_estimator]
  exact remaining_legSlots _ _ _ _ _ _

end Netlib.Check.CampusTCPTwoExchangeBoundSetup
