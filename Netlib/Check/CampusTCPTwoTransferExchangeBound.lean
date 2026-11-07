import Netlib.Check.CampusTCPTwoTransferForwardWriteBounded
import Netlib.Check.CampusTCPTwoExchangeBound
import Netlib.Check.CampusTCPTwoProgressBounded

/-!
# A static horizon for the transfer exchange

The forward bound includes the transfer and the later write.
The actual reverse task retains the original receiver's RTO and estimator.
-/

namespace Netlib.Check.CampusTCPTwoTransferExchangeBound

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferEvidence (Evidence ReadAdvanced)
open CampusTCPTwoTransferPostRead (After)
open CampusTCPTwoTransferCurrentReverseGeometry (Started)
open CampusTCPTwoTransferForwardWriteBounded (ReadWrite)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut readBefore current : Cut input complete} {sender : Actor} {gateway location : Gateway}
variable {lower upper : List UInt8} {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance bound : Nat} {reverseLower reverseUpper : List UInt8}
variable {readMonitor monitor : CampusTCPTwoTransferMonitor.Monitor} {readActual actual : Step input}
variable {evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper readBefore readMonitor location}
variable {forward : ReadAdvanced evidence readActual} {value : After forward current monitor}

def reverseSlots (initial : TwoWriteInitial cut sender gateway lower upper) (quantum allowance bound : Nat) : Nat :=
  CampusTCPTwoExchangeBound.legSlots initial.receiverState.idle.recovery.rto
    initial.receiverState.idle.recovery.estimator quantum allowance bound

def wholeSlots (initial : TwoWriteInitial cut sender gateway lower upper) (quantum allowance bound : Nat) : Nat :=
  CampusTCPTwoTransferForwardWriteBounded.boundSlots initial quantum allowance bound + reverseSlots initial quantum allowance bound

theorem reverse_eq (start : Started value actual) (spent : Nat) :
    CampusTCPTwoProgressBounded.boundSlots start.reverseInitial quantum (allowance - spent) bound =
      CampusTCPTwoExchangeBound.legSlots initial.receiverState.idle.recovery.rto
        initial.receiverState.idle.recovery.estimator quantum (allowance - spent) bound := by
  change CampusTCPTwoProgressRecoveryBounded.boundSlots start.reverseInitial quantum (allowance - spent) bound = _
  rw [CampusTCPTwoExchangeBound.boundSlots_eq_legSlots, start.reverse_rto, start.reverse_estimator]

theorem reverse_le (start : Started value actual) (spent : Nat) :
    CampusTCPTwoProgressBounded.boundSlots start.reverseInitial quantum (allowance - spent) bound ≤
      reverseSlots initial quantum allowance bound := by
  rw [reverse_eq start spent]
  exact CampusTCPTwoExchangeBound.remaining_legSlots _ _ _ _ _ _

theorem after_write_fits {steps : List (Step input)}
    (rw : ReadWrite initial checks routing quantum allowance reverseLower reverseUpper steps)
    (written : rw.writeSlot < CampusTCPTwoTransferForwardWriteBounded.boundSlots initial quantum allowance bound)
    (spent : Nat) :
    rw.writeSlot + 1 + CampusTCPTwoProgressBounded.boundSlots rw.written.start.reverseInitial quantum (allowance - spent) bound ≤
      wholeSlots initial quantum allowance bound := by
  have reverse := reverse_le (bound := bound) rw.written.start spent
  unfold wholeSlots
  omega

end Netlib.Check.CampusTCPTwoTransferExchangeBound
