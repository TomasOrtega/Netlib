import Netlib.Check.CampusTCPTwoTransferRecoveryBounded
import Netlib.Check.CampusTCPTwoTransferCurrentReverseBounded

/-!
# The forward read and later reverse write on one trace

The whole service condition covers recovery and clocks before the write.
The result retains both actual operations and their report positions.
-/

namespace Netlib.Check.CampusTCPTwoTransferForwardWriteBounded

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)
open CampusTCPTwoTransferEvidenceTrace (ReadAt)
open CampusTCPTwoTransferCurrentReverseBounded (WriteAt)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {steps : List (Step input)} {events remaining : List Event} {final : State input} {bound : Nat}

structure ReadWrite (initial : TwoWriteInitial cut sender gateway lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (routing : Routing cut gateway)
    (quantum allowance : Nat) (reverseLower reverseUpper : List UInt8) (steps : List (Step input)) where
  readSlot : Nat
  read : ReadAt initial checks routing quantum allowance reverseLower reverseUpper steps readSlot
  writeSlot : Nat
  written : WriteAt read.advance steps writeSlot
  ordered : readSlot < writeSlot

def boundSlots (initial : TwoWriteInitial cut sender gateway lower upper) (quantum allowance bound : Nat) : Nat :=
  CampusTCPTwoTransferRecoveryBounded.boundSlots initial quantum allowance bound + bound

theorem start_by
    (initial : TwoWriteInitial cut sender .primary lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (routing : Routing cut .primary)
    (quantum allowance : Nat) (reverseLower reverseUpper : List UInt8)
    (primaryEmpty : cut.report.final.outstanding .primary = 0)
    (targetEmpty : cut.report.final.standby.transport = Checkpoint.Gateway.initial)
    (targetNS : cut.report.final.standby.guard.source.ns = (input.deployment .standby).executionNS)
    (endpointReserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (gatewayReserve : CampusTCPTwoReverseGeometry.Initial initial reverseLower reverseUpper)
    (lowerNonempty : reverseLower ≠ []) (upperNonempty : reverseUpper ≠ [])
    (budget : allowance ≤ 2) (positive : 0 < quantum)
    (trace : Trace input cut.report.final events steps final remaining)
    (actions : CampusTCPTwoTransferMonitor.actions (config initial checks routing quantum allowance reverseLower reverseUpper)
      cut.report.final .initial steps = true)
    (service : CampusTCPTwoTransferMonitor.check (config initial checks routing quantum allowance reverseLower reverseUpper)
      cut.report.final .initial steps bound = true)
    (enough : boundSlots initial quantum allowance bound ≤ steps.length) :
    ∃ value : ReadWrite initial checks routing quantum allowance reverseLower reverseUpper steps,
      value.writeSlot < boundSlots initial quantum allowance bound := by
  have forwardWithin : CampusTCPTwoTransferRecoveryBounded.boundSlots initial quantum allowance bound ≤ steps.length := by
    unfold boundSlots at enough
    omega
  obtain ⟨readSlot, readWithin, ⟨read⟩⟩ := CampusTCPTwoTransferRecoveryBounded.forward_read_by initial checks routing
    quantum allowance reverseLower reverseUpper primaryEmpty targetEmpty targetNS budget positive trace actions service forwardWithin
  have room : readSlot + 1 + bound ≤ steps.length := by
    unfold boundSlots at enough
    omega
  obtain ⟨writeSlot, afterRead, before, ⟨written⟩⟩ := CampusTCPTwoTransferCurrentReverseBounded.write_by
    endpointReserve gatewayReserve lowerNonempty upperNonempty trace
    ((CampusTCPTwoTransferMonitor.actions_correct _ _ _ _).mp actions)
    (CampusTCPTwoTransferCurrentReverseBounded.At.of_read read)
    ((CampusTCPTwoTransferMonitor.check_correct _ _ _ _ _).mp service) room
  refine ⟨⟨readSlot, read, writeSlot, written, by omega⟩, ?_⟩
  change writeSlot < boundSlots initial quantum allowance bound
  unfold boundSlots
  omega

end Netlib.Check.CampusTCPTwoTransferForwardWriteBounded
