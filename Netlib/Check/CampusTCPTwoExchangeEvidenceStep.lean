import Netlib.Check.CampusTCPTwoExchangeEvidenceForward
import Netlib.Check.CampusTCPTwoExchangeEvidenceWrite
import Netlib.Check.CampusTCPTwoExchangeEvidenceReverse

/-!
# Preservation under every allowed exchange step

The current selector chooses the active local proof or the actual write.
Each transition extends the same report with the supplied stored step.
-/

namespace Netlib.Check.CampusTCPTwoExchangeEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {reverseLower reverseUpper : List UInt8} {monitor : M.Monitor}

theorem Evidence.step (evidence : Evidence initial native quantum allowance reverseLower reverseUpper current monitor)
    (budget : allowance ≤ 2)
    (endpointReserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (gatewayReserve : CampusTCPTwoReverseGeometry.Initial initial reverseLower reverseUpper)
    (lowerNonempty : reverseLower ≠ []) (upperNonempty : reverseUpper ≠ [])
    (actual : Step input) (before : actual.before = current.report.final)
    (allowed : CampusTCPTwoExchangeMonitor.Allowed
      (CampusTCPTwoExchangeSetup.config initial native quantum allowance reverseLower reverseUpper)
      current.report.final monitor actual.event) :
    ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance reverseLower reverseUpper move.after
      (CampusTCPTwoExchangeMonitor.observe
        (CampusTCPTwoExchangeSetup.config initial native quantum allowance reverseLower reverseUpper) monitor actual)) := by
  cases evidence with
  | forward value mode _ => exact forward_step value mode budget actual before allowed
  | needWrite value mode =>
    exact needWrite_step value mode budget endpointReserve gatewayReserve lowerNonempty upperNonempty actual before allowed
  | reverse forward start value mode _ => exact reverse_step forward start value mode budget actual before allowed
  | done forward start value mode => exact done_step forward start value mode budget actual before allowed

end Netlib.Check.CampusTCPTwoExchangeEvidence
