import Netlib.Check.CampusTCPTwoTransferDrainProgress
import Netlib.Check.CampusTCPTwoTransferControlProgress

/-!
# Actual capture after the selected primary drain

The same service empties the primary queue and enables a fresh capture.
The capture retains the original task and all pending packet work.
-/

namespace Netlib.Check.CampusTCPTwoTransferDrainProgress

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : CampusTCPTwoTransferMonitor.Monitor} {actual : Step input}
variable {sent : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor .primary sent received}

private theorem Advanced.capture_selected (value : Advanced core ticket actual)
    (drain : CampusTCPTwoTransferMonitor.drainTicket current.report.final monitor = some ticket) :
    CampusTCPTwoTransferMonitor.controlDemand
      (CampusTCPTwoTransferMonitor.observe (config initial checks routing quantum allowance reverseLower reverseUpper) monitor actual) =
        some .capture := by
  have nextMode : (CampusTCPTwoTransferMonitor.observe
      (config initial checks routing quantum allowance reverseLower reverseUpper) monitor actual).mode = .capture := by
    rw [value.value.observed]
    exact CampusTCPTwoTransferDrainObserve.drain_mode drain
  simp only [CampusTCPTwoTransferMonitor.controlDemand, nextMode]

theorem Advanced.capture_at (value : Advanced core ticket actual)
    (scope : CampusTCPTwoTransferScope.TransferScope monitor)
    (drain : CampusTCPTwoTransferMonitor.drainTicket current.report.final monitor = some ticket) :
    ∃ captured, Nonempty (CampusTCPTwoTransferControlProgress.ActiveAdvanced value.active .capture captured) := by
  exact value.active.control_at value.phase (value.capture_selected drain)
    (CampusTCPTwoTransferControlObserve.noDrain_of_primary_zero _ _ (value.primary_empty scope drain))

theorem Advanced.capture_step (value : Advanced core ticket actual)
    (scope : CampusTCPTwoTransferScope.TransferScope monitor)
    (drain : CampusTCPTwoTransferMonitor.drainTicket current.report.final monitor = some ticket)
    (captured : Step input) (before : captured.before = value.value.value.value.move.after.report.final)
    (event : captured.event = CampusTCPTwoTransferMonitor.Control.capture.event
      (config initial checks routing quantum allowance reverseLower reverseUpper)) :
    Nonempty (CampusTCPTwoTransferControlProgress.ActiveAdvanced value.active .capture captured) := by
  exact value.active.control_step value.phase (value.capture_selected drain)
    (CampusTCPTwoTransferControlObserve.noDrain_of_primary_zero _ _ (value.primary_empty scope drain)) captured before event

end Netlib.Check.CampusTCPTwoTransferDrainProgress
