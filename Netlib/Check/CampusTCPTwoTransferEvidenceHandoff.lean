import Netlib.Check.CampusTCPTwoTransferEvidenceControl
import Netlib.Check.CampusTCPTwoTransferEvidenceDrain
import Netlib.Check.CampusTCPTwoTransferEvidenceFacts
import Netlib.Check.CampusTCPTwoTransferControlBound

/-!
# Current evidence throughout the selected transfer controls

An allowed step in this region is a control, a selected primary drain, or a
clock. Each branch constructs evidence for that same supplied step.
-/

namespace Netlib.Check.CampusTCPTwoTransferEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)
open CampusTCPTwoTransferScope (TransferScope)

namespace B
export CampusTCPTwoTransferControlBound (potential rank potential_active control_valid serves_control_event drain_serves_event)
end B

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {actual : Step input} {kind : W.Control}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

variable (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)

theorem Evidence.control_region_step (selected : W.controlDemand monitor = some kind)
    (actual : Step input) (before : actual.before = current.report.final)
    (allowed : W.Allowed cfg current.report.final monitor actual.event) : Nonempty (Advanced evidence actual) := by
  cases event : actual.event
  all_goals first
    | exact evidence.clock_step actual before event allowed
    | (
      cases drain : W.drainTicket current.report.final monitor with
      | some ticket =>
        have served : CampusTCPTwoTransferMonitor.drainServes ticket actual.event = true := by
          simpa [W.Allowed, CampusTCPTwoTransferMonitor.allowed, evidence.healthy, drain, event] using allowed
        exact evidence.drain_step drain actual before (B.drain_serves_event.mp served)
      | none =>
        have served : kind.serves cfg actual.event = true := by
          simpa [W.Allowed, CampusTCPTwoTransferMonitor.allowed, evidence.healthy, drain, selected, event] using allowed
        exact evidence.control_step selected drain actual before ((B.serves_control_event actual.event).mp served))

include evidence in
theorem Evidence.control_scope (selected : W.controlDemand monitor = some kind) : TransferScope monitor := by
  by_cases armed : monitor.mode = .armed
  · have due : CampusTCPTwoTransferMonitor.transferDue monitor.exchange = true := by
      simp only [W.controlDemand, armed] at selected
      split at selected
      · assumption
      · cases selected
    exact TransferScope.of_due due
  · exact evidence.scope armed (B.control_valid selected).1

include evidence in
theorem Evidence.control_primary_le_one (selected : W.controlDemand monitor = some kind) :
    current.report.final.outstanding .primary ≤ 1 :=
  evidence.core.primaryQueue.resolved_count_le_one (CampusTCPOrigins.Report.work_valid current.report)
    (evidence.control_scope selected).resolved

include evidence in
theorem Evidence.control_potential_le_eight (selected : W.controlDemand monitor = some kind) :
    B.potential current.report.final monitor ≤ 8 := by
  have pending := evidence.control_primary_le_one selected
  have remaining : B.rank kind ≤ 7 := by cases kind <;> decide
  rw [B.potential_active current.report.final selected]
  omega

end Netlib.Check.CampusTCPTwoTransferEvidence
