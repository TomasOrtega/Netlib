import Netlib.Check.CampusTCPTwoTransferEvidenceEvents
import Netlib.Check.CampusTCPTwoTransferEvidenceHandoff
import Netlib.Check.CampusTCPTwoTransferEvidenceSend
import Netlib.Check.CampusTCPTwoTransferEvidenceAssign
import Netlib.Check.CampusTCPTwoTransferEvidenceService
import Netlib.Check.CampusTCPTwoTransferEvidenceDataReceive
import Netlib.Check.CampusTCPTwoTransferEvidenceAckReceive
import Netlib.Check.CampusTCPTwoTransferEvidenceAckOutput
import Netlib.Check.CampusTCPTwoTransferEvidenceRead
import Netlib.Check.CampusTCPTwoTransferEvidenceTimeout
import Netlib.Check.CampusTCPTwoTransferEvidenceDrop

namespace Netlib.Check.CampusTCPTwoTransferEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {actual : Step input}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

private theorem no_drain (state : State input) (monitor : W.Monitor) (ordinary : W.controlDemand monitor = none) :
    W.drainTicket state monitor = none := by
  cases selected : W.drainTicket state monitor with
  | none => rfl
  | some ticket =>
    have mode := CampusTCPTwoTransferControlBound.drain_mode selected
    simp only [W.controlDemand, mode] at ordinary
    cases ordinary

variable (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)

theorem Evidence.step (budget : allowance ≤ 2) (actual : Step input) (before : actual.before = current.report.final)
    (allowed : W.Allowed cfg current.report.final monitor actual.event) :
    Nonempty (Advanced evidence actual) ∨ Nonempty (ReadAdvanced evidence actual) := by
  cases control : W.controlDemand monitor with
  | some kind => exact Or.inl (evidence.control_region_step control actual before allowed)
  | none =>
    have drainless := no_drain current.report.final monitor control
    cases CampusTCPTwoTransferEvidenceEvents.classify evidence drainless control allowed with
    | send count event => exact Or.inl (evidence.send_step actual before event allowed)
    | assign index ingress event => exact Or.inl (evidence.assign_step actual before event allowed)
    | serve ticket event => exact Or.inl (evidence.service_step actual before event allowed drainless)
    | deliver index bytes event =>
      cases pending : monitor.exchange.forward.ack with
      | none => exact Or.inl (evidence.data_receive_step actual before event allowed pending)
      | some lane => exact Or.inl (evidence.ack_receive_step pending actual before event allowed)
    | ack event => exact Or.inl (evidence.ack_output_step actual before event allowed)
    | read mode event => exact Or.inr (evidence.read_step mode actual before event)
    | clock actor millis event => exact Or.inl (evidence.clock_step actual before event allowed)
    | timeout event => exact Or.inl (evidence.timeout_step budget actual before event allowed)
    | drop id event => exact Or.inl (evidence.drop_step actual before event allowed)

end Netlib.Check.CampusTCPTwoTransferEvidence
