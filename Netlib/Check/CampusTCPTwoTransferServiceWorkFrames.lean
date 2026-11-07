import Netlib.Check.CampusTCPTwoTransferLocatedService
import Netlib.Check.CampusTCPTwoProgressPhaseNetworkState

/-!
# Unselected work after the same actual service

Current ticket identities separate the two data ranges and the ACK actor.
The actual service retains all other custody and writer evidence.
-/

namespace Netlib.Check.CampusTCPTwoTransferServiceWorkFrames

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferWork (DataWork OriginalLane)
open CampusTCPTwoTransferPaths (DataTicket AckTicket)
open CampusTCPTwoTransferLocatedService (DataServiced AckServiced DataTarget)

namespace N
export CampusTCPTwoTransferNetwork (Service)
end N
namespace W
export CampusTCPTwoTransferMonitor (Monitor observe)
end W
namespace S
export CampusTCPTwoProgressSender (Part Stage)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
namespace M
export CampusTCPTwoProgressMonitor (Lane)
end M

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {sent : S.Stage initial} {received : R.Stage}
variable {part role : S.Part} {lane otherLane : M.Lane} {target : DataTarget} {actual : Step input}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

private theorem data_ticket_ne (first : DataTicket initial checks current role otherLane)
    (second : DataTicket initial checks current part lane) (different : role ≠ part) : first.ticket.id ≠ second.ticket.id := by
  intro sameID
  obtain ⟨completed, _, selected⟩ := second.completes
  have same := selected.symm.trans
    (completed.item_eq (CampusTCPOrigins.Report.work_valid current.report) first.ticket first.pending sameID)
  have produced := first.toTicketPath.produced.symm.trans
    ((congrArg (fun item => item.value.produced) same.symm).trans second.toTicketPath.produced)
  cases role <;> cases part
  · exact different rfl
  · exact CampusTCPTwoProgressPathsDistinct.produced_ne first.output.fields second.output.fields produced
  · exact CampusTCPTwoProgressPathsDistinct.produced_ne second.output.fields first.output.fields produced.symm
  · exact different rfl

private theorem data_ack_ticket_ne (data : DataTicket initial checks current role otherLane)
    (ack : AckTicket initial checks current count lane) : data.ticket.id ≠ ack.ticket.id := by
  intro sameID
  obtain ⟨completed, _, selected⟩ := ack.completes
  have same := selected.symm.trans
    (completed.item_eq (CampusTCPOrigins.Report.work_valid current.report) data.ticket data.pending sameID)
  have dataActor : data.ticket.value.produced.actor = sender := by rw [data.toTicketPath.produced]; exact data.output.actor
  have ackActor : ack.ticket.value.produced.actor = sender.other := by rw [ack.toTicketPath.produced]; exact ack.output.actor
  have impossible := dataActor.symm.trans ((congrArg (fun item => item.value.produced.actor) same.symm).trans ackActor)
  cases sender <;> cases impossible

private theorem nonconsuming (value : N.Service current item hit session actual served emission emitted) (id : Nat) :
    CampusTCPTwoProgressPathRetain.consumedPacket current.report.final actual.event ≠ some id := by
  simp only [value.facts.event, CampusTCPTwoProgressPathRetain.consumedPacket, ne_eq, reduceCtorEq, not_false_eq_true]

def data_other {path : DataTicket initial checks current part lane} (value : DataServiced core path target actual)
    (work : DataWork initial checks current core.live.gatewayState role otherLane) (different : role ≠ part) :
    DataWork initial checks value.value.value.move.after value.next.live.gatewayState role otherLane := by
  rw [value.gateway]
  cases work with
  | ingress path source =>
    exact .ingress (path.after_move value.value.value.move (nonconsuming value.value.value _))
      ((CampusTCPTwoTransferSources.Frame.service value.value.value).selected source)
  | ticket other selected source =>
    exact .ticket (other.after_service value.value.value (data_ticket_ne other path different)) selected
      ((CampusTCPTwoTransferSources.Frame.service value.value.value).selected source)
  | link path source covered =>
    exact .link (path.after_move value.value.value.move (nonconsuming value.value.value _))
      ((CampusTCPTwoTransferSources.Frame.service value.value.value).selected source) (value.value.preserved role covered)

def original_other {path : DataTicket initial checks current part lane} (value : DataServiced core path target actual)
    (work : OriginalLane initial checks current core.live.gatewayState received role otherLane) (different : role ≠ part) :
    OriginalLane initial checks value.value.value.move.after value.next.live.gatewayState received role otherLane := by
  cases work with
  | active work missing => exact .active (data_other value work different) missing
  | done phase => exact .done phase

def data_ack {path : AckTicket initial checks current (received.bytes lower upper).length lane}
    (value : AckServiced core path actual) (work : DataWork initial checks current core.live.gatewayState role otherLane) :
    DataWork initial checks value.value.value.move.after value.next.live.gatewayState role otherLane := by
  rw [value.gateway]
  cases work with
  | ingress path source =>
    exact .ingress (path.after_move value.value.value.move (nonconsuming value.value.value _))
      ((CampusTCPTwoTransferSources.Frame.service value.value.value).selected source)
  | ticket data selected source =>
    exact .ticket (data.after_service value.value.value (data_ack_ticket_ne data path)) selected
      ((CampusTCPTwoTransferSources.Frame.service value.value.value).selected source)
  | link path source covered =>
    have nextCovered : (CampusTCPTwoTransferAdmission.rangeAt value.value.next role).isSome = true := by
      cases role
      · simpa only [CampusTCPTwoTransferAdmission.rangeAt, value.value.lowerRun] using covered
      · simpa only [CampusTCPTwoTransferAdmission.rangeAt, value.value.upperRun] using covered
    exact .link (path.after_move value.value.value.move (nonconsuming value.value.value _))
      ((CampusTCPTwoTransferSources.Frame.service value.value.value).selected source) nextCovered

def original_ack {path : AckTicket initial checks current (received.bytes lower upper).length lane}
    (value : AckServiced core path actual)
    (work : OriginalLane initial checks current core.live.gatewayState received role otherLane) :
    OriginalLane initial checks value.value.value.move.after value.next.live.gatewayState received role otherLane := by
  cases work with
  | active work missing => exact .active (data_ack value work) missing
  | done phase => exact .done phase

theorem phase_service (phase : CampusTCPTwoTransferControlState.Phase current.report.final monitor.mode location)
    (ordinary : monitor.mode = .armed ∨ monitor.mode = .finished)
    (value : N.Service current item hit session actual served emission emitted) (located : item.value.gateway = location) :
    CampusTCPTwoTransferControlState.Phase value.move.after.report.final monitor.mode location := by
  generalize equation : monitor.mode = mode at phase ordinary ⊢
  cases phase with
  | armed fields => exact .armed (fields.primary_service value located)
  | finished fields =>
    have fixed := value.environment
    have paused := congrArg CampusTCPRoundEnvironment.Environment.assignmentPaused fixed
    have sealed := congrArg CampusTCPRoundEnvironment.Environment.primarySealed fixed
    have fenced := congrArg CampusTCPRoundEnvironment.Environment.primaryFenced fixed
    have owners := congrArg CampusTCPRoundEnvironment.Environment.owners fixed
    have installed := congrArg CampusTCPRoundEnvironment.Environment.installed fixed
    change current.report.final.owners = value.move.after.report.final.owners at owners
    exact .finished ⟨paused.symm.trans fields.unpaused, sealed.symm.trans fields.sealed,
      fenced.symm.trans fields.fenced, by rw [← owners]; exact fields.client,
      by rw [← owners]; exact fields.server, installed.symm.trans fields.installed⟩
  | capture | install | clientRoute | serverRoute | fence | resume =>
    rcases ordinary with impossible | impossible <;> cases impossible

end Netlib.Check.CampusTCPTwoTransferServiceWorkFrames
