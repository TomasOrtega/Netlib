import Netlib.Check.CampusTCPTwoTransferExchangeResult
import Netlib.Check.CampusTCPTwoTransferControlEvents
import Netlib.Check.CampusTCPTwoReverseEndpoints

/-!
# Endpoint, writer and control facts for the completed exchange

Both byte streams retain their selected actual writers and service permissions.
The actual control slots belong to the same report, and both endpoints are idle.
-/

namespace Netlib.Check.CampusTCPTwoTransferExchangeResult

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance bound : Nat} {reverseLower reverseUpper : List UInt8} {steps : List (Step input)}

variable (result : Result initial checks routing quantum allowance reverseLower reverseUpper bound steps)

theorem Result.recorded_suffix : result.reverse.point.value.recorded.suffix = steps.take result.slot :=
  List.append_cancel_left (result.reverse.point.value.recorded.history.symm.trans result.history)

theorem Result.control_slots : (result.monitor.controls.map (·.2)).Pairwise (· < ·) :=
  CampusTCPTwoTransferControlEvents.recorded_ordered result.reverse.point.value.recorded result.reverse.point.healthy

theorem Result.control_event {control : CampusTCPTwoTransferMonitor.Control} {slot : Nat}
    (member : (control, slot) ∈ result.monitor.controls) :
    ∃ actual, steps[slot]? = some actual ∧ actual.event = control.event (config initial checks routing quantum allowance reverseLower reverseUpper) := by
  obtain ⟨actual, found, event⟩ := CampusTCPTwoTransferControlEvents.recorded_event
    result.reverse.point.value.recorded result.reverse.point.healthy member
  have bound := CampusTCPTwoTransferControlEvents.recorded_bound
    result.reverse.point.value.recorded result.reverse.point.healthy member
  rw [result.recorded_suffix, List.length_take] at bound
  rw [result.recorded_suffix, List.getElem?_take_of_lt (by omega : slot < result.slot)] at found
  exact ⟨actual, found, event⟩

theorem Result.forward_permissions (prior : cut.report.compliant = true) (index : Nat) (byte : UInt8)
    (selected : (lower ++ upper)[index]? = some byte) :
    ∃ origin : CampusTCPTwoTransferLocatedRead.ReadByte result.readWrite.read.advance.value index byte,
      origin.writer.origin.writer = initial.write.writer ∧
        CampusTCPRoundOrigins.ServicePermissions origin.origin.delivery.service.joint.step
          origin.origin.delivery.receive.receipt.served := by
  obtain ⟨origin, permission⟩ := CampusTCPTwoTransferEvidence.ReadAdvanced.permissions
    result.readWrite.read.point.evidence result.readWrite.read.advance prior index byte selected
  exact ⟨origin, origin.writer.writer, permission⟩

theorem Result.reverse_permissions (prior : cut.report.compliant = true) (index : Nat) (byte : UInt8)
    (selected : (reverseLower ++ reverseUpper)[index]? = some byte) :
    ∃ origin : CampusTCPTwoProgressReadSuffix.SuffixReadOrigin result.reverse.value.completed index byte,
      Nonempty (CampusTCPTwoProgressWriteOrigins.SelectedWriteOrigin result.readWrite.written.start.reverseInitial
        origin.attempt origin.read.origin.localIndex byte) ∧
        CampusTCPRoundOrigins.ServicePermissions origin.delivery.service.joint.step origin.delivery.receive.receipt.served :=
  CampusTCPTwoTransferReverseResult.Result.read_permissions result.reverse prior index byte selected

theorem Result.reverse_writer {stored : List ApplicationTrace.Step} {attempt : CampusTCPModel.T.OutputAt stored}
    {index : Nat} {byte : UInt8}
    (writer : CampusTCPTwoProgressWriteOrigins.SelectedWriteOrigin result.readWrite.written.start.reverseInitial attempt index byte) :
    writer.origin.writer = result.readWrite.written.start.boundary.write.operation :=
  writer.writer.trans result.readWrite.written.start.writer

theorem Result.forward_write_member : ∃ actual ∈ result.current.report.steps,
    actual.result.application = some (sender, initial.write.writer) := by
  obtain ⟨actual, member, operation⟩ := initial.write.joint
  refine ⟨actual, ?_, operation⟩
  rw [result.history]
  exact List.mem_append_left _ member

theorem Result.reverse_write_recorded : result.readWrite.written.actual.result.application =
    some (sender.other, result.readWrite.written.start.reverseInitial.write.writer) := by
  rw [result.readWrite.written.start.writer]
  exact result.readWrite.written.start.boundary.write.recorded

structure EndpointIdle (state : Endpoint.State) where
  idle : IdleEndpoint state
  pending : state.pending = []
  unread : state.core.received = []
  held : state.receiveStore.held = []

theorem Result.endpoints_idle (actor : Actor) : Nonempty (EndpointIdle (endpoint result.current.endpoints actor)) := by
  let done := result.reverse.value.completed
  by_cases selected : actor = sender.other
  · subst actor
    have unread : (endpoint result.readWrite.written.start.boundary.write.move.after.endpoints sender.other).core.received = [] := by
      rw [result.readWrite.written.start.boundary.write.selected]
      exact result.readWrite.written.point.value.receiver.empty
    exact ⟨{
      idle := CampusTCPTwoReverseEndpoints.sender_idle done result.reverse.value.senderDuplicate
      pending := CampusTCPTwoReverseEndpoints.sender_pending done
      unread := CampusTCPTwoReverseEndpoints.sender_unread done unread
      held := CampusTCPTwoReverseEndpoints.sender_held done }⟩
  · have same : actor = sender := by cases actor <;> cases sender <;> first | rfl | exact False.elim (selected rfl)
    subst actor
    have other : sender.other.other = sender := by cases sender <;> rfl
    have receiver : Nonempty (EndpointIdle (endpoint result.current.endpoints sender.other.other)) := ⟨{
      idle := CampusTCPTwoReverseEndpoints.receiver_idle done
      pending := CampusTCPTwoReverseEndpoints.closed_pending done.receiver
      unread := done.receiver.empty
      held := done.receiver.held }⟩
    simpa only [other] using receiver

end Netlib.Check.CampusTCPTwoTransferExchangeResult
