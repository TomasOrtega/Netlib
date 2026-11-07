import Netlib.Check.CampusTCPTwoTransferState
import Netlib.Check.CampusTCPTwoProgressSenderWindow
import Netlib.Check.CampusTCPTwoProgressWire
import Netlib.Check.CampusTCPPartialAck
import Netlib.Check.CampusTCPZeroAck

/-!
# Actual ACK receipt at the current gateway location

Retirement and zero-count receipt use the selected stored emission.
The sender window reserve remains separate from the joint state.
-/

namespace Netlib.Check.CampusTCPTwoTransferLocatedAckReceive

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPGapProgressPhaseBase (Move)
open CampusTCPTwoProgressStart CampusTCPTwoProgressWire
open CampusTCPTwoTransferState (LiveAt)

namespace S
export CampusTCPTwoProgressSender (Stage Flight Retires source)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage Facts)
end R
namespace W
export CampusTCPTwoProgressSenderWindow (Reserved)
end W
namespace D
export CampusTCPDeliveryEnabled (ApplicationSource LinkPending)
end D

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {sent next : S.Stage initial} {timeouts amount : Nat} {received : R.Stage}
variable {index : Nat} {served : Served input}
variable {emission : WireForwarding.Emission served.ticket.value.source.packet}
variable {emitted : served.evidence.output = some emission}

private theorem emission_fields (live : LiveAt initial current location sent timeouts received)
    (fields : AckFields initial count served.ticket.value.produced)
    (target : emission.target = initial.gatewayState.session.entry.flow.output sender.other.direction) :
    emission.asInput.packet.header = (endpoint current.endpoints sender).core.inbound ∧
      EstablishedReceive.control emission.asInput.packet.segment = none ∧
      Flags.ack emission.asInput.packet.segment.flags = true ∧
      emission.asInput.packet.segment.sequence = (endpoint current.endpoints sender).core.receiveNext ∧
      emission.asInput.packet.segment.payload = [] ∧
      emission.asInput.packet.segment.acknowledgment = (endpoint cut.endpoints sender).core.sendNext.add count ∧
      lower.length + upper.length ≤ count + emission.asInput.packet.segment.window.val := by
  have twice : sender.other.other = sender := by cases sender <;> rfl
  have controls := CampusTCPRoundEmission.profile_controls
    (CampusTCPRoundEmission.emission_profile emission fields.profile)
  refine ⟨?_, controls.1, controls.2, ?_, emission.payload.trans fields.payload,
    emission.control.2.1.trans fields.acknowledgment, ?_⟩
  · change emission.decoded.header = _
    rw [emission.header, target, initial.output_tuple sender.other, twice, live.senderFlight.inbound]
    rfl
  · exact emission.control.1.trans (fields.sequence.trans
      ((receiver_sequence initial).trans live.senderFlight.receiveNext.symm))
  · change lower.length + upper.length ≤ count + emission.decoded.segment.window.val
    rw [emission.control.2.2.2.2.1]
    exact fields.window

private theorem retirement_coordinate (retiring : S.Retires sent amount next) :
    next.retiredBytes = sent.retiredBytes + amount := by
  cases retiring <;> simp only [CampusTCPTwoProgressSender.Stage.retiredBytes, Nat.zero_add]

private theorem old_sent_space (space : W.Reserved initial state sent)
    (retiring : S.Retires sent amount next) : next.sent.length ≤ state.sendWindow := by
  cases retiring
  · change lower.length + upper.length ≤ 0 + state.sendWindow at space
    change upper.length ≤ state.sendWindow
    omega
  · exact Nat.zero_le _
  · exact Nat.zero_le _

private theorem incoming_sent_space (retiring : S.Retires sent amount next)
    (space : lower.length + upper.length ≤ next.retiredBytes + window) : next.sent.length ≤ window := by
  cases retiring
  · change lower.length + upper.length ≤ lower.length + window at space
    change upper.length ≤ window
    omega
  · exact Nat.zero_le _
  · exact Nat.zero_le _

private theorem incoming_current_head (flight : S.Flight initial state sent timeouts)
    (recovering : sent.preparing = false)
    (space : lower.length + upper.length ≤ sent.retiredBytes + window)
    (head : Recovery.Outstanding) (present : sent.ledger.head? = some head) : head.count ≤ window := by
  cases sent with
  | written => cases recovering
  | lower first => cases recovering
  | both first second current =>
    have same : current = head := Option.some.inj present
    subst head
    have size := congrArg Recovery.Outstanding.count flight.headFixed
    change current.count = lower.length at size
    change lower.length + upper.length ≤ 0 + window at space
    omega
  | tail first second current =>
    have same : current = head := Option.some.inj present
    subst head
    have size := congrArg Recovery.Outstanding.count flight.headFixed
    change current.count = upper.length at size
    change lower.length + upper.length ≤ lower.length + window at space
    omega
  | retired first second => cases present

private def after_delivery (live : LiveAt initial current location sent timeouts received)
    (delivery : CampusTCPRoundDelivery.Delivery current.report complete current.endpoints index served emission emitted)
    (move : Move current delivery.step) (updated : move.after.endpoints = delivery.updated)
    (actor : served.ticket.value.produced.actor.other = sender)
    (flight : S.Flight initial delivery.after next timeouts) : LiveAt initial move.after location next timeouts received := by
  have selected : endpoint move.after.endpoints sender = delivery.after := by
    rw [updated]
    simpa only [actor] using delivery.selected
  have peer : endpoint move.after.endpoints sender.other = endpoint current.endpoints sender.other := by
    rw [updated]
    simpa only [actor] using delivery.peer
  let nextFlight : S.Flight initial (endpoint move.after.endpoints sender) next timeouts := selected.symm ▸ flight
  let receiver : R.Facts initial (endpoint move.after.endpoints sender.other) received := peer.symm ▸ live.receiverFacts
  have gatewayFrame (selected) : beforeService input move.after.report.final selected = beforeService input current.report.final selected := by
    rw [move.final, CampusTCPRoundLocal.step_service_nonservice delivery.step (by rw [delivery.event]; trivial), delivery.beforeEq]
  have operations : applicationSteps move.after.endpoints sender.other = applicationSteps current.endpoints sender.other := by
    rw [updated]
    simpa only [actor] using delivery.peerSteps
  exact ⟨⟨⟨live.anchor.retained.trans move.retained,
    fun selected => (live.anchor.policy selected).trans
      (congrArg CampusTCPService.Before.environment (gatewayFrame selected)).symm⟩,
    CampusTCPTwoProgressState.endpoint_guards nextFlight receiver⟩,
    nextFlight, receiver, live.gatewayState.reframe (gatewayFrame location),
    live.gatewayWindow, live.history.same operations⟩

structure Advanced (live : LiveAt initial current location sent timeouts received) (next : S.Stage initial) (amount : Nat)
    (index : Nat) (served : Served input) (emission : WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission) where
  delivery : CampusTCPPartialAck.PartialAckDelivered current.report complete current.endpoints index served emission emitted
    live.senderFlight.recovery live.senderFlight.reaction
  actor : served.ticket.value.produced.actor = sender.other
  retiring : S.Retires sent amount next
  protocol : Endpoint.AdvancingAck (endpoint current.endpoints sender) emission.asInput live.senderFlight.recovery delivery.after
  counted : Endpoint.inOrderCount (endpoint current.endpoints sender) emission.asInput = amount
  joint : LiveAt initial delivery.move.after location next timeouts received
  space : W.Reserved initial (endpoint delivery.move.after.endpoints sender) next

structure Zero (live : LiveAt initial current location sent timeouts received)
    (index : Nat) (served : Served input) (emission : WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission) where
  delivery : CampusTCPZeroAck.ZeroAckDelivered current.report complete current.endpoints index served emission emitted
    live.senderFlight.recovery live.senderFlight.reaction
  actor : served.ticket.value.produced.actor = sender.other
  protocol : Endpoint.ZeroAck (endpoint current.endpoints sender) emission.asInput live.senderFlight.recovery delivery.after
  joint : LiveAt initial delivery.move.after location sent timeouts received
  space : W.Reserved initial (endpoint delivery.move.after.endpoints sender) sent

theorem advancing_at (live : LiveAt initial current location sent timeouts received)
    (space : W.Reserved initial (endpoint current.endpoints sender) sent)
    (retiring : S.Retires sent amount next)
    (found : current.report.final.services[index]? = some served)
    (actor : served.ticket.value.produced.actor = sender.other)
    (application : D.ApplicationSource served.ticket.value.produced) (pending : D.LinkPending current.report.final index)
    (fields : AckFields initial next.retiredBytes served.ticket.value.produced)
    (target : emission.target = initial.gatewayState.session.entry.flow.output sender.other.direction) :
    Nonempty (Advanced live next amount index served emission emitted) := by
  obtain ⟨tuple, controls, ack, sequence, empty, acknowledgment, incoming⟩ := emission_fields live fields target
  have other : served.ticket.value.produced.actor.other = sender := by rw [actor]; cases sender <;> rfl
  have advancing : emission.asInput.packet.segment.acknowledgment =
      (endpoint current.endpoints sender).core.sendUna.add amount := by
    rw [acknowledgment, live.senderFlight.sendUna, S.source, initial.senderState.idle.cursor,
      Seq.add_add, retirement_coordinate retiring]
  have conditions := live.senderFlight.ack_conditions retiring tuple controls ack sequence empty advancing
  have selectedConditions : Endpoint.AdvancingAckConditions
      (endpoint current.endpoints served.ticket.value.produced.actor.other) emission.asInput
      live.senderFlight.recovery live.senderFlight.reaction := by simpa only [other] using conditions
  obtain ⟨delivery⟩ := CampusTCPPartialAck.Report.deliver_partial_ack current.report complete current.endpoints
    current.connection index served found emission emitted application pending live.senderFlight.recovery
    live.senderFlight.reaction selectedConditions
  have protocol : Endpoint.AdvancingAck (endpoint current.endpoints sender) emission.asInput live.senderFlight.recovery delivery.after := by
    simpa only [other] using delivery.protocol
  have counted := live.senderFlight.ack_counted retiring advancing
  let flight := live.senderFlight.ack_received retiring protocol counted
    (old_sent_space space retiring) (incoming_sent_space retiring incoming)
  have selected : endpoint delivery.move.after.endpoints sender = delivery.after := by
    change endpoint delivery.updated sender = delivery.after
    simpa only [other] using delivery.selected
  refine ⟨⟨delivery, actor, retiring, protocol, counted,
    after_delivery live delivery.toDelivery delivery.move rfl other flight, ?_⟩⟩
  rw [selected]
  exact CampusTCPTwoProgressSenderWindow.advancing_ack space retiring protocol incoming

theorem zero_at (live : LiveAt initial current location sent timeouts received)
    (space : W.Reserved initial (endpoint current.endpoints sender) sent)
    (recovering : sent.preparing = false)
    (found : current.report.final.services[index]? = some served)
    (actor : served.ticket.value.produced.actor = sender.other)
    (application : D.ApplicationSource served.ticket.value.produced) (pending : D.LinkPending current.report.final index)
    (fields : AckFields initial sent.retiredBytes served.ticket.value.produced)
    (target : emission.target = initial.gatewayState.session.entry.flow.output sender.other.direction)
    (credit : Endpoint.qualifyingDuplicate (endpoint current.endpoints sender) emission.asInput.packet.segment 0 = true →
      live.senderFlight.recovery.duplicateAcks < 2) :
    Nonempty (Zero live index served emission emitted) := by
  obtain ⟨tuple, controls, ack, sequence, empty, acknowledgment, incoming⟩ := emission_fields live fields target
  have other : served.ticket.value.produced.actor.other = sender := by rw [actor]; cases sender <;> rfl
  have equal : emission.asInput.packet.segment.acknowledgment = (endpoint current.endpoints sender).core.sendUna := by
    rw [acknowledgment, live.senderFlight.sendUna, S.source, initial.senderState.idle.cursor]
  have conditions : Endpoint.ZeroAckConditions (endpoint current.endpoints sender) emission.asInput
      live.senderFlight.recovery live.senderFlight.reaction :=
    ⟨live.senderFlight.valid, live.senderFlight.coherent, live.senderFlight.prepared, live.senderFlight.storage,
      live.senderFlight.runtime, live.senderFlight.ackRuntime, tuple, controls, ack, sequence, empty, equal, credit⟩
  have selectedConditions : Endpoint.ZeroAckConditions
      (endpoint current.endpoints served.ticket.value.produced.actor.other) emission.asInput
      live.senderFlight.recovery live.senderFlight.reaction := by simpa only [other] using conditions
  obtain ⟨delivery⟩ := CampusTCPZeroAck.Report.deliver_zero_ack current.report complete current.endpoints
    current.connection index served found emission emitted application pending live.senderFlight.recovery
    live.senderFlight.reaction selectedConditions
  have protocol : Endpoint.ZeroAck (endpoint current.endpoints sender) emission.asInput live.senderFlight.recovery delivery.after := by
    simpa only [other] using delivery.protocol
  let flight := live.senderFlight.zero_ack_received protocol recovering
    (incoming_current_head live.senderFlight recovering incoming)
  have selected : endpoint delivery.move.after.endpoints sender = delivery.after := by
    change endpoint delivery.updated sender = delivery.after
    simpa only [other] using delivery.selected
  refine ⟨⟨delivery, actor, protocol, after_delivery live delivery.toDelivery delivery.move rfl other flight, ?_⟩⟩
  rw [selected]
  exact CampusTCPTwoProgressSenderWindow.zero_ack space protocol incoming

theorem Step.advancing (actual : Step input) (live : LiveAt initial current location sent timeouts received)
    (space : W.Reserved initial (endpoint current.endpoints sender) sent) (retiring : S.Retires sent amount next)
    (before : actual.before = current.report.final) (event : actual.event = .deliver index emission.bytes true)
    (found : current.report.final.services[index]? = some served)
    (actor : served.ticket.value.produced.actor = sender.other)
    (application : D.ApplicationSource served.ticket.value.produced) (pending : D.LinkPending current.report.final index)
    (fields : AckFields initial next.retiredBytes served.ticket.value.produced)
    (target : emission.target = initial.gatewayState.session.entry.flow.output sender.other.direction) :
    ∃ value : Advanced live next amount index served emission emitted, value.delivery.step = actual := by
  obtain ⟨value⟩ := advancing_at (emitted := emitted) live space retiring found actor application pending fields target
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event value.delivery.step actual
    (value.delivery.beforeEq.trans before.symm) (value.delivery.event.trans event.symm)
  exact ⟨value, same⟩

theorem Step.zero (actual : Step input) (live : LiveAt initial current location sent timeouts received)
    (space : W.Reserved initial (endpoint current.endpoints sender) sent) (recovering : sent.preparing = false)
    (before : actual.before = current.report.final) (event : actual.event = .deliver index emission.bytes true)
    (found : current.report.final.services[index]? = some served)
    (actor : served.ticket.value.produced.actor = sender.other)
    (application : D.ApplicationSource served.ticket.value.produced) (pending : D.LinkPending current.report.final index)
    (fields : AckFields initial sent.retiredBytes served.ticket.value.produced)
    (target : emission.target = initial.gatewayState.session.entry.flow.output sender.other.direction)
    (credit : Endpoint.qualifyingDuplicate (endpoint current.endpoints sender) emission.asInput.packet.segment 0 = true →
      live.senderFlight.recovery.duplicateAcks < 2) :
    ∃ value : Zero live index served emission emitted, value.delivery.step = actual := by
  obtain ⟨value⟩ := zero_at (emitted := emitted) live space recovering found actor application pending fields target credit
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event value.delivery.step actual
    (value.delivery.beforeEq.trans before.symm) (value.delivery.event.trans event.symm)
  exact ⟨value, same⟩

end Netlib.Check.CampusTCPTwoTransferLocatedAckReceive
