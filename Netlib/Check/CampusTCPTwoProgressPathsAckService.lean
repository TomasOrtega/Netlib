import Netlib.Check.CampusTCPTwoProgressPathsReady
import Netlib.Check.CampusTCPTwoProgressServiceState
import Netlib.Check.CampusTCPTwoProgressNetworkState
import Netlib.Check.CampusTCPTwoProgressSenderWindow

/-!
# Actual ACK service from the current path

Current coverage bounds establish admission for the stored ACK.
Its actual processing supplies the next link and gateway count.
-/

namespace Netlib.Check.CampusTCPTwoProgressPathsAckService

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressSender
open CampusTCPTwoProgressState (Live)
open CampusTCPTwoProgressPaths (AckTicket AckLink)
open CampusTCPTwoProgressPathsReady
open CampusTCPTwoProgressNetwork (ServiceMove)
open CampusTCPTwoProgressServiceState (processingAt processingAt_admission processingAt_attachment)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry}
variable {sent : Stage initial} {timeouts : Nat} {received : CampusTCPTwoProgressReceiver.Stage}
variable {lane : CampusTCPTwoProgressMonitor.Lane} {actual : Step input} {count : Nat}

private theorem ticket_actor (path : AckTicket initial native current count lane) :
    path.ticket.value.produced.actor = sender.other := by rw [path.produced]; exact path.output.actor

private theorem ticket_fields (path : AckTicket initial native current count lane) :
    CampusTCPTwoProgressWire.AckFields initial count path.ticket.value.produced := by
  rw [path.produced]
  exact path.output.fields

private def ack_ready (live : Live initial current sent timeouts received)
    (path : AckTicket initial native current count lane)
    (within : initial.geometry.«prefix» + count ≤ (live.gatewayState.gateway.session.lane sender.direction).observed)
    (oldAck : (live.gatewayState.gateway.session.lane sender.direction).acknowledged ≤ initial.geometry.«prefix» + count) :
    CampusTCPService.ExistingDataReady (input.contextFor path.ticket.value.gateway)
      (beforeService input current.report.final path.ticket.value.gateway) path.ticket.value.source input.zone path.ticket.value.ingress
      ⟨live.gatewayState.gateway.session.entry.flow, sender.other.direction⟩ live.gatewayState.gateway.session
      path.ticket.value.produced.actor.nextHop := by
  rw [path.gateway, path.ingress, ticket_actor path]
  exact live.gatewayState.gateway.existing_ready (native.paths sender.other)
    (CampusTCPTwoProgressNetwork.service_environment live.anchor) path.ticket.value.source input.zone
    (ack_header live.gatewayState (ticket_fields path)) (current_zone initial live.gatewayState sender.other)
    (.inr ((ticket_fields path).admission_ready live.gatewayState within (by omega))) (ticket_fields path).ttl

private theorem ack_offset (fields : CampusTCPTwoProgressWire.AckFields initial count produced)
    (view : CampusTCPTwoProgressGatewayState.View initial current)
    (within : initial.geometry.«prefix» + count ≤ (view.gateway.session.lane sender.direction).observed) :
    Admission.ackOffset (view.gateway.session.lane sender.direction) produced.source.packet.segment =
      initial.geometry.«prefix» + count := by
  have peerLane : view.gateway.session.peer sender.other.direction = view.gateway.session.lane sender.direction := by
    cases sender <;> rfl
  have offset := CampusTCPTwoProgressGateway.ack_offset_add view.gateway.session sender.other.direction
    produced.source.packet.segment (initial.geometry.«prefix» + count) (by simpa only [peerLane] using within)
    (by rw [peerLane, view.gateway.identity.base, fields.acknowledgment, initial.geometry.senderCursor, Seq.add_add])
  simpa only [peerLane] using offset

private theorem acknowledged_after (live : Live initial current sent timeouts received)
    (path : AckTicket initial native current count lane)
    (value : ServiceMove initial current path.ticket ⟨live.gatewayState.gateway.session.entry.flow, sender.other.direction⟩
      live.gatewayState.gateway.session actual served emission emitted)
    (view : CampusTCPTwoProgressGatewayState.View initial value.move.after)
    (within : initial.geometry.«prefix» + count ≤ (live.gatewayState.gateway.session.lane sender.direction).observed)
    (oldAck : (live.gatewayState.gateway.session.lane sender.direction).acknowledged ≤ initial.geometry.«prefix» + count) :
    (view.gateway.session.lane sender.direction).acknowledged = initial.geometry.«prefix» + count := by
  obtain ⟨processing, present, _, _, attached, _⟩ := value.facts.processing
  have previous : served.before = beforeService input current.report.final gateway := by
    rw [value.facts.current, value.selected]
  let selected := processingAt processing previous
  have direction : selected.prepared.attachment.direction = sender.other.direction := by
    rw [processingAt_attachment]
    exact attached
  have peerLane : ∀ session : Admission.Session,
      session.peer selected.prepared.attachment.direction = session.lane sender.direction := by
    intro session
    rw [direction]
    cases sender <;> rfl
  have phase : selected.admitted.state.phase = .data view.gateway.session := by
    have phase := view.gateway.phase
    rw [value.after_before processing present] at phase
    change processing.nextAdmission.phase = .data view.gateway.session at phase
    rw [← processingAt_admission processing previous,
      CampusTCPRoundAdmission.Processing.committed_data selected live.gatewayState.gateway.session live.gatewayState.gateway.phase] at phase
    exact phase
  have fields := CampusTCPTwoProgressGatewayWindow.result_window_fields selected.admitted live.gatewayState.gateway.phase phase
  have nextLane : view.gateway.session.lane sender.direction =
      Admission.acknowledgedLane (live.gatewayState.gateway.session.lane sender.direction) served.ticket.value.source.packet.segment := by
    simpa only [peerLane, WireForwarding.Source.asInput] using fields.2.2
  rw [nextLane, Admission.acknowledgedLane_count]
  have offset : Admission.ackOffset (live.gatewayState.gateway.session.lane sender.direction)
      served.ticket.value.source.packet.segment = initial.geometry.«prefix» + count := by
    rw [value.facts.ticket]
    exact ack_offset (ticket_fields path) live.gatewayState within
  rw [offset, Nat.max_eq_right oldAck]

structure AckServed (live : Live initial current sent timeouts received)
    (path : AckTicket initial native current (received.bytes lower upper).length lane) (actual : Step input) where
  served : Served input
  emission : WireForwarding.Emission served.ticket.value.source.packet
  emitted : served.evidence.output = some emission
  value : ServiceMove initial current path.ticket ⟨live.gatewayState.gateway.session.entry.flow, sender.other.direction⟩
    live.gatewayState.gateway.session actual served emission emitted
  nextLane : CampusTCPTwoProgressMonitor.Lane
  observed : CampusTCPTwoProgressMonitor.Lane.ofGap
    (CampusTCPGapProgressMonitor.observeService lane.toGap actual false .ackLink) = nextLane
  link : AckLink initial value.move.after (received.bytes lower upper).length nextLane
  next : Live initial value.move.after sent timeouts received
  reserve : CampusTCPTwoProgressSenderWindow.Reserved initial (endpoint value.move.after.endpoints sender) sent
  acknowledged : (next.gatewayState.gateway.session.lane sender.direction).acknowledged =
    initial.geometry.«prefix» + (received.bytes lower upper).length
  lowerRun : next.gatewayState.ranges.lowerRun = live.gatewayState.ranges.lowerRun
  upperRun : next.gatewayState.ranges.upperRun = live.gatewayState.ranges.upperRun
  linkIndex : link.index = current.report.final.services.length
  linkServed : link.served = served
  linkProduced : link.served.ticket.value.produced = path.output.produced

theorem serve_ack_at (live : Live initial current sent timeouts received)
    (space : CampusTCPTwoProgressSenderWindow.Reserved initial (endpoint current.endpoints sender) sent)
    (path : AckTicket initial native current (received.bytes lower upper).length lane)
    (within : initial.geometry.«prefix» + (received.bytes lower upper).length ≤
      (live.gatewayState.gateway.session.lane sender.direction).observed)
    (oldAck : (live.gatewayState.gateway.session.lane sender.direction).acknowledged ≤
      initial.geometry.«prefix» + (received.bytes lower upper).length) :
    ∃ actual, Nonempty (AckServed live path actual) := by
  obtain ⟨actual, served, emission, emitted, ⟨value⟩⟩ := CampusTCPTwoProgressNetwork.serve_at initial native current live.anchor
    path.ticket path.pending path.gateway ⟨live.gatewayState.gateway.session.entry.flow, sender.other.direction⟩
    live.gatewayState.gateway.session (ack_ready live path within oldAck)
  obtain ⟨view, lowerRun, upperRun⟩ := CampusTCPTwoProgressServiceState.empty_service live.gatewayState value
    (by rw [value.facts.ticket]; exact (ticket_fields path).payload)
  have gatewaySpace := CampusTCPTwoProgressGatewayWindow.receiver_service_reserved live.gatewayState live.gatewayWindow value view rfl
    (by rw [value.facts.ticket]; exact (ticket_fields path).window_reserve live.gatewayState within)
  let joint := CampusTCPTwoProgressNetworkState.service_live live value view gatewaySpace
  have fields : CampusTCPTwoProgressWire.AckFields initial (received.bytes lower upper).length served.ticket.value.produced := by
    rw [value.facts.ticket]
    exact ticket_fields path
  have actor : served.ticket.value.produced.actor = sender.other := by rw [value.facts.ticket]; exact ticket_actor path
  obtain ⟨packetID, custody⟩ := CampusTCPRoundMonitorFacts.service_pending actual served value.facts.recorded emission emitted
  rw [value.move.beforeEq] at custody
  let afterLane : CampusTCPTwoProgressMonitor.Lane :=
    ⟨.ackLink, { lane.refs with ackService := some current.report.final.services.length, ackLinkPacket := some packetID }⟩
  have observed : CampusTCPTwoProgressMonitor.Lane.ofGap
      (CampusTCPGapProgressMonitor.observeService lane.toGap actual false .ackLink) = afterLane := by
    simp only [CampusTCPGapProgressMonitor.observeService, value.facts.recorded, value.move.beforeEq,
      emitted, custody, CampusTCPTwoProgressMonitor.Lane.toGap,
      CampusTCPTwoProgressMonitor.Lane.ofGap, afterLane, Bool.false_eq_true, ite_false]
  let link : AckLink initial value.move.after (received.bytes lower upper).length afterLane := {
    index := current.report.final.services.length
    served, stored := by rw [value.move.final]; exact value.facts.serviceIndex
    emission, emitted, actor, application := by rw [value.facts.ticket, path.produced]; exact path.output.application
    fields
    target := by
      change emission.target = _
      rw [← live.gatewayState.gateway.identity.entry]
      exact value.facts.target
    packetID, custody := by rw [value.move.final]; exact custody
    phase := rfl, serviceRef := rfl, packetRef := rfl }
  exact ⟨actual, ⟨⟨served, emission, emitted, value, afterLane, observed, link, joint,
    by rw [value.endpoints]; exact space,
    acknowledged_after live path value view within oldAck, lowerRun, upperRun, rfl, rfl,
    by change served.ticket.value.produced = _; rw [value.facts.ticket, path.produced]⟩⟩⟩

end Netlib.Check.CampusTCPTwoProgressPathsAckService
