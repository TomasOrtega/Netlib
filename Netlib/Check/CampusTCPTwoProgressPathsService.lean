import Netlib.Check.CampusTCPTwoProgressPathsReady
import Netlib.Check.CampusTCPTwoProgressServiceState
import Netlib.Check.CampusTCPTwoProgressNetworkState
import Netlib.Check.CampusTCPTwoProgressSenderWindow

/-!
# Actual data service from current path evidence

The current ledger selects fresh or repeated admission.
The same stored service supplies the next live link and joint state.
-/

namespace Netlib.Check.CampusTCPTwoProgressPathsService

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressSender
open CampusTCPTwoProgressState (Live)
open CampusTCPTwoProgressPaths (DataTicket DataLink)
open CampusTCPTwoProgressPathsReady
open CampusTCPTwoProgressNetwork (ServiceMove)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry}
variable {sent : Stage initial} {timeouts : Nat} {received : CampusTCPTwoProgressReceiver.Stage}
variable {part : Part} {lane : CampusTCPTwoProgressMonitor.Lane} {actual : Step input}

private theorem ticket_actor (path : DataTicket initial native current part lane) :
    path.ticket.value.produced.actor = sender := by rw [path.produced]; exact path.output.actor

private theorem ticket_fields (path : DataTicket initial native current part lane) :
    CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper) path.ticket.value.produced := by
  rw [path.produced]
  exact path.output.fields

private def fresh_ready (live : Live initial current sent timeouts received)
    (path : DataTicket initial native current part lane)
    (data : Admission.DataReady live.gatewayState.gateway.session sender.direction path.ticket.value.source.packet.segment) :
    CampusTCPService.ExistingDataReady (input.contextFor path.ticket.value.gateway)
      (beforeService input current.report.final path.ticket.value.gateway) path.ticket.value.source input.zone path.ticket.value.ingress
      ⟨live.gatewayState.gateway.session.entry.flow, sender.direction⟩ live.gatewayState.gateway.session path.ticket.value.produced.actor.nextHop := by
  rw [path.gateway, path.ingress, ticket_actor path]
  exact live.gatewayState.gateway.existing_ready (native.paths sender)
    (CampusTCPTwoProgressNetwork.service_environment live.anchor) path.ticket.value.source input.zone
    (data_header live.gatewayState (ticket_fields path)) (current_zone initial live.gatewayState sender)
    data (ticket_fields path).ttl

private def repeated_ready (live : Live initial current sent timeouts received)
    (path : DataTicket initial native current part lane)
    (data : Admission.RepeatedReady live.gatewayState.gateway.session sender.direction path.ticket.value.source.packet.segment
      (beforeService input current.report.final gateway).admission.observations) :
    CampusTCPService.ExistingRepeatedReady (input.contextFor path.ticket.value.gateway)
      (beforeService input current.report.final path.ticket.value.gateway) path.ticket.value.source input.zone path.ticket.value.ingress
      ⟨live.gatewayState.gateway.session.entry.flow, sender.direction⟩ live.gatewayState.gateway.session path.ticket.value.produced.actor.nextHop := by
  rw [path.gateway, path.ingress, ticket_actor path]
  exact live.gatewayState.gateway.repeated_ready (native.paths sender)
    (CampusTCPTwoProgressNetwork.service_environment live.anchor) path.ticket.value.source input.zone
    (data_header live.gatewayState (ticket_fields path)) (current_zone initial live.gatewayState sender)
    data (ticket_fields path).ttl

structure DataServed (live : Live initial current sent timeouts received)
    (path : DataTicket initial native current part lane) (actual : Step input) where
  served : Served input
  emission : WireForwarding.Emission served.ticket.value.source.packet
  emitted : served.evidence.output = some emission
  value : ServiceMove initial current path.ticket ⟨live.gatewayState.gateway.session.entry.flow, sender.direction⟩
    live.gatewayState.gateway.session actual served emission emitted
  nextLane : CampusTCPTwoProgressMonitor.Lane
  observed : CampusTCPTwoProgressMonitor.Lane.ofGap
    (CampusTCPGapProgressMonitor.observeService lane.toGap actual true .dataLink) = nextLane
  link : DataLink initial value.move.after part nextLane
  next : Live initial value.move.after sent timeouts received
  reserve : CampusTCPTwoProgressSenderWindow.Reserved initial (endpoint value.move.after.endpoints sender) sent
  covered : (rangeAt next.gatewayState part).isSome = true
  preserved : ∀ role, (rangeAt live.gatewayState role).isSome = true → (rangeAt next.gatewayState role).isSome = true
  linkIndex : link.index = current.report.final.services.length
  linkServed : link.served = served
  linkProduced : link.served.ticket.value.produced = path.output.produced

private theorem finish (live : Live initial current sent timeouts received)
    (space : CampusTCPTwoProgressSenderWindow.Reserved initial (endpoint current.endpoints sender) sent)
    (path : DataTicket initial native current part lane)
    (value : ServiceMove initial current path.ticket ⟨live.gatewayState.gateway.session.entry.flow, sender.direction⟩
      live.gatewayState.gateway.session actual served emission emitted)
    (view : CampusTCPTwoProgressGatewayState.View initial value.move.after)
    (covered : (rangeAt view part).isSome = true)
    (preserved : ∀ role, (rangeAt live.gatewayState role).isSome = true → (rangeAt view role).isSome = true) :
    Nonempty (DataServed live path actual) := by
  have gatewaySpace := CampusTCPTwoProgressGatewayWindow.sender_service_reserved live.gatewayState live.gatewayWindow value view rfl
  let joint := CampusTCPTwoProgressNetworkState.service_live live value view gatewaySpace
  have fields : CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper) served.ticket.value.produced := by
    rw [value.facts.ticket]
    exact ticket_fields path
  have actor : served.ticket.value.produced.actor = sender := by rw [value.facts.ticket]; exact ticket_actor path
  obtain ⟨packetID, custody⟩ := CampusTCPRoundMonitorFacts.service_pending actual served value.facts.recorded emission emitted
  rw [value.move.beforeEq] at custody
  let afterLane : CampusTCPTwoProgressMonitor.Lane :=
    ⟨.dataLink, { lane.refs with dataService := some current.report.final.services.length, dataLinkPacket := some packetID }⟩
  have observed : CampusTCPTwoProgressMonitor.Lane.ofGap
      (CampusTCPGapProgressMonitor.observeService lane.toGap actual true .dataLink) = afterLane := by
    simp only [CampusTCPGapProgressMonitor.observeService, value.facts.recorded, value.move.beforeEq,
      emitted, custody, CampusTCPTwoProgressMonitor.Lane.toGap,
      CampusTCPTwoProgressMonitor.Lane.ofGap, afterLane, ite_true]
  let link : DataLink initial value.move.after part afterLane := {
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
  exact ⟨⟨served, emission, emitted, value, afterLane, observed, link, joint,
    by rw [value.endpoints]; exact space, covered, preserved, rfl, rfl,
    by change served.ticket.value.produced = _; rw [value.facts.ticket, path.produced]⟩⟩

theorem serve_data_at (live : Live initial current sent timeouts received)
    (space : CampusTCPTwoProgressSenderWindow.Reserved initial (endpoint current.endpoints sender) sent)
    (path : DataTicket initial native current part lane) :
    ∃ actual, Nonempty (DataServed live path actual) := by
  have fields := ticket_fields path
  have ready := data_admission live.gatewayState live.gatewayWindow fields
  cases ready with
  | lower missing admitted =>
    obtain ⟨actual, served, emission, emitted, ⟨value⟩⟩ := CampusTCPTwoProgressNetwork.serve_at initial native current live.anchor
      path.ticket path.pending path.gateway ⟨live.gatewayState.gateway.session.entry.flow, sender.direction⟩
      live.gatewayState.gateway.session (fresh_ready live path (.inl admitted))
    have servedReady : Admission.FreshReady live.gatewayState.gateway.session sender.direction served.ticket.value.source.packet.segment := by
      rw [value.facts.ticket]
      exact admitted
    have position : Seq.distance (live.gatewayState.gateway.session.lane sender.direction).base
        served.ticket.value.source.packet.segment.sequence = initial.geometry.«prefix» := by
      rw [value.facts.ticket]
      exact live.gatewayState.lower_position _ (by simpa only [Part.offset, Seq.add_zero, Ticket.source] using fields.sequence)
    obtain ⟨view, upperEq, run, lowerEq, _⟩ := CampusTCPTwoProgressServiceState.lower_service live.gatewayState value rfl servedReady missing position
      (by rw [value.facts.ticket]; exact fields.payload)
    have covered : (rangeAt view .lower).isSome = true := by simp only [rangeAt, lowerEq, Option.isSome_some]
    exact ⟨actual, finish live space path value view covered (by
      intro role before
      cases role
      · exact covered
      · simpa only [rangeAt, upperEq] using before)⟩
  | upper missing admitted =>
    obtain ⟨actual, served, emission, emitted, ⟨value⟩⟩ := CampusTCPTwoProgressNetwork.serve_at initial native current live.anchor
      path.ticket path.pending path.gateway ⟨live.gatewayState.gateway.session.entry.flow, sender.direction⟩
      live.gatewayState.gateway.session (fresh_ready live path (.inl admitted))
    have servedReady : Admission.FreshReady live.gatewayState.gateway.session sender.direction served.ticket.value.source.packet.segment := by
      rw [value.facts.ticket]
      exact admitted
    have position : Seq.distance (live.gatewayState.gateway.session.lane sender.direction).base
        served.ticket.value.source.packet.segment.sequence = initial.geometry.«prefix» + lower.length := by
      rw [value.facts.ticket]
      exact live.gatewayState.upper_position _ fields.sequence
    obtain ⟨view, lowerEq, run, upperEq, _⟩ := CampusTCPTwoProgressServiceState.upper_service live.gatewayState value rfl servedReady missing position
      (by rw [value.facts.ticket]; exact fields.payload)
    have covered : (rangeAt view .upper).isSome = true := by simp only [rangeAt, upperEq, Option.isSome_some]
    exact ⟨actual, finish live space path value view covered (by
      intro role before
      cases role
      · simpa only [rangeAt, lowerEq] using before
      · exact covered)⟩
  | repeated present admitted =>
    obtain ⟨actual, served, emission, emitted, ⟨value⟩⟩ := CampusTCPTwoProgressNetwork.serve_repeated_at initial native current live.anchor
      path.ticket path.pending path.gateway ⟨live.gatewayState.gateway.session.entry.flow, sender.direction⟩
      live.gatewayState.gateway.session (repeated_ready live path admitted)
    have known : Admission.KnownRange (live.gatewayState.gateway.session.lane sender.direction)
        live.gatewayState.gateway.session.entry sender.direction served.ticket.value.source.packet.segment
        (beforeService input current.report.final gateway).admission.observations := by
      rw [value.facts.ticket]
      simpa only [CampusTCPTwoProgressGatewayState.sender_lane, Ticket.source] using admitted.known
    obtain ⟨view, lowerEq, upperEq⟩ := CampusTCPTwoProgressServiceState.repeat_service live.gatewayState value known
    have preserved : ∀ role, (rangeAt live.gatewayState role).isSome = true → (rangeAt view role).isSome = true := by
      intro role before
      cases role
      · simpa only [rangeAt, lowerEq] using before
      · simpa only [rangeAt, upperEq] using before
    exact ⟨actual, finish live space path value view (preserved part present) preserved⟩

end Netlib.Check.CampusTCPTwoProgressPathsService
