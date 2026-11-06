import Netlib.Check.CampusTCPRoundGateway
import Netlib.Check.CampusTCPRoundLocal
import Netlib.Check.CampusTCPRoundEndpointGeometry
import Netlib.Check.CampusTCPGatewayEnabled
import Netlib.Check.CampusTCPRoundClock
import Netlib.Check.CampusTCPRoundStart
import Netlib.Check.CampusTCPRoundAssignment
import Netlib.Check.CampusTCPRoundService
import Netlib.Check.CampusTCPRoundEmission
import Netlib.Check.CampusTCPRoundDelivery
import Netlib.Check.CampusTCPRoundAck

/-!
# Connected steps in a campus TCP round

Each cut retains the actual report and its endpoint histories.
Packet assignment and gateway service preserve these endpoints.
-/

namespace Netlib.Check.CampusTCPRound

open CampusTCPModel CampusTCPEnabled

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {events : List Event} {report : Report input events} {bytes : List UInt8}
open Protocol.TCP

structure Cut (input : Input) (complete : H.Completed input.active input.passive) where
  events : List Event
  report : Report input events
  supported : report.supported = true
  finished : report.remaining = []
  endpoints : Applications complete
  connection : report.final.connection = .application complete endpoints

def Cut.ofPrepared (start : CampusTCPRoundSetup.PreparedStart report complete bytes) : Cut input complete :=
  ⟨_, start.next.report, start.next.supported, start.next.finished, start.next.endpoints, start.next.connection⟩

abbrev NetworkEvent := CampusTCPRoundClock.NetworkAction


def Cut.appendNetwork (cut : Cut input complete) (actual : Step input)
    (before : actual.before = cut.report.final) (supported : actual.result.supported = true)
    (network : NetworkEvent actual.event) : Cut input complete where
  events := cut.events ++ [actual.event]
  report := CampusTCPSchedule.Report.appendStep cut.report cut.supported cut.finished actual before supported
  supported := CampusTCPSchedule.Report.appendStep_supported _ _ _ _ _ _
  finished := rfl
  endpoints := cut.endpoints
  connection := (CampusTCPRoundClock.Step.connection_frame actual network).trans (before ▸ cut.connection)

structure LocalAppend (cut : Cut input complete) (actual : Step input) (actor : Actor) (localStep : T.Step) where
  next : Cut input complete
  history : next.report.steps = cut.report.steps ++ [actual]
  final : next.report.final = actual.result.state
  selected : endpoint next.endpoints actor = localStep.result.state
  peer : endpoint next.endpoints actor.other = endpoint cut.endpoints actor.other
  localBefore : localStep.before = endpoint cut.endpoints actor

theorem Cut.appendLocal (cut : Cut input complete) (actual : Step input)
    (before : actual.before = cut.report.final) (supported : actual.result.supported = true)
    (actor : Actor) (event : T.Event) (action : LocalAction actor actual.event event)
    (localStep : T.Step) (recorded : actual.result.application = some (actor, localStep)) :
    Nonempty (LocalAppend cut actual actor localStep) := by
  have connection : actual.before.connection = .application complete cut.endpoints := before ▸ cut.connection
  obtain ⟨after, connected, selected, peer, _, _, source, _, _⟩ :=
    CampusTCPEnabled.Step.application_frame actual complete cut.endpoints connection actor event action localStep recorded
  let report := CampusTCPSchedule.Report.appendStep cut.report cut.supported cut.finished actual before supported
  let next : Cut input complete := ⟨_, report,
    CampusTCPSchedule.Report.appendStep_supported _ _ _ _ _ _, rfl, after, connected⟩
  exact ⟨⟨next, rfl, rfl, selected, peer, source⟩⟩

structure Sent (start : CampusTCPRoundSetup.PreparedStart report complete bytes) where
  cut : Cut input complete
  actual : Step input
  before : actual.before = start.next.report.final
  event : actual.event = .send .client bytes.length true
  supported : actual.result.supported = true
  history : cut.report.steps = start.next.report.steps ++ [actual]
  final : cut.report.final = actual.result.state
  localStep : T.Step
  application : actual.result.application = some (.client, localStep)
  produced : Produced input.active input.passive
  output : actual.result.output = some produced
  packet : EstablishedReceive.Input
  origin : T.OutputOrigin localStep packet
  production : produced = .application .client localStep packet origin
  payload : packet.packet.segment.payload = bytes
  encoded : ∃ payload, Endpoint.emit localStep.before payload = .ok packet
  localBefore : localStep.before = endpoint start.next.endpoints .client
  sender : endpoint cut.endpoints .client = Endpoint.sendState (endpoint start.next.endpoints .client) bytes.length
  receiver : endpoint cut.endpoints .server = endpoint start.next.endpoints .server
  source : cut.report.final.outputs[start.next.report.final.outputs.length]? = some produced
  pending : IngressPending cut.report.final start.next.report.final.outputs.length
  gateway : beforeService input cut.report.final .primary = beforeService input start.next.report.final .primary
  environment : CampusTCPRoundEnvironment.environment start.next.report.final =
    CampusTCPRoundEnvironment.environment cut.report.final

theorem send (start : CampusTCPRoundSetup.PreparedStart report complete bytes)
    (nonempty : bytes ≠ [])
    (mss : bytes.length ≤ Handshake.effectiveMSS input.active (Handshake.receiveOffer input.passive))
    (window : bytes.length ≤ input.passive.capacity) : Nonempty (Sent start) := by
  let cut := Cut.ofPrepared start
  let state := endpoint start.next.endpoints .client
  have ready := start.send_ready nonempty mss window
  have prepared := start.client_ack
  have earlier := (CampusTCPChronology.Report.application_before start.next.report complete
    start.next.endpoints start.next.connection).1
  obtain ⟨effect, produced, computed, supported, output, _, payload, application⟩ :=
    send_enabled start.next.report.final complete start.next.endpoints start.next.connection .client
      bytes.length earlier ready prepared
  let actual : Step input := ⟨_, _, effect, computed⟩
  let localStep := ApplicationTrace.Step.make state (endpoint_valid start.next.endpoints .client)
    (.send bytes.length true) start.next.report.final.time
  have app : actual.result.application = some (.client, localStep) := application
  have emitted : actual.result.output = some produced := output
  obtain ⟨next⟩ := cut.appendLocal actual rfl supported .client (.send bytes.length true)
    (.send bytes.length true) localStep app
  obtain ⟨packet, origin, production⟩ := CampusTCPRoundLocal.step_application_output actual complete
    start.next.endpoints start.next.connection .client (.send bytes.length true)
    (.send bytes.length true) localStep app produced emitted
  have packetPayload : packet.packet.segment.payload = bytes := by
    have actualPayload := payload
    rw [production] at actualPayload
    simp only [Produced.output, start.client, Endpoint.writeState, CampusTCPRoundSetup.preparedSeed,
      CampusTCPRoundSetup.ackState, CampusTCPRoundSetup.recoveryState, complete.certificate.empty.1,
      List.nil_append, List.take_length] at actualPayload
    exact actualPayload
  have original : ApplicationTrace.NoRetry localStep := by
    intro policy event
    cases event
  obtain ⟨wire, sent⟩ := Endpoint.send_success_enabled state bytes.length (endpoint_valid start.next.endpoints .client) ready prepared
  have selected : localStep.result.state = Endpoint.sendState state bytes.length := by
    change (Endpoint.send state bytes.length true).state = _
    rw [sent]
  have source : next.next.report.final.outputs[start.next.report.final.outputs.length]? = some produced := by
    rw [next.final, CampusTCPOrigins.output_history actual, emitted]
    change (start.next.report.final.outputs ++ [produced])[start.next.report.final.outputs.length]? = some produced
    simp
  obtain ⟨packetItem, member, _, minted⟩ := CampusTCPCustodyFacts.Step.output_packet actual produced emitted
  have live : IngressPending next.next.report.final start.next.report.final.outputs.length := by
    rw [next.final]
    refine ⟨packetItem, member, ?_⟩
    simp only [minted, Transit.ingressAt]
    exact beq_self_eq_true _
  refine ⟨⟨next.next, actual, rfl, rfl, supported, next.history, next.final, localStep, app, produced,
    emitted, packet, origin, production, packetPayload, CampusTCPRoundLocal.original_encoded origin original,
    next.localBefore, next.selected.trans selected, next.peer, source, live, ?_, ?_⟩⟩
  · rw [next.final]
    exact CampusTCPRoundLocal.step_service_nonservice actual trivial .primary
  · rw [next.final]
    exact CampusTCPRoundEnvironment.Step.environment actual trivial

theorem Sent.packet_fields {start : CampusTCPRoundSetup.PreparedStart report complete bytes} (sent : Sent start) :
    sent.produced.source.packet.header = Output.reverse complete.certificate.activeSeed.core.inbound ∧
      sent.produced.source.packet.segment.sequence = input.active.iss.add 1 ∧
      sent.produced.source.packet.segment.acknowledgment = input.passive.iss.add 1 ∧
      sent.produced.source.packet.segment.payload = bytes ∧
      Admission.DataProfile sent.produced.source.packet.segment ∧
      1 < sent.produced.source.packet.ip.packet.ttl.toNat := by
  obtain ⟨payload, encoded⟩ := sent.encoded
  have transport := Endpoint.emit_transport _ _ _ encoded
  have profile := CampusTCPRoundLocal.emit_profile _ _ _ encoded
  rw [sent.localBefore, start.client] at transport
  have fields := complete.certificate.initial_sequences
  have header : sent.packet.packet.header = Output.reverse complete.certificate.activeSeed.core.inbound := transport.1
  have sequence : sent.packet.packet.segment.sequence = input.active.iss.add 1 := by
    simpa only [Endpoint.writeState, CampusTCPRoundSetup.preparedSeed, CampusTCPRoundSetup.ackState,
      CampusTCPRoundSetup.recoveryState, fields.2.1, complete.activeConfig] using transport.2.1
  have acknowledgment : sent.packet.packet.segment.acknowledgment = input.passive.iss.add 1 := by
    simpa only [Endpoint.writeState, CampusTCPRoundSetup.preparedSeed, CampusTCPRoundSetup.ackState,
      CampusTCPRoundSetup.recoveryState, fields.2.2.1, complete.passiveConfig] using transport.2.2.1
  simpa only [sent.production, Produced.source, Produced.output, WireForwarding.Source.ofInput] using
    And.intro header ⟨sequence, acknowledgment, sent.payload, profile.1, profile.2.2.2⟩

variable {request : CampusTCPRoundStart.Request input}

def Sent.ready_at (initial : CampusTCPRoundStart.Initial report complete request)
    (native : CampusTCPRoundStart.NativeEnv initial) (sent : Sent initial.start) (current : State input)
    (same : beforeService input current .primary = initial.beforeService) :
    CampusTCPService.ExistingDataReady (input.contextFor .primary) (beforeService input current .primary)
      sent.produced.source input.zone native.dataIngress ⟨initial.entry.flow, .original⟩ initial.session "server" := by
  obtain ⟨header, sequence, acknowledgment, payload, profile, ttl⟩ := sent.packet_fields
  apply CampusTCPRoundGateway.original_ready input complete initial.aligned native.original
    (beforeService input current .primary) (congrArg CampusTCPService.Before.environment same.symm)
    sent.produced.source header
  · rw [same]
    exact initial.valid
  · rw [same]
    exact initial.records
  · rw [same]
    exact initial.phase
  · exact sequence
  · exact acknowledgment
  · exact profile
  · rw [payload]
    exact request.nonempty
  · rw [payload]
    exact request.peer_mss complete
  · rw [payload]
    exact request.receiveFits
  · rw [payload]
    exact request.epoch complete
  · exact ttl

structure Assigned (initial : CampusTCPRoundStart.Initial report complete request)
    (native : CampusTCPRoundStart.NativeEnv initial) (sent : Sent initial.start) where
  actual : Step input
  facts : CampusTCPRoundAssignment.AssignmentFacts sent.cut.report.final
    initial.state.outputs.length native.dataIngress sent.produced actual

variable {initial : CampusTCPRoundStart.Initial report complete request}
variable {native : CampusTCPRoundStart.NativeEnv initial} {sent : Sent initial.start}

def Assigned.cut (assigned : Assigned initial native sent) : Cut input complete :=
  sent.cut.appendNetwork assigned.actual assigned.facts.beforeEq assigned.facts.supported
    (assigned.facts.event ▸ CampusTCPRoundClock.NetworkAction.assign _ _)

def Assigned.ticket (_assigned : Assigned initial native sent) :=
  CampusTCPRoundAssignment.ticket sent.cut.report.final initial.state.outputs.length native.dataIngress sent.produced

theorem assign (initial : CampusTCPRoundStart.Initial report complete request)
    (native : CampusTCPRoundStart.NativeEnv initial) (sent : Sent initial.start) :
    Nonempty (Assigned initial native sent) := by
  obtain ⟨actual, facts⟩ := CampusTCPRoundAssignment.Report.assign_enabled sent.cut.report
    initial.state.outputs.length native.dataIngress sent.produced sent.source
    (native.route_at sent.cut.report.final sent.environment sent.produced.actor) sent.pending
  exact ⟨⟨actual, facts⟩⟩

theorem Assigned.gateway (assigned : Assigned initial native sent) :
    beforeService input assigned.cut.report.final .primary = initial.beforeService := by
  change beforeService input assigned.actual.result.state .primary = _
  have nonservice : CampusTCPRoundEnvironment.Nonservice assigned.actual.event := by rw [assigned.facts.event]; trivial
  rw [CampusTCPRoundLocal.step_service_nonservice assigned.actual nonservice, assigned.facts.beforeEq]
  exact sent.gateway

theorem Assigned.environment (assigned : Assigned initial native sent) :
    CampusTCPRoundEnvironment.environment initial.state =
      CampusTCPRoundEnvironment.environment assigned.cut.report.final := by
  have transport : CampusTCPRoundEnvironment.TransportOnly assigned.actual.event := by rw [assigned.facts.event]; trivial
  have fixed := CampusTCPRoundEnvironment.Step.environment assigned.actual transport
  rw [assigned.facts.beforeEq] at fixed
  exact sent.environment.trans fixed

theorem Assigned.primary (assigned : Assigned initial native sent) : assigned.ticket.value.gateway = .primary :=
  native.owner_at sent.cut.report.final sent.environment sent.produced.actor

theorem Assigned.pending (assigned : Assigned initial native sent) :
    assigned.ticket ∈ assigned.cut.report.final.work.pending := assigned.facts.pending

def Assigned.ready (assigned : Assigned initial native sent) :
    CampusTCPService.ExistingDataReady (input.contextFor assigned.ticket.value.gateway)
      (beforeService input assigned.cut.report.final assigned.ticket.value.gateway)
      assigned.ticket.value.source input.zone assigned.ticket.value.ingress
      ⟨initial.entry.flow, .original⟩ initial.session assigned.ticket.value.produced.actor.nextHop := by
  have who : assigned.ticket.value.produced.actor = .client := by
    change sent.produced.actor = .client
    rw [sent.production]
    rfl
  rw [assigned.primary, who]
  exact sent.ready_at initial native assigned.cut.report.final assigned.gateway

structure DataServed (assigned : Assigned initial native sent) where
  actual : Step input
  served : Served input
  emission : WireForwarding.Emission served.ticket.value.source.packet
  emitted : served.evidence.output = some emission
  facts : CampusTCPRoundService.ServiceFacts assigned.cut.report.final assigned.ticket
    ⟨initial.entry.flow, .original⟩ initial.session actual served emission emitted

variable {assigned : Assigned initial native sent}

def DataServed.cut (served : DataServed assigned) : Cut input complete :=
  assigned.cut.appendNetwork served.actual served.facts.beforeEq served.facts.supported
    (served.facts.event ▸ CampusTCPRoundClock.NetworkAction.serve _ _)

theorem serve_data (assigned : Assigned initial native sent) : Nonempty (DataServed assigned) := by
  have phase : CampusTCPGatewayEnabled.ServicePhaseReady assigned.cut.report.final assigned.ticket.value.gateway := by
    rw [assigned.primary]
    exact native.service_phase_at assigned.cut.report.final assigned.environment
  obtain ⟨actual, service, emission, emitted, facts⟩ := CampusTCPRoundService.Report.serve_enabled
    assigned.cut.report assigned.ticket assigned.pending phase ⟨initial.entry.flow, .original⟩ initial.session assigned.ready
  exact ⟨⟨actual, service, emission, emitted, facts⟩⟩

theorem DataServed.source_fields (service : DataServed assigned) :
    service.served.ticket.value.source.packet.segment.sequence = input.active.iss.add 1 ∧
      service.served.ticket.value.source.packet.segment.acknowledgment = input.passive.iss.add 1 ∧
      service.served.ticket.value.source.packet.segment.payload = request.bytes ∧
      Admission.DataProfile service.served.ticket.value.source.packet.segment := by
  rw [service.facts.ticket]
  exact ⟨sent.packet_fields.2.1, sent.packet_fields.2.2.1, sent.packet_fields.2.2.2.1,
    sent.packet_fields.2.2.2.2.1⟩

theorem DataServed.ready (service : DataServed assigned) :
    ∃ recovery reaction, CampusTCPDeliveryEnabled.InOrderReady
      (endpoint service.cut.endpoints .server) service.emission.asInput recovery reaction := by
  obtain ⟨sequence, acknowledgment, payload, profile⟩ := service.source_fields
  obtain ⟨recovery, reaction, ready⟩ := CampusTCPRoundEmission.data_ready initial service.emission
    service.facts.target sequence acknowledgment payload profile
  refine ⟨recovery, reaction, ?_⟩
  change CampusTCPDeliveryEnabled.InOrderReady (endpoint sent.cut.endpoints .server) _ _ _
  rw [sent.receiver]
  exact ready

theorem DataServed.pending (service : DataServed assigned) :
    CampusTCPDeliveryEnabled.LinkPending service.cut.report.final assigned.cut.report.final.services.length := by
  obtain ⟨packet, member, _, source, _⟩ := service.facts.link
  refine ⟨packet, member, ?_⟩
  simp only [source, Transit.linkAt, beq_self_eq_true]

theorem DataServed.application (service : DataServed assigned) :
    CampusTCPDeliveryEnabled.ApplicationSource service.served.ticket.value.produced := by
  rw [service.facts.ticket]
  change CampusTCPDeliveryEnabled.ApplicationSource sent.produced
  rw [sent.production]
  trivial

theorem DataServed.actor (service : DataServed assigned) : service.served.ticket.value.produced.actor = .client := by
  rw [service.facts.ticket]
  change sent.produced.actor = .client
  rw [sent.production]
  rfl

theorem DataServed.emitted_payload (service : DataServed assigned) :
    service.emission.asInput.packet.segment.payload = request.bytes := by
  change service.emission.decoded.segment.payload = request.bytes
  rw [service.emission.payload]
  exact service.source_fields.2.2.1

theorem DataServed.before_eq (service : DataServed assigned) : service.served.before = initial.beforeService := by
  rw [service.facts.current, assigned.primary]
  exact assigned.gateway

theorem DataServed.environment (service : DataServed assigned) :
    CampusTCPRoundEnvironment.environment initial.state = CampusTCPRoundEnvironment.environment service.cut.report.final :=
  assigned.environment.trans service.facts.environment

theorem DataServed.geometry (service : DataServed assigned) :
    ∃ after : Admission.Session,
      (beforeService input service.cut.report.final .primary).admission.phase = .data after ∧
      CampusTCPRoundAdmission.DataGeometry initial.session after service.served.ticket.value.source.packet.segment
        service.served.before.admission.observations.length := by
  obtain ⟨processing, present, _, _, direction, _⟩ := service.facts.processing
  have phase : service.served.before.admission.phase = .data initial.session := by
    rw [service.before_eq]
    exact initial.phase
  obtain ⟨sequence, acknowledgment, payload, profile⟩ := service.source_fields
  obtain ⟨after, committed, geometry⟩ := CampusTCPRoundAdmission.Processing.original_empty_geometry processing
    initial.session phase direction initial.aligned.originalCoverage initial.aligned.originalAcknowledged
    initial.aligned.replyCoverage initial.aligned.replyAcknowledged
    (sequence.trans initial.aligned.originalBase.symm) (acknowledgment.trans initial.aligned.replyBase.symm)
    profile (by rw [payload]; exact request.nonempty)
    (by rw [payload, initial.aligned.serverMSS]; exact request.peer_mss complete)
    (by rw [payload, initial.aligned.originalWindow]; exact request.receiveFits)
    (by rw [payload]; exact request.epoch complete)
  have stored := service.facts.admission processing present
  rw [assigned.primary] at stored
  change service.actual.result.state.primary.transport.admission = processing.nextAdmission at stored
  refine ⟨after, ?_, geometry⟩
  change service.actual.result.state.primary.transport.admission.phase = .data after
  rw [stored]
  exact committed

theorem DataServed.tracker (service : DataServed assigned) :
    (beforeService input service.cut.report.final .primary).tracker.Valid ∧
      (beforeService input service.cut.report.final .primary).tracker.records = [⟨initial.entry, true⟩] := by
  obtain ⟨processing, present, _, _, _, _⟩ := service.facts.processing
  have phase : service.served.before.admission.phase = .data initial.session := by
    rw [service.before_eq]
    exact initial.phase
  have records : service.served.before.tracker.records = [⟨initial.entry, true⟩] := by
    rw [service.before_eq]
    exact initial.records
  have preserved := CampusTCPRoundGateway.Evidence.singleton_data_records service.served.evidence processing present
    initial.session phase records
  have transport := service.facts.transport
  rw [assigned.primary] at transport
  change service.actual.result.state.primary.transport =
    ⟨service.served.evidence.tracker, service.served.evidence.admission⟩ at transport
  change service.actual.result.state.primary.transport.tracker.Valid ∧
    service.actual.result.state.primary.transport.tracker.records = [⟨initial.entry, true⟩]
  rw [transport]
  exact preserved

structure Released (service : DataServed assigned) where
  delivery : CampusTCPRoundDelivery.DataDelivered service.cut.report complete service.cut.endpoints
    assigned.cut.report.final.services.length service.served service.emission service.emitted

variable {service : DataServed assigned}

def Released.cut (released : Released service) : Cut input complete where
  events := service.cut.events ++ [released.delivery.step.event]
  report := released.delivery.toDelivery.append service.cut.supported service.cut.finished
  supported := released.delivery.toDelivery.append_supported _ _
  finished := rfl
  endpoints := released.delivery.updated
  connection := released.delivery.connection

theorem release_data (service : DataServed assigned) : Nonempty (Released service) := by
  obtain ⟨recovery, reaction, ready⟩ := service.ready
  have selected : CampusTCPDeliveryEnabled.InOrderReady
      (endpoint service.cut.endpoints service.served.ticket.value.produced.actor.other)
      service.emission.asInput recovery reaction := by
    simpa only [service.actor, Actor.other] using ready
  obtain ⟨delivery⟩ := CampusTCPRoundDelivery.Report.deliver_data service.cut.report complete service.cut.endpoints
    service.cut.connection assigned.cut.report.final.services.length service.served service.facts.serviceIndex
    service.emission service.emitted service.application service.pending recovery reaction selected
  exact ⟨⟨delivery⟩⟩

theorem Released.server (released : Released service) :
    endpoint released.cut.endpoints .server = released.delivery.after := by
  change endpoint released.delivery.updated .server = _
  simpa only [service.actor, Actor.other] using released.delivery.selected

theorem Released.sender (released : Released service) :
    endpoint released.cut.endpoints .client = Endpoint.sendState (endpoint initial.start.next.endpoints .client) request.bytes.length := by
  have peer := released.delivery.peer
  simp only [service.actor, Actor.other] at peer
  exact peer.trans sent.sender

theorem Released.payload (released : Released service) :
    (endpoint released.cut.endpoints .server).core.received = request.bytes := by
  rw [released.server]
  have received := released.delivery.received
  simp only [service.actor, Actor.other] at received
  change released.delivery.after.core.received = (endpoint sent.cut.endpoints .server).core.received ++ _ at received
  rw [sent.receiver, initial.start.server] at received
  simpa only [CampusTCPRoundSetup.preparedSeed, CampusTCPRoundSetup.ackState,
    CampusTCPRoundSetup.recoveryState, complete.certificate.empty.2.2.2.2.2,
    service.emitted_payload, List.nil_append] using received

theorem Released.receiveNext (released : Released service) :
    (endpoint released.cut.endpoints .server).core.receiveNext = (input.active.iss.add 1).add request.bytes.length := by
  rw [released.server]
  have cursor := released.delivery.receiveNext
  simp only [service.actor, Actor.other] at cursor
  change released.delivery.after.core.receiveNext = (endpoint sent.cut.endpoints .server).core.receiveNext.add _ at cursor
  rw [sent.receiver, initial.start.server] at cursor
  simpa only [CampusTCPRoundSetup.preparedSeed, CampusTCPRoundSetup.ackState, CampusTCPRoundSetup.recoveryState,
    complete.certificate.initial_sequences.2.2.2.2.2, complete.activeConfig, service.emitted_payload] using cursor

theorem Released.sendNext (released : Released service) :
    (endpoint released.cut.endpoints .server).core.sendNext = input.passive.iss.add 1 := by
  rw [released.server]
  have cursor := released.delivery.sendNext
  simp only [service.actor, Actor.other] at cursor
  change released.delivery.after.core.sendNext = (endpoint sent.cut.endpoints .server).core.sendNext at cursor
  rw [sent.receiver, initial.start.server] at cursor
  simpa only [CampusTCPRoundSetup.preparedSeed, CampusTCPRoundSetup.ackState, CampusTCPRoundSetup.recoveryState,
    complete.certificate.initial_sequences.2.2.2.2.1, complete.passiveConfig] using cursor

theorem Released.inbound (released : Released service) :
    (endpoint released.cut.endpoints .server).core.inbound = complete.certificate.passiveSeed.core.inbound := by
  rw [released.server]
  have inbound := released.delivery.inbound
  simp only [service.actor, Actor.other] at inbound
  change released.delivery.after.core.inbound = (endpoint sent.cut.endpoints .server).core.inbound at inbound
  rw [sent.receiver, initial.start.server] at inbound
  exact inbound

structure Acked (released : Released service) where
  actual : Step input
  facts : CampusTCPRoundAck.AckFacts released.cut.report.final complete released.cut.endpoints .server actual

variable {released : Released service}

def Acked.cut (ack : Acked released) : Cut input complete where
  events := released.cut.events ++ [ack.actual.event]
  report := CampusTCPSchedule.Report.appendStep released.cut.report released.cut.supported released.cut.finished
    ack.actual ack.facts.beforeEq ack.facts.supported
  supported := CampusTCPSchedule.Report.appendStep_supported _ _ _ _ _ _
  finished := rfl
  endpoints := ack.facts.after
  connection := ack.facts.connection

theorem emit_ack (released : Released service) : Nonempty (Acked released) := by
  have prepared : Endpoint.AckPrepared (endpoint released.cut.endpoints .server) := by
    rw [released.server]
    exact released.delivery.prepared
  have available : Endpoint.ResponseAvailable (endpoint released.cut.endpoints .server) false := by
    rw [released.server]
    exact released.delivery.available
  obtain ⟨actual, ⟨facts⟩⟩ := CampusTCPRoundAck.Report.emitAck_enabled released.cut.report complete released.cut.endpoints
    released.cut.connection .server prepared available
  exact ⟨⟨actual, facts⟩⟩

theorem Released.gateway (released : Released service) :
    beforeService input released.cut.report.final .primary = beforeService input service.cut.report.final .primary := by
  change beforeService input released.delivery.step.result.state .primary = _
  have selected : CampusTCPRoundEnvironment.Nonservice released.delivery.step.event := by
    rw [released.delivery.event]
    trivial
  rw [CampusTCPRoundLocal.step_service_nonservice released.delivery.step selected, released.delivery.beforeEq]

theorem Released.environment (released : Released service) :
    CampusTCPRoundEnvironment.environment initial.state = CampusTCPRoundEnvironment.environment released.cut.report.final :=
  assigned.environment.trans (service.facts.environment.trans released.delivery.environment)

theorem Acked.source_fields (ack : Acked released) :
    ack.facts.produced.source.packet.header = Output.reverse complete.certificate.passiveSeed.core.inbound ∧
      ack.facts.produced.source.packet.segment.sequence = input.passive.iss.add 1 ∧
      ack.facts.produced.source.packet.segment.acknowledgment = (input.active.iss.add 1).add request.bytes.length ∧
      ack.facts.produced.source.packet.segment.payload = [] ∧
      Admission.DataProfile ack.facts.produced.source.packet.segment ∧
      1 < ack.facts.produced.source.packet.ip.packet.ttl.toNat := by
  have fields := ack.facts.source_fields
  rw [released.inbound, released.sendNext, released.receiveNext] at fields
  exact fields

theorem Acked.gateway (ack : Acked released) :
    beforeService input ack.cut.report.final .primary = beforeService input service.cut.report.final .primary := by
  change beforeService input ack.actual.result.state .primary = _
  have selected : CampusTCPRoundEnvironment.Nonservice ack.actual.event := by rw [ack.facts.event]; trivial
  rw [CampusTCPRoundLocal.step_service_nonservice ack.actual selected, ack.facts.beforeEq]
  exact released.gateway

theorem Acked.environment (ack : Acked released) :
    CampusTCPRoundEnvironment.environment initial.state = CampusTCPRoundEnvironment.environment ack.cut.report.final :=
  released.environment.trans ack.facts.environment

theorem Acked.sender (ack : Acked released) :
    endpoint ack.cut.endpoints .client = Endpoint.sendState (endpoint initial.start.next.endpoints .client) request.bytes.length :=
  ack.facts.peer.trans released.sender

theorem Acked.payload (ack : Acked released) : (endpoint ack.cut.endpoints .server).core.received = request.bytes := by
  change (endpoint ack.facts.after .server).core.received = _
  rw [ack.facts.selected]
  exact released.payload

end Netlib.Check.CampusTCPRound
