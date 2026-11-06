import Netlib.Check.CampusTCPRoundPhaseBase
import Netlib.Check.CampusTCPRoundMonitorFacts

/-!
# Forward phase actions at actual current cuts

The next operation uses the current report and its endpoint histories.
Earlier packet records keep their actual source state and stamp.
-/

namespace Netlib.Check.CampusTCPRoundPhaseForward

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRound (Cut)
namespace B
export CampusTCPRoundPhaseBase
  (At Move Hop Anchor Current Sent Assigned DataServed Released Acked ApplicationOutput OriginalFields config)
end B
namespace M
export CampusTCPRoundMonitor (Monitor Phase References nextAction advance ingressAction ticketAction linkAction)
end M
namespace F
export CampusTCPRoundMonitorFacts
  (observe_action observeOutput_eq observeAssignment_eq observeService_eq observeReceipt_eq
    output_pending service_pending AssignmentFacts.find_new)
end F

variable {input : Input} {events : List Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}
variable {initial : Initial report complete request} {native : NativeEnv initial}

private def networkMove (current : Cut input complete) (actual : Step input)
    (before : actual.before = current.report.final) (supported : actual.result.supported = true)
    (passed : actual.result.passed = true) (action : CampusTCPRoundClock.NetworkAction actual.event) : B.Move current actual :=
  ⟨current.appendNetwork actual before supported action, before, supported, passed, rfl, rfl⟩

theorem send_at (initial : Initial report complete request) (native : NativeEnv initial)
    (current : Cut input complete) (placement : B.At (Cut.ofPrepared initial.start) current) :
    ∃ sent : B.Sent initial native, sent.hop.before = current := by
  let state := endpoint current.endpoints .client
  have client : endpoint current.endpoints .client = endpoint initial.start.next.endpoints .client :=
    placement.frame.endpointEq .client
  have server : endpoint current.endpoints .server = endpoint initial.start.next.endpoints .server :=
    placement.frame.endpointEq .server
  have ready : Endpoint.SendReady state request.bytes.length := by
    change Endpoint.SendReady (endpoint current.endpoints .client) _
    rw [client]
    exact initial.send_ready
  have prepared : Endpoint.AckPrepared state := by
    change Endpoint.AckPrepared (endpoint current.endpoints .client)
    rw [client]
    exact initial.start.client_ack
  have earlier := (CampusTCPChronology.Report.application_before current.report complete current.endpoints current.connection).1
  obtain ⟨effect, produced, computed, supported, output, actor, payload, recorded⟩ := send_enabled
    current.report.final complete current.endpoints current.connection .client request.bytes.length earlier ready prepared
  let actual : Step input := ⟨_, _, effect, computed⟩
  let operation := ApplicationTrace.Step.make state (endpoint_valid current.endpoints .client)
    (.send request.bytes.length true) current.report.final.time
  have application : actual.result.application = some (.client, operation) := recorded
  have emitted : actual.result.output = some produced := output
  obtain ⟨appended⟩ := current.appendLocal actual rfl supported .client (.send request.bytes.length true)
    (.send request.bytes.length true) operation application
  have passed : actual.result.passed = true := CampusTCPRoundLocal.step_local_passed actual .client
    (.send request.bytes.length true) (.send request.bytes.length true)
  let move : B.Move current actual := ⟨appended.next, rfl, supported, passed, appended.history, appended.final⟩
  let hop : B.Hop (Cut.ofPrepared initial.start) CampusTCPRoundMonitor.Monitor.initial := ⟨current, placement, actual, move⟩
  have final : hop.post.report.final = actual.result.state := move.final
  obtain ⟨packet, origin, production⟩ := CampusTCPRoundLocal.step_application_output actual complete
    current.endpoints current.connection .client (.send request.bytes.length true)
    (.send request.bytes.length true) operation application produced emitted
  have localEvent : operation.event = .send request.bytes.length true := rfl
  have noRetry : ApplicationTrace.NoRetry operation := by intro policy event; cases event
  obtain ⟨bytes, encoded⟩ := CampusTCPRoundLocal.original_encoded origin noRetry
  have transport := Endpoint.emit_transport _ _ _ encoded
  rw [appended.localBefore, client, initial.start.client] at transport
  have profile := CampusTCPRoundLocal.emit_profile _ _ _ encoded
  have sourcePacket : produced.source.packet = packet.packet := by rw [production]; rfl
  have packetPayload : packet.packet.segment.payload = request.bytes := by
    have value := payload
    rw [production] at value
    simpa only [Produced.output, client, initial.start.client, Endpoint.writeState,
      CampusTCPRoundSetup.preparedSeed, CampusTCPRoundSetup.ackState, CampusTCPRoundSetup.recoveryState,
      complete.certificate.empty.1, List.nil_append, List.take_length] using value
  have fields : B.OriginalFields (complete := complete) (request := request) produced := by
    constructor
    · rw [sourcePacket]
      exact transport.1
    · rw [sourcePacket]
      simpa only [Endpoint.writeState, CampusTCPRoundSetup.preparedSeed, CampusTCPRoundSetup.ackState,
        CampusTCPRoundSetup.recoveryState, complete.certificate.initial_sequences.2.1, complete.activeConfig] using transport.2.1
    · rw [sourcePacket]
      simpa only [Endpoint.writeState, CampusTCPRoundSetup.preparedSeed, CampusTCPRoundSetup.ackState,
        CampusTCPRoundSetup.recoveryState, complete.certificate.initial_sequences.2.2.1, complete.passiveConfig] using transport.2.2.1
    · rw [sourcePacket]; exact packetPayload
    · rw [sourcePacket]; exact profile.1
    · rw [sourcePacket]; exact profile.2.2.2
  obtain ⟨wire, sent⟩ := Endpoint.send_success_enabled state request.bytes.length (endpoint_valid current.endpoints .client)
    ready prepared
  have selected : operation.result.state = Endpoint.sendState state request.bytes.length := by
    change (Endpoint.send state request.bytes.length true).state = _
    rw [sent]
  have sender : endpoint hop.post.endpoints .client =
      Endpoint.sendState (endpoint initial.start.next.endpoints .client) request.bytes.length := by
    exact appended.selected.trans (selected.trans (congrArg (fun value => Endpoint.sendState value request.bytes.length) client))
  have receiver : endpoint hop.post.endpoints .server = endpoint initial.start.next.endpoints .server :=
    appended.peer.trans server
  have source : hop.post.report.final.outputs[actual.before.outputs.length]? = some produced := by
    rw [final, CampusTCPOrigins.output_history actual, emitted]
    simp
  obtain ⟨packetItem, member, _, minted⟩ := CampusTCPCustodyFacts.Step.output_packet actual produced emitted
  have pending : IngressPending hop.post.report.final actual.before.outputs.length := by
    rw [final]
    exact ⟨packetItem, member, by simp only [minted, Transit.ingressAt, beq_self_eq_true]⟩
  obtain ⟨id, pendingID⟩ := F.output_pending actual produced emitted
  have observed : hop.monitor (B.config initial native) =
      { phase := .dataIngress, refs := { dataOutput := some actual.before.outputs.length, dataIngressPacket := some id } } := by
    change CampusTCPRoundMonitor.observe _ CampusTCPRoundMonitor.Monitor.initial actual = _
    rw [F.observe_action _ CampusTCPRoundMonitor.Monitor.initial actual (.send .client request.bytes.length true) supported passed rfl rfl]
    exact F.observeOutput_eq CampusTCPRoundMonitor.Monitor.initial actual .client .dataIngress produced emitted actor pendingID
  have guards : CampusTCPRoundGuards.Guards hop.post.endpoints := by
    intro receiverActor
    cases receiverActor
    · rw [sender]
      exact CampusTCPRoundGuards.PreparedStart.sent_guards initial.start request.nonempty request.mssFits request.receiveFits
    · rw [receiver]
      exact CampusTCPRoundGuards.PreparedStart.server_guards initial.start
  have environment : CampusTCPRoundEnvironment.environment initial.state = CampusTCPRoundEnvironment.environment hop.post.report.final := by
    exact placement.frame.environment.symm.trans
      (final ▸ CampusTCPRoundEnvironment.Step.environment actual trivial)
  have gateway : beforeService input hop.post.report.final .primary = initial.beforeService := by
    rw [final, CampusTCPRoundLocal.step_service_nonservice actual trivial]
    exact placement.frame.beforeService .primary
  refine ⟨⟨hop, rfl, ⟨operation, application, packet, origin, produced, emitted, production,
    appended.localBefore, rfl⟩, localEvent, fields, sender, receiver, gateway, source, pending, ?_⟩, rfl⟩
  refine ⟨?_, ?_, guards, placement.retained.trans move.retained, environment⟩
  · rw [observed]
  · rw [observed]
    change M.ingressAction hop.post.report.final (some actual.before.outputs.length) (some id) native.dataIngress = _
    simp only [M.ingressAction, source, bind, Option.bind]
    rw [final, pendingID]
    simp only [beq_self_eq_true, ite_true]
    rfl

theorem assign_at (sent : B.Sent initial native) (current : Cut input complete)
    (placement : B.At sent.hop.post current) : ∃ assigned : B.Assigned sent, assigned.hop.before = current := by
  let oldMonitor := sent.hop.monitor (B.config initial native)
  have environment : CampusTCPRoundEnvironment.environment initial.state = CampusTCPRoundEnvironment.environment current.report.final :=
    sent.anchor.environment.trans placement.frame.environment.symm
  have source : current.report.final.outputs[sent.index]? = some sent.application.produced := by
    rw [placement.frame.outputs]
    exact sent.source
  have pending : IngressPending current.report.final sent.index := by
    simpa only [IngressPending, placement.frame.custody, CampusTCPRoundPhaseBase.Sent.index] using sent.pending
  obtain ⟨actual, facts⟩ := CampusTCPRoundAssignment.Report.assign_enabled current.report sent.index native.dataIngress
    sent.application.produced source (native.route_at current.report.final environment sent.application.produced.actor) pending
  let move := networkMove current actual facts.beforeEq facts.supported facts.passed
    (facts.event ▸ CampusTCPRoundClock.NetworkAction.assign _ _)
  let hop : B.Hop sent.hop.post oldMonitor := ⟨current, placement, actual, move⟩
  let ticket := CampusTCPRoundAssignment.ticket current.report.final sent.index native.dataIngress sent.application.produced
  have final : hop.post.report.final = actual.result.state := move.final
  have ticketID : ticket.id = actual.before.work.nextID := by rw [facts.beforeEq]; rfl
  have next : M.nextAction (B.config initial native) actual.before oldMonitor = some (.assign sent.index native.dataIngress) := by
    rw [facts.beforeEq, CampusTCPRoundPhaseBase.Frame.nextAction placement.frame]
    exact sent.anchor.next
  have observed : hop.monitor (B.config initial native) =
      { phase := .dataTicket, refs := { oldMonitor.refs with dataTicket := some ticket.id } } := by
    have phase : oldMonitor.phase = .dataIngress := sent.anchor.phaseEq
    change CampusTCPRoundMonitor.observe _ oldMonitor actual = _
    rw [F.observe_action _ oldMonitor actual (.assign sent.index native.dataIngress) facts.supported facts.passed next facts.event]
    simp only [M.advance, phase]
    exact F.observeAssignment_eq oldMonitor actual .client .dataTicket ticket
      (CampusTCPRoundMonitorFacts.AssignmentFacts.find_new facts)
  have gateway : beforeService input hop.post.report.final .primary = initial.beforeService := by
    have nonservice : CampusTCPRoundEnvironment.Nonservice actual.event := by rw [facts.event]; trivial
    rw [final, CampusTCPRoundLocal.step_service_nonservice actual nonservice, facts.beforeEq,
      placement.frame.beforeService .primary]
    exact sent.gateway
  have sender : endpoint hop.post.endpoints .client =
      Endpoint.sendState (endpoint initial.start.next.endpoints .client) request.bytes.length :=
    (placement.frame.endpointEq .client).trans sent.sender
  have receiver : endpoint hop.post.endpoints .server = endpoint initial.start.next.endpoints .server :=
    (placement.frame.endpointEq .server).trans sent.receiver
  have ticketPending : ticket ∈ hop.post.report.final.work.pending := by
    rw [final]
    exact facts.pending
  refine ⟨⟨hop, facts, ticket, rfl, sender, receiver, gateway, ticketPending, ?_⟩, rfl⟩
  refine ⟨?_, ?_, ?_, sent.anchor.retained.trans hop.retained, ?_⟩
  · rw [observed]
  · rw [observed]
    change M.ticketAction hop.post.report.final (some ticket.id) = some (.serve ticket.id)
    simp only [M.ticketAction, bind, Option.bind]
    rw [final, ticketID, CampusTCPRoundMonitorFacts.AssignmentFacts.find_new facts]
    rfl
  · exact CampusTCPRoundPhaseBase.Frame.guards placement.frame sent.anchor.guards
  · have fixed := CampusTCPRoundEnvironment.Step.environment actual (by rw [facts.event]; trivial)
    rw [facts.beforeEq] at fixed
    exact environment.trans (final ▸ fixed)

theorem serve_data_at {sent : B.Sent initial native} (assigned : B.Assigned sent) (current : Cut input complete)
    (placement : B.At assigned.hop.post current) : ∃ service : B.DataServed assigned, service.hop.before = current := by
  let oldMonitor := assigned.hop.monitor (B.config initial native)
  have environment := assigned.anchor.environment.trans placement.frame.environment.symm
  have same : beforeService input current.report.final .primary = initial.beforeService :=
    (placement.frame.beforeService .primary).trans assigned.gateway
  have beforeEnvironment := sent.anchor.environment.trans assigned.hop.placement.frame.environment.symm
  have primary : assigned.ticket.value.gateway = .primary := by
    rw [assigned.ticketEq]
    exact native.owner_at assigned.hop.before.report.final beforeEnvironment sent.application.produced.actor
  have ticketSource : assigned.ticket.value.source = sent.application.produced.source := by rw [assigned.ticketEq]; rfl
  have ticketIngress : assigned.ticket.value.ingress = native.dataIngress := by rw [assigned.ticketEq]; rfl
  have ticketActor : assigned.ticket.value.produced.actor = .client := by
    rw [assigned.ticketEq]
    change sent.application.produced.actor = .client
    rw [sent.application.production]
    rfl
  have ready : CampusTCPService.ExistingDataReady (input.contextFor assigned.ticket.value.gateway)
      (beforeService input current.report.final assigned.ticket.value.gateway) assigned.ticket.value.source input.zone
      assigned.ticket.value.ingress ⟨initial.entry.flow, .original⟩ initial.session assigned.ticket.value.produced.actor.nextHop := by
    rw [primary, ticketSource, ticketIngress, ticketActor]
    apply CampusTCPRoundGateway.original_ready input complete initial.aligned native.original
      (beforeService input current.report.final .primary) (congrArg CampusTCPService.Before.environment same.symm)
      sent.application.produced.source sent.fields.header
    · rw [same]; exact initial.valid
    · rw [same]; exact initial.records
    · rw [same]; exact initial.phase
    · exact sent.fields.sequence
    · exact sent.fields.acknowledgment
    · exact sent.fields.profile
    · rw [sent.fields.payload]; exact request.nonempty
    · rw [sent.fields.payload]; exact request.peer_mss complete
    · rw [sent.fields.payload]; exact request.receiveFits
    · rw [sent.fields.payload]; exact request.epoch complete
    · exact sent.fields.ttl
  have pending : assigned.ticket ∈ current.report.final.work.pending := by
    rw [placement.frame.work]
    exact assigned.pending
  have servicePhase : CampusTCPGatewayEnabled.ServicePhaseReady current.report.final assigned.ticket.value.gateway := by
    rw [primary]
    exact native.service_phase_at current.report.final environment
  obtain ⟨actual, served, emission, emitted, facts⟩ := CampusTCPRoundService.Report.serve_enabled current.report
    assigned.ticket pending servicePhase ⟨initial.entry.flow, .original⟩ initial.session ready
  let move := networkMove current actual facts.beforeEq facts.supported facts.passed
    (facts.event ▸ CampusTCPRoundClock.NetworkAction.serve _ _)
  let hop : B.Hop assigned.hop.post oldMonitor := ⟨current, placement, actual, move⟩
  have final : hop.post.report.final = actual.result.state := move.final
  have fields : B.OriginalFields (complete := complete) (request := request) served.ticket.value.produced := by
    rw [facts.ticket, assigned.ticketEq]
    exact sent.fields
  have sourcePayload : served.ticket.value.source.packet.segment.payload = request.bytes := fields.payload
  have serviceBefore : served.before = initial.beforeService := by
    rw [facts.current, primary]
    exact same
  obtain ⟨processing, present, _, entry, direction, existing⟩ := facts.processing
  have phase : served.before.admission.phase = .data initial.session := by rw [serviceBefore]; exact initial.phase
  have oldRecords : served.before.tracker.records = [⟨initial.entry, true⟩] := by rw [serviceBefore]; exact initial.records
  obtain ⟨session, committed, geometry⟩ := CampusTCPRoundAdmission.Processing.original_empty_geometry processing
    initial.session phase direction initial.aligned.originalCoverage initial.aligned.originalAcknowledged
    initial.aligned.replyCoverage initial.aligned.replyAcknowledged
    (fields.sequence.trans initial.aligned.originalBase.symm) (fields.acknowledgment.trans initial.aligned.replyBase.symm)
    fields.profile (by rw [sourcePayload]; exact request.nonempty)
    (by rw [sourcePayload, initial.aligned.serverMSS]; exact request.peer_mss complete)
    (by rw [sourcePayload, initial.aligned.originalWindow]; exact request.receiveFits)
    (by rw [sourcePayload]; exact request.epoch complete)
  have transport := facts.transport
  rw [primary] at transport
  change actual.result.state.primary.transport = ⟨served.evidence.tracker, served.evidence.admission⟩ at transport
  have postPhase : (beforeService input hop.post.report.final .primary).admission.phase = .data session := by
    rw [final]
    change actual.result.state.primary.transport.admission.phase = _
    rw [transport, (served.evidence.processing_states processing present).2]
    exact committed
  have tracker := CampusTCPRoundGateway.Evidence.singleton_data_records served.evidence processing present initial.session phase oldRecords
  have postTracker : (beforeService input hop.post.report.final .primary).tracker.Valid ∧
      (beforeService input hop.post.report.final .primary).tracker.records = [⟨initial.entry, true⟩] := by
    rw [final]
    change actual.result.state.primary.transport.tracker.Valid ∧ actual.result.state.primary.transport.tracker.records = _
    rw [transport]
    exact tracker
  have stored : hop.post.report.final.services[actual.before.services.length]? = some served := by
    rw [final, facts.beforeEq]
    exact facts.serviceIndex
  have linkPending : CampusTCPDeliveryEnabled.LinkPending hop.post.report.final actual.before.services.length := by
    obtain ⟨packet, member, _, source, _⟩ := facts.link
    rw [final, facts.beforeEq]
    refine ⟨packet, member, ?_⟩
    simp only [source, Transit.linkAt, beq_self_eq_true]
  have next : M.nextAction (B.config initial native) actual.before oldMonitor = some (.serve assigned.ticket.id) := by
    rw [facts.beforeEq, CampusTCPRoundPhaseBase.Frame.nextAction placement.frame]
    exact assigned.anchor.next
  obtain ⟨id, pendingID⟩ := F.service_pending actual served facts.recorded emission emitted
  have observed : hop.monitor (B.config initial native) =
      { phase := .dataLink, refs := { oldMonitor.refs with dataService := some actual.before.services.length, dataLinkPacket := some id } } := by
    have oldPhase : oldMonitor.phase = .dataTicket := assigned.anchor.phaseEq
    change CampusTCPRoundMonitor.observe _ oldMonitor actual = _
    rw [F.observe_action _ oldMonitor actual (.serve assigned.ticket.id) facts.supported facts.passed next facts.event]
    simp only [M.advance, oldPhase]
    exact F.observeService_eq oldMonitor actual .client .dataLink served facts.recorded emission emitted pendingID
  refine ⟨⟨hop, served, emission, emitted, facts, fields, session, postPhase, geometry, postTracker.1, postTracker.2,
    (placement.frame.endpointEq .client).trans assigned.sender,
    (placement.frame.endpointEq .server).trans assigned.receiver, stored, linkPending, ?_⟩, rfl⟩
  refine ⟨?_, ?_, ?_, assigned.anchor.retained.trans hop.retained, ?_⟩
  · rw [observed]
  · rw [observed]
    change M.linkAction hop.post.report.final (some actual.before.services.length) (some id) = _
    simp only [M.linkAction, stored, emitted, bind, Option.bind]
    rw [final, pendingID]
    simp only [beq_self_eq_true, ite_true]
    rfl
  · exact CampusTCPRoundPhaseBase.Frame.guards placement.frame assigned.anchor.guards
  · exact environment.trans (final ▸ facts.environment)

theorem release_data_at {sent : B.Sent initial native} {assigned : B.Assigned sent}
    (service : B.DataServed assigned) (current : Cut input complete) (placement : B.At service.hop.post current) :
    ∃ released : B.Released service, released.hop.before = current := by
  let oldMonitor := service.hop.monitor (B.config initial native)
  have actor : service.served.ticket.value.produced.actor = .client := by
    rw [service.facts.ticket, assigned.ticketEq]
    change sent.application.produced.actor = .client
    rw [sent.application.production]
    rfl
  have application : CampusTCPDeliveryEnabled.ApplicationSource service.served.ticket.value.produced := by
    rw [service.facts.ticket, assigned.ticketEq]
    change CampusTCPDeliveryEnabled.ApplicationSource sent.application.produced
    rw [sent.application.production]
    trivial
  have receiver : endpoint current.endpoints .server = endpoint initial.start.next.endpoints .server :=
    (placement.frame.endpointEq .server).trans service.receiver
  obtain ⟨recovery, reaction, oldReady⟩ := CampusTCPRoundEmission.data_ready initial service.emission service.facts.target
    service.sourceFields.sequence service.sourceFields.acknowledgment service.sourceFields.payload service.sourceFields.profile
  have ready : CampusTCPDeliveryEnabled.InOrderReady
      (endpoint current.endpoints service.served.ticket.value.produced.actor.other) service.emission.asInput recovery reaction := by
    simpa only [actor, Actor.other, receiver] using oldReady
  have stored : current.report.final.services[service.index]? = some service.served := by
    rw [placement.frame.services]
    exact service.stored
  have pending : CampusTCPDeliveryEnabled.LinkPending current.report.final service.index := by
    simpa only [CampusTCPDeliveryEnabled.LinkPending, placement.frame.custody, CampusTCPRoundPhaseBase.DataServed.index]
      using service.pending
  obtain ⟨delivery⟩ := CampusTCPRoundDelivery.Report.deliver_data current.report complete current.endpoints
    current.connection service.index service.served stored service.emission service.emitted application pending recovery reaction ready
  let next : Cut input complete := ⟨_, delivery.toDelivery.append current.supported current.finished,
    delivery.toDelivery.append_supported _ _, rfl, delivery.updated, delivery.connection⟩
  let move : B.Move current delivery.step := ⟨next, delivery.beforeEq, delivery.supported, delivery.passed, rfl, rfl⟩
  let hop : B.Hop service.hop.post oldMonitor := ⟨current, placement, delivery.step, move⟩
  have final : hop.post.report.final = delivery.step.result.state := move.final
  have server : endpoint hop.post.endpoints .server = delivery.after := by
    change endpoint delivery.updated .server = delivery.after
    simpa only [actor, Actor.other] using delivery.selected
  have sender : endpoint hop.post.endpoints .client =
      Endpoint.sendState (endpoint initial.start.next.endpoints .client) request.bytes.length := by
    have peer := delivery.peer
    simp only [actor, Actor.other] at peer
    exact peer.trans ((placement.frame.endpointEq .client).trans service.sender)
  have emittedPayload : service.emission.asInput.packet.segment.payload = request.bytes :=
    service.emission.payload.trans service.sourceFields.payload
  have payload : (endpoint hop.post.endpoints .server).core.received = request.bytes := by
    rw [server]
    have received := delivery.received
    simp only [actor, Actor.other, receiver, initial.start.server, CampusTCPRoundSetup.preparedSeed,
      CampusTCPRoundSetup.ackState, CampusTCPRoundSetup.recoveryState, complete.certificate.empty.2.2.2.2.2,
      emittedPayload, List.nil_append] at received
    exact received
  have receiveNext : (endpoint hop.post.endpoints .server).core.receiveNext =
      (input.active.iss.add 1).add request.bytes.length := by
    rw [server]
    have cursor := delivery.receiveNext
    simpa only [actor, Actor.other, receiver, initial.start.server, CampusTCPRoundSetup.preparedSeed,
      CampusTCPRoundSetup.ackState, CampusTCPRoundSetup.recoveryState, complete.certificate.initial_sequences.2.2.2.2.2,
      complete.activeConfig, emittedPayload] using cursor
  have sendNext : (endpoint hop.post.endpoints .server).core.sendNext = input.passive.iss.add 1 := by
    rw [server]
    have cursor := delivery.sendNext
    simpa only [actor, Actor.other, receiver, initial.start.server, CampusTCPRoundSetup.preparedSeed,
      CampusTCPRoundSetup.ackState, CampusTCPRoundSetup.recoveryState, complete.certificate.initial_sequences.2.2.2.2.1,
      complete.passiveConfig] using cursor
  have inbound : (endpoint hop.post.endpoints .server).core.inbound = complete.certificate.passiveSeed.core.inbound := by
    rw [server]
    simpa only [actor, Actor.other, receiver, initial.start.server, CampusTCPRoundSetup.preparedSeed,
      CampusTCPRoundSetup.ackState, CampusTCPRoundSetup.recoveryState] using delivery.inbound
  have gateway : beforeService input hop.post.report.final .primary = beforeService input service.hop.post.report.final .primary := by
    rw [final, CampusTCPRoundLocal.step_service_nonservice delivery.step (by rw [delivery.event]; trivial), delivery.beforeEq]
    exact placement.frame.beforeService .primary
  have nextAction : M.nextAction (B.config initial native) delivery.step.before oldMonitor =
      some (.deliver service.index service.emission.bytes true) := by
    rw [delivery.beforeEq, CampusTCPRoundPhaseBase.Frame.nextAction placement.frame]
    exact service.anchor.next
  have receiptActor : delivery.receipt.actor = .server := by
    rw [delivery.receipt.receiver, delivery.receiptService, actor]
    rfl
  have recorded : delivery.step.result.application = some (.server, delivery.localStep) := by
    simpa only [actor, Actor.other] using delivery.recorded
  have observed : hop.monitor (B.config initial native) = { phase := .needAck, refs := { oldMonitor.refs with
      dataReceipt := some delivery.step.before.receipts.length, dataReceiveStamp := some delivery.localStep.stamp } } := by
    have phase : oldMonitor.phase = .dataLink := service.anchor.phaseEq
    change CampusTCPRoundMonitor.observe _ oldMonitor delivery.step = _
    rw [F.observe_action _ oldMonitor delivery.step (.deliver service.index service.emission.bytes true)
      delivery.supported delivery.passed nextAction delivery.event]
    simp only [M.advance, phase]
    exact F.observeReceipt_eq oldMonitor delivery.step .server .needAck delivery.receipt delivery.receiptAt
      receiptActor delivery.localStep recorded
  refine ⟨⟨hop, delivery, rfl, server, sender, payload, receiveNext, sendNext, inbound, gateway, ?_⟩, rfl⟩
  refine ⟨?_, ?_, ?_, service.anchor.retained.trans hop.retained, ?_⟩
  · rw [observed]
  · rw [observed]
    rfl
  · exact CampusTCPRoundGuards.DataDelivered.guards delivery recovery reaction ready
      (CampusTCPRoundPhaseBase.Frame.guards placement.frame service.anchor.guards)
  · exact (service.anchor.environment.trans placement.frame.environment.symm).trans (final ▸ delivery.environment)

theorem emit_ack_at {sent : B.Sent initial native} {assigned : B.Assigned sent} {service : B.DataServed assigned}
    (released : B.Released service) (current : Cut input complete) (placement : B.At released.hop.post current) :
    ∃ ack : B.Acked released, ack.hop.before = current := by
  let oldMonitor := released.hop.monitor (B.config initial native)
  have guards := CampusTCPRoundPhaseBase.Frame.guards placement.frame released.anchor.guards
  have server : endpoint current.endpoints .server = released.delivery.after :=
    (placement.frame.endpointEq .server).trans released.server
  have available : Endpoint.ResponseAvailable (endpoint current.endpoints .server) false := by
    rw [server]
    exact released.delivery.available
  obtain ⟨actual, ⟨facts⟩⟩ := CampusTCPRoundAck.Report.emitAck_enabled current.report complete current.endpoints
    current.connection .server (guards .server).prepared available
  let next : Cut input complete := ⟨_, CampusTCPSchedule.Report.appendStep current.report current.supported current.finished
    actual facts.beforeEq facts.supported, CampusTCPSchedule.Report.appendStep_supported _ _ _ _ _ _, rfl,
    facts.after, facts.connection⟩
  let move : B.Move current actual := ⟨next, facts.beforeEq, facts.supported, facts.passed, rfl, rfl⟩
  let hop : B.Hop released.hop.post oldMonitor := ⟨current, placement, actual, move⟩
  have final : hop.post.report.final = actual.result.state := move.final
  have fields : CampusTCPRoundPhaseBase.AckFields (complete := complete) (request := request) facts.produced := by
    have source := facts.source_fields
    rw [placement.frame.endpointEq .server, released.inbound, released.sendNext, released.receiveNext] at source
    exact ⟨source.1, source.2.1, source.2.2.1, source.2.2.2.1, source.2.2.2.2.1, source.2.2.2.2.2⟩
  have sender : endpoint hop.post.endpoints .client =
      Endpoint.sendState (endpoint initial.start.next.endpoints .client) request.bytes.length :=
    facts.peer.trans ((placement.frame.endpointEq .client).trans released.sender)
  have payload : (endpoint hop.post.endpoints .server).core.received = request.bytes := by
    change (endpoint facts.after .server).core.received = _
    rw [facts.selected]
    change (endpoint current.endpoints .server).core.received = _
    rw [placement.frame.endpointEq .server]
    exact released.payload
  have gateway : beforeService input hop.post.report.final .primary = beforeService input service.hop.post.report.final .primary := by
    rw [final, CampusTCPRoundLocal.step_service_nonservice actual (by rw [facts.event]; trivial), facts.beforeEq,
      placement.frame.beforeService .primary]
    exact released.gateway
  have source : hop.post.report.final.outputs[actual.before.outputs.length]? = some facts.produced := by
    rw [final, facts.beforeEq]
    exact facts.source
  have pending : IngressPending hop.post.report.final actual.before.outputs.length := by
    rw [final, facts.beforeEq]
    exact facts.pending
  have nextAction : M.nextAction (B.config initial native) actual.before oldMonitor = some (.emitAck .server true) := by
    rw [facts.beforeEq, CampusTCPRoundPhaseBase.Frame.nextAction placement.frame]
    exact released.anchor.next
  obtain ⟨id, pendingID⟩ := F.output_pending actual facts.produced facts.output
  have actor : facts.produced.actor = .server := by rw [facts.production]; rfl
  have observed : hop.monitor (B.config initial native) = { phase := .ackIngress, refs := { oldMonitor.refs with
      ackOutput := some actual.before.outputs.length, ackIngressPacket := some id } } := by
    have phase : oldMonitor.phase = .needAck := released.anchor.phaseEq
    change CampusTCPRoundMonitor.observe _ oldMonitor actual = _
    rw [F.observe_action _ oldMonitor actual (.emitAck .server true) facts.supported facts.passed nextAction facts.event]
    simp only [M.advance, phase]
    exact F.observeOutput_eq oldMonitor actual .server .ackIngress facts.produced facts.output actor pendingID
  refine ⟨⟨hop, facts, fields, sender, payload, gateway, source, pending, ?_⟩, rfl⟩
  refine ⟨?_, ?_, ?_, released.anchor.retained.trans hop.retained, ?_⟩
  · rw [observed]
  · rw [observed]
    change M.ingressAction hop.post.report.final (some actual.before.outputs.length) (some id) native.ackIngress = _
    simp only [M.ingressAction, source, bind, Option.bind]
    rw [final, pendingID]
    simp only [beq_self_eq_true, ite_true]
    rfl
  · exact CampusTCPRoundGuards.AckFacts.guards facts guards
  · exact (released.anchor.environment.trans placement.frame.environment.symm).trans (final ▸ facts.environment)

end Netlib.Check.CampusTCPRoundPhaseForward
