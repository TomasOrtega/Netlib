import Netlib.Check.CampusTCPRound

/-!
# Reverse ACK service and application read in one actual round

The data service supplies the reverse admission geometry.
The covering ACK retires the actual send range before the application reads it.
-/

namespace Netlib.Check.CampusTCPRoundReverse

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRound CampusTCPRoundStart

variable {input : Input} {events : List Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}
variable {initial : Initial report complete request} {native : NativeEnv initial}
variable {sent : Sent initial.start} {assigned : Assigned initial native sent}
variable {service : DataServed assigned} {released : Released service}

structure AckAssigned (ack : Acked released) where
  actual : Step input
  facts : CampusTCPRoundAssignment.AssignmentFacts ack.cut.report.final
    released.cut.report.final.outputs.length native.ackIngress ack.facts.produced actual

variable {ack : Acked released}

def AckAssigned.cut (assignment : AckAssigned ack) : Cut input complete :=
  ack.cut.appendNetwork assignment.actual assignment.facts.beforeEq assignment.facts.supported
    (assignment.facts.event ▸ CampusTCPRoundClock.NetworkAction.assign _ _)

def AckAssigned.ticket (_assignment : AckAssigned ack) :=
  CampusTCPRoundAssignment.ticket ack.cut.report.final released.cut.report.final.outputs.length
    native.ackIngress ack.facts.produced

theorem assign_ack (ack : Acked released) : Nonempty (AckAssigned ack) := by
  obtain ⟨actual, facts⟩ := CampusTCPRoundAssignment.Report.assign_enabled ack.cut.report
    released.cut.report.final.outputs.length native.ackIngress ack.facts.produced ack.facts.source
    (native.route_at ack.cut.report.final ack.environment ack.facts.produced.actor) ack.facts.pending
  exact ⟨⟨actual, facts⟩⟩

theorem AckAssigned.environment (assignment : AckAssigned ack) :
    CampusTCPRoundEnvironment.environment initial.state = CampusTCPRoundEnvironment.environment assignment.cut.report.final := by
  exact ack.environment.trans (by
    change CampusTCPRoundEnvironment.environment ack.cut.report.final =
      CampusTCPRoundEnvironment.environment assignment.actual.result.state
    simpa only [assignment.facts.beforeEq] using
      CampusTCPRoundEnvironment.Step.environment assignment.actual (by rw [assignment.facts.event]; trivial))

theorem AckAssigned.gateway (assignment : AckAssigned ack) :
    beforeService input assignment.cut.report.final .primary = beforeService input service.cut.report.final .primary := by
  change beforeService input assignment.actual.result.state .primary = _
  have selected : CampusTCPRoundEnvironment.Nonservice assignment.actual.event := by rw [assignment.facts.event]; trivial
  rw [CampusTCPRoundLocal.step_service_nonservice assignment.actual selected, assignment.facts.beforeEq]
  exact ack.gateway

theorem AckAssigned.primary (assignment : AckAssigned ack) : assignment.ticket.value.gateway = .primary :=
  native.owner_at ack.cut.report.final ack.environment ack.facts.produced.actor

theorem AckAssigned.actor (assignment : AckAssigned ack) : assignment.ticket.value.produced.actor = .server := by
  change ack.facts.produced.actor = .server
  rw [ack.facts.production]
  rfl

theorem AckAssigned.pending (assignment : AckAssigned ack) :
    assignment.ticket ∈ assignment.cut.report.final.work.pending := assignment.facts.pending

theorem AckAssigned.ready (assignment : AckAssigned ack) :
    ∃ session : Admission.Session,
      Nonempty (CampusTCPService.ExistingDataReady (input.contextFor assignment.ticket.value.gateway)
        (beforeService input assignment.cut.report.final assignment.ticket.value.gateway)
        assignment.ticket.value.source input.zone assignment.ticket.value.ingress
        ⟨initial.entry.flow, .reply⟩ session assignment.ticket.value.produced.actor.nextHop) := by
  obtain ⟨session, phase, geometry⟩ := service.geometry
  obtain ⟨header, sequence, acknowledgment, payload, profile, ttl⟩ := ack.source_fields
  have currentPhase : (beforeService input assignment.cut.report.final .primary).admission.phase = .data session := by
    rw [assignment.gateway]
    exact phase
  have currentValid : (beforeService input assignment.cut.report.final .primary).tracker.Valid := by
    rw [assignment.gateway]
    exact service.tracker.1
  have currentRecords : (beforeService input assignment.cut.report.final .primary).tracker.records = [⟨initial.entry, true⟩] := by
    rw [assignment.gateway]
    exact service.tracker.2
  refine ⟨session, ⟨?_⟩⟩
  rw [assignment.primary, assignment.actor]
  apply CampusTCPRoundGateway.reply_ready input complete initial.aligned geometry native.reply
    (beforeService input assignment.cut.report.final .primary)
    (initial.service_environment assignment.cut.report.final assignment.environment)
    ack.facts.produced.source header currentValid currentRecords currentPhase sequence
  · simpa only [service.source_fields.2.2.1] using acknowledgment
  · exact profile
  · exact payload
  · exact ttl

structure AckServed (assignment : AckAssigned ack) where
  session : Admission.Session
  actual : Step input
  served : Served input
  emission : WireForwarding.Emission served.ticket.value.source.packet
  emitted : served.evidence.output = some emission
  facts : CampusTCPRoundService.ServiceFacts assignment.cut.report.final assignment.ticket
    ⟨initial.entry.flow, .reply⟩ session actual served emission emitted

variable {assignment : AckAssigned ack}

def AckServed.cut (service : AckServed assignment) : Cut input complete :=
  assignment.cut.appendNetwork service.actual service.facts.beforeEq service.facts.supported
    (service.facts.event ▸ CampusTCPRoundClock.NetworkAction.serve _ _)

theorem serve_ack (assignment : AckAssigned ack) : Nonempty (AckServed assignment) := by
  obtain ⟨session, ⟨ready⟩⟩ := assignment.ready
  have phase : CampusTCPGatewayEnabled.ServicePhaseReady assignment.cut.report.final assignment.ticket.value.gateway := by
    rw [assignment.primary]
    exact native.service_phase_at assignment.cut.report.final assignment.environment
  obtain ⟨actual, served, emission, emitted, facts⟩ := CampusTCPRoundService.Report.serve_enabled
    assignment.cut.report assignment.ticket assignment.pending phase ⟨initial.entry.flow, .reply⟩ session ready
  exact ⟨⟨session, actual, served, emission, emitted, facts⟩⟩

theorem AckServed.source_fields (reverse : AckServed assignment) :
    reverse.served.ticket.value.source.packet.segment.sequence = input.passive.iss.add 1 ∧
      reverse.served.ticket.value.source.packet.segment.acknowledgment = (input.active.iss.add 1).add request.bytes.length ∧
      reverse.served.ticket.value.source.packet.segment.payload = [] ∧
      Admission.DataProfile reverse.served.ticket.value.source.packet.segment := by
  rw [reverse.facts.ticket]
  exact ⟨ack.source_fields.2.1, ack.source_fields.2.2.1, ack.source_fields.2.2.2.1, ack.source_fields.2.2.2.2.1⟩

theorem AckServed.actor (reverse : AckServed assignment) : reverse.served.ticket.value.produced.actor = .server := by
  rw [reverse.facts.ticket]
  exact assignment.actor

theorem AckServed.application (reverse : AckServed assignment) :
    CampusTCPDeliveryEnabled.ApplicationSource reverse.served.ticket.value.produced := by
  rw [reverse.facts.ticket]
  change CampusTCPDeliveryEnabled.ApplicationSource ack.facts.produced
  rw [ack.facts.production]
  trivial

theorem AckServed.pending (reverse : AckServed assignment) :
    CampusTCPDeliveryEnabled.LinkPending reverse.cut.report.final assignment.cut.report.final.services.length := by
  obtain ⟨packet, member, _, source, _⟩ := reverse.facts.link
  refine ⟨packet, member, ?_⟩
  simp only [source, Transit.linkAt, beq_self_eq_true]

theorem AckServed.ready (reverse : AckServed assignment) :
    ∃ recovery reaction, CampusTCPDeliveryEnabled.FullAckReady
      (endpoint reverse.cut.endpoints .client) reverse.emission.asInput recovery reaction := by
  obtain ⟨sequence, acknowledgment, payload, profile⟩ := reverse.source_fields
  obtain ⟨recovery, reaction, ready⟩ := CampusTCPRoundEmission.ack_ready initial reverse.emission
    reverse.facts.target sequence acknowledgment payload profile
  refine ⟨recovery, reaction, ?_⟩
  change CampusTCPDeliveryEnabled.FullAckReady (endpoint ack.cut.endpoints .client) _ _ _
  rw [ack.sender]
  exact ready

structure Retired (reverse : AckServed assignment) where
  delivery : CampusTCPRoundDelivery.AckDelivered reverse.cut.report complete reverse.cut.endpoints
    assignment.cut.report.final.services.length reverse.served reverse.emission reverse.emitted

variable {reverse : AckServed assignment}

def Retired.cut (retired : Retired reverse) : Cut input complete where
  events := reverse.cut.events ++ [retired.delivery.step.event]
  report := retired.delivery.toDelivery.append reverse.cut.supported reverse.cut.finished
  supported := retired.delivery.toDelivery.append_supported _ _
  finished := rfl
  endpoints := retired.delivery.updated
  connection := retired.delivery.connection

theorem deliver_ack (reverse : AckServed assignment) : Nonempty (Retired reverse) := by
  obtain ⟨recovery, reaction, ready⟩ := reverse.ready
  have selected : CampusTCPDeliveryEnabled.FullAckReady
      (endpoint reverse.cut.endpoints reverse.served.ticket.value.produced.actor.other)
      reverse.emission.asInput recovery reaction := by
    simpa only [reverse.actor, Actor.other] using ready
  obtain ⟨delivery⟩ := CampusTCPRoundDelivery.Report.deliver_full_ack reverse.cut.report complete reverse.cut.endpoints
    reverse.cut.connection assignment.cut.report.final.services.length reverse.served reverse.facts.serviceIndex
    reverse.emission reverse.emitted reverse.application reverse.pending recovery reaction selected
  exact ⟨⟨delivery⟩⟩

theorem Retired.sender (retired : Retired reverse) : endpoint retired.cut.endpoints .client = retired.delivery.after := by
  change endpoint retired.delivery.updated .client = _
  simpa only [reverse.actor, Actor.other] using retired.delivery.selected

theorem Retired.receiver (retired : Retired reverse) :
    endpoint retired.cut.endpoints .server = endpoint ack.cut.endpoints .server := by
  change endpoint retired.delivery.updated .server = endpoint reverse.cut.endpoints .server
  simpa only [reverse.actor, Actor.other] using retired.delivery.peer

theorem Retired.payload (retired : Retired reverse) :
    (endpoint retired.cut.endpoints .server).core.received = request.bytes := by
  rw [retired.receiver]
  exact ack.payload

theorem Retired.runtime (retired : Retired reverse) :
    (endpoint retired.cut.endpoints .client).core.sent = [] ∧
      ∃ recovery, (endpoint retired.cut.endpoints .client).recovery = some recovery ∧
        recovery.outstanding = [] ∧ recovery.deadline = none ∧ recovery.timeoutCount = 0 := by
  rw [retired.sender]
  exact ⟨retired.delivery.sentEmpty, retired.delivery.nextRecovery, retired.delivery.runtime,
    retired.delivery.outstanding, retired.delivery.deadline, retired.delivery.timeoutCount⟩

variable {retired : Retired reverse}

private theorem application_passed (before : State input) (actor : Actor) (event : T.Event)
    (effect : Effect input) (computed : applyApplication input before actor event = .ok effect) :
    effect.passed = true := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

structure Read (retired : Retired reverse) where
  actual : Step input
  beforeEq : actual.before = retired.cut.report.final
  event : actual.event = .read .server request.bytes.length
  supported : actual.result.supported = true
  passed : actual.result.passed = true
  localStep : T.Step
  application : actual.result.application = some (.server, localStep)
  localEvent : localStep.event = .read request.bytes.length
  read : actual.result.read = request.bytes
  localRead : localStep.result.read = request.bytes
  next : LocalAppend retired.cut actual .server localStep


def Read.cut (read : Read retired) : Cut input complete := read.next.next

theorem read_application (retired : Retired reverse) : Nonempty (Read retired) := by
  have earlier := (CampusTCPChronology.Report.application_before retired.cut.report complete
    retired.cut.endpoints retired.cut.connection).2
  have fits : request.bytes.length ≤ (endpoint retired.cut.endpoints .server).core.received.length := by
    rw [retired.payload]
    exact Nat.le_refl _
  obtain ⟨effect, computed, supported, _, read, application⟩ := CampusTCPEnabled.read_enabled
    retired.cut.report.final complete retired.cut.endpoints retired.cut.connection .server request.bytes.length earlier fits
  let actual : Step input := ⟨_, _, effect, computed⟩
  let localStep := ApplicationTrace.Step.make (endpoint retired.cut.endpoints .server)
    (endpoint_valid retired.cut.endpoints .server) (.read request.bytes.length) retired.cut.report.final.time
  have app : actual.result.application = some (.server, localStep) := application
  obtain ⟨next⟩ := retired.cut.appendLocal actual rfl supported .server (.read request.bytes.length)
    (.read request.bytes.length) localStep app
  have passed : actual.result.passed = true := by
    obtain ⟨core, custody, accepted, same⟩ := actual.processed
    have applied : applyApplication input retired.cut.report.final .server (.read request.bytes.length) = .ok core := accepted
    simpa only [same] using application_passed retired.cut.report.final .server (.read request.bytes.length) core applied
  have readBytes : actual.result.read = request.bytes := by
    simpa only [retired.payload, List.take_length] using read
  have localRead : localStep.result.read = request.bytes := by
    change (Endpoint.read (endpoint retired.cut.endpoints .server) request.bytes.length).read = _
    rw [Endpoint.read_of_fits _ _ (endpoint_valid retired.cut.endpoints .server) fits]
    simp only [retired.payload, List.take_length]
  exact ⟨⟨actual, rfl, rfl, supported, passed, localStep, app, rfl, readBytes, localRead, next⟩⟩

theorem Read.retirement (read : Read retired) :
    (endpoint read.cut.endpoints .client).core.sent = [] ∧
      ∃ recovery, (endpoint read.cut.endpoints .client).recovery = some recovery ∧
        recovery.outstanding = [] ∧ recovery.deadline = none ∧ recovery.timeoutCount = 0 := by
  have peer := read.next.peer
  change endpoint read.cut.endpoints .client = endpoint retired.cut.endpoints .client at peer
  rw [peer]
  exact retired.runtime

theorem Read.receiver_empty (read : Read retired) :
    (endpoint read.cut.endpoints .server).core.received = [] := by
  have fits : request.bytes.length ≤ (endpoint retired.cut.endpoints .server).core.received.length := by
    rw [retired.payload]
    exact Nat.le_refl _
  have localState := congrArg Endpoint.Result.state read.localStep.computed
  rw [read.next.localBefore, read.localEvent] at localState
  simp only [ApplicationTrace.evaluate, Endpoint.read_of_fits _ _ (endpoint_valid _ _) fits] at localState
  change (endpoint read.next.next.endpoints .server).core.received = []
  rw [read.next.selected, localState]
  change ((endpoint retired.cut.endpoints .server).core.received.drop request.bytes.length) = []
  rw [retired.payload, List.drop_length]

structure CompleteRound (initial : Initial report complete request) (native : NativeEnv initial) where
  sent : Sent initial.start
  assigned : Assigned initial native sent
  dataServed : DataServed assigned
  released : Released dataServed
  acked : Acked released
  ackAssigned : AckAssigned acked
  ackServed : AckServed ackAssigned
  retired : Retired ackServed
  read : Read retired

def CompleteRound.cut (round : CompleteRound initial native) : Cut input complete := round.read.cut

theorem execute (initial : Initial report complete request) (native : NativeEnv initial) :
    Nonempty (CompleteRound initial native) := by
  obtain ⟨sent⟩ := CampusTCPRound.send initial.start request.nonempty request.mssFits request.receiveFits
  obtain ⟨assigned⟩ := CampusTCPRound.assign initial native sent
  obtain ⟨dataServed⟩ := CampusTCPRound.serve_data assigned
  obtain ⟨released⟩ := CampusTCPRound.release_data dataServed
  obtain ⟨acked⟩ := CampusTCPRound.emit_ack released
  obtain ⟨ackAssigned⟩ := assign_ack acked
  obtain ⟨ackServed⟩ := serve_ack ackAssigned
  obtain ⟨retired⟩ := deliver_ack ackServed
  obtain ⟨read⟩ := read_application retired
  exact ⟨⟨sent, assigned, dataServed, released, acked, ackAssigned, ackServed, retired, read⟩⟩

theorem CompleteRound.read_bytes (round : CompleteRound initial native) : round.read.actual.result.read = request.bytes :=
  round.read.read

theorem CompleteRound.retirement (round : CompleteRound initial native) :
    (endpoint round.cut.endpoints .client).core.sent = [] ∧
      ∃ recovery, (endpoint round.cut.endpoints .client).recovery = some recovery ∧
        recovery.outstanding = [] ∧ recovery.deadline = none ∧ recovery.timeoutCount = 0 :=
  round.read.retirement

theorem CompleteRound.receiver_empty (round : CompleteRound initial native) :
    (endpoint round.cut.endpoints .server).core.received = [] := round.read.receiver_empty

theorem CompleteRound.steps (round : CompleteRound initial native) :
    round.cut.report.steps = initial.start.next.report.steps ++
      [round.sent.actual, round.assigned.actual, round.dataServed.actual, round.released.delivery.step,
        round.acked.actual, round.ackAssigned.actual, round.ackServed.actual, round.retired.delivery.step,
        round.read.actual] := by
  change round.read.next.next.report.steps = _
  rw [round.read.next.history]
  simp only [Retired.cut, AckServed.cut, AckAssigned.cut, Acked.cut, Released.cut,
    DataServed.cut, Assigned.cut, Cut.appendNetwork, CampusTCPRoundDelivery.Delivery.append,
    CampusTCPSchedule.Report.appendStep]
  have retained := congrArg (fun steps => steps ++
    [round.assigned.actual, round.dataServed.actual, round.released.delivery.step,
      round.acked.actual, round.ackAssigned.actual, round.ackServed.actual, round.retired.delivery.step,
      round.read.actual]) round.sent.history
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using retained

theorem CompleteRound.length (round : CompleteRound initial native) :
    round.cut.report.steps.length = initial.start.next.report.steps.length + 9 := by
  rw [round.steps]
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem CompleteRound.write_retained (round : CompleteRound initial native) :
    initial.start.writeStep ∈ round.cut.report.steps := by
  rw [round.steps]
  exact List.mem_append_left _ initial.start.writeMember

private def connectionSteps (actor : Actor) : Connection active passive → List T.Step
  | .startup .. => []
  | .application _ endpoints => applicationSteps endpoints actor

private theorem local_histories (actual : Step input) (complete : H.Completed input.active input.passive)
    (before after : Applications complete)
    (connectedBefore : actual.before.connection = .application complete before)
    (connectedAfter : actual.result.state.connection = .application complete after)
    (actor : Actor) (event : T.Event) (action : LocalAction actor actual.event event)
    (localStep : T.Step) (recorded : actual.result.application = some (actor, localStep)) :
    applicationSteps after actor = applicationSteps before actor ++ [localStep] ∧
      applicationSteps after actor.other = applicationSteps before actor.other := by
  obtain ⟨updated, connected, _, _, selected, peer, _, _, _⟩ :=
    CampusTCPEnabled.Step.application_frame actual complete before connectedBefore actor event action localStep recorded
  have histories (receiver : Actor) : applicationSteps updated receiver = applicationSteps after receiver :=
    congrArg (connectionSteps receiver) (connected.symm.trans connectedAfter)
  exact ⟨(histories actor).symm.trans selected, (histories actor.other).symm.trans peer⟩

theorem CompleteRound.server_history (round : CompleteRound initial native) :
    applicationSteps round.cut.endpoints .server = applicationSteps initial.start.next.endpoints .server ++
      [round.released.delivery.localStep, round.acked.facts.localStep, round.read.localStep] := by
  have sentConnection : round.sent.actual.result.state.connection = .application complete round.sent.cut.endpoints := by
    rw [← round.sent.final]
    exact round.sent.cut.connection
  have sentHistories := local_histories round.sent.actual complete initial.start.next.endpoints round.sent.cut.endpoints
    (round.sent.before ▸ initial.start.next.connection) sentConnection .client (.send request.bytes.length true)
    (round.sent.event ▸ LocalAction.send request.bytes.length true) round.sent.localStep round.sent.application
  have sentServer : applicationSteps round.sent.cut.endpoints .server = applicationSteps initial.start.next.endpoints .server :=
    sentHistories.2
  have releasedHistory : applicationSteps round.released.cut.endpoints .server =
      applicationSteps initial.start.next.endpoints .server ++ [round.released.delivery.localStep] := by
    have selected := round.released.delivery.selectedSteps
    simp only [round.dataServed.actor, Actor.other] at selected
    change applicationSteps round.released.cut.endpoints .server =
      applicationSteps round.sent.cut.endpoints .server ++ [round.released.delivery.localStep] at selected
    exact selected.trans (congrArg (fun steps => steps ++ [round.released.delivery.localStep]) sentServer)
  have ackHistory : applicationSteps round.acked.cut.endpoints .server =
      applicationSteps initial.start.next.endpoints .server ++
        [round.released.delivery.localStep, round.acked.facts.localStep] := by
    have selected := round.acked.facts.selectedSteps
    have combined := selected.trans (congrArg (fun steps => steps ++ [round.acked.facts.localStep]) releasedHistory)
    change applicationSteps round.acked.facts.after .server = _
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using combined
  have retiredHistory : applicationSteps round.retired.cut.endpoints .server =
      applicationSteps initial.start.next.endpoints .server ++
        [round.released.delivery.localStep, round.acked.facts.localStep] := by
    have peer := round.retired.delivery.peerSteps
    simp only [round.ackServed.actor, Actor.other] at peer
    change applicationSteps round.retired.cut.endpoints .server =
      applicationSteps round.acked.cut.endpoints .server at peer
    exact peer.trans ackHistory
  have readConnection : round.read.actual.result.state.connection = .application complete round.cut.endpoints := by
    rw [← round.read.next.final]
    exact round.cut.connection
  have readHistories := local_histories round.read.actual complete round.retired.cut.endpoints round.cut.endpoints
    (round.read.beforeEq ▸ round.retired.cut.connection) readConnection .server (.read request.bytes.length)
    (round.read.event ▸ LocalAction.read request.bytes.length) round.read.localStep round.read.application
  have combined := readHistories.1.trans (congrArg (fun steps => steps ++ [round.read.localStep]) retiredHistory)
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using combined

private theorem beforeTransport_released (cursor : Cursor seed) (ready : cursor.beforeTransport = true) :
    cursor.steps.flatMap Protocol.TCP.ApplicationTrace.Step.releasedPayload = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro operation member
  have noReceive := cursor.beforeTransport_no_receive ready operation member
  cases event : operation.event with
  | receive packet => exact False.elim (noReceive packet event)
  | write bytes | send count policy | read count | emitAck policy | enableRecovery | advanceClock millis
  | timeout policy | enableAck | dispatchAck policy =>
    simp only [ApplicationTrace.Step.releasedPayload, ApplicationTrace.releasedPayload, event]

theorem CompleteRound.data_release (round : CompleteRound initial native) :
    round.released.delivery.localStep.releasedPayload = request.bytes := by
  have received := round.released.delivery.received
  simp only [round.dataServed.actor, Actor.other] at received
  simp only [ApplicationTrace.Step.releasedPayload, ApplicationTrace.releasedPayload,
    round.released.delivery.localEvent, round.released.delivery.resultState,
    round.released.delivery.localBefore, round.dataServed.actor, Actor.other, received, List.drop_left]
  exact round.dataServed.emitted_payload

theorem CompleteRound.server_released (round : CompleteRound initial native) :
    (applicationSteps round.cut.endpoints .server).flatMap Protocol.TCP.ApplicationTrace.Step.releasedPayload = request.bytes := by
  have old := beforeTransport_released initial.start.next.endpoints.server initial.start.next.serverBefore
  change (applicationSteps initial.start.next.endpoints .server).flatMap
    Protocol.TCP.ApplicationTrace.Step.releasedPayload = [] at old
  have ackReleased : round.acked.facts.localStep.releasedPayload = [] := by
    simp only [ApplicationTrace.Step.releasedPayload, ApplicationTrace.releasedPayload, round.acked.facts.localEvent]
  have readReleased : round.read.localStep.releasedPayload = [] := by
    simp only [ApplicationTrace.Step.releasedPayload, ApplicationTrace.releasedPayload, round.read.localEvent]
  have released := congrArg (List.flatMap Protocol.TCP.ApplicationTrace.Step.releasedPayload) round.server_history
  simpa only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, old, round.data_release,
    ackReleased, readReleased, List.nil_append, List.append_nil] using released

theorem CompleteRound.server_read (round : CompleteRound initial native) :
    (applicationSteps round.cut.endpoints .server).flatMap Protocol.TCP.ApplicationTrace.Step.readBytes = request.bytes := by
  have balance := round.cut.endpoints.server.chain.received
  have empty := complete.certificate.empty.2.2.2.2.2
  change complete.certificate.passiveSeed.core.received ++
    (applicationSteps round.cut.endpoints .server).flatMap Protocol.TCP.ApplicationTrace.Step.releasedPayload =
      (applicationSteps round.cut.endpoints .server).flatMap Protocol.TCP.ApplicationTrace.Step.readBytes ++
        (endpoint round.cut.endpoints .server).core.received at balance
  rw [empty, round.server_released, round.receiver_empty] at balance
  simpa only [List.nil_append, List.append_nil] using balance.symm

theorem CompleteRound.only_server_receive (round : CompleteRound initial native)
    (operation : T.Step) (member : operation ∈ applicationSteps round.cut.endpoints .server)
    (packet : EstablishedReceive.Input) (received : operation.event = .receive packet) :
    operation = round.released.delivery.localStep := by
  have history := round.server_history
  rw [history] at member
  rcases List.mem_append.mp member with old | current
  · exact False.elim (initial.start.next.endpoints.server.beforeTransport_no_receive
      initial.start.next.serverBefore operation old packet received)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at current
    rcases current with same | same | same
    · exact same
    · rw [same, round.acked.facts.localEvent] at received
      cases received
    · rw [same, round.read.localEvent] at received
      cases received

theorem CompleteRound.only_nonempty_read (round : CompleteRound initial native)
    (operation : T.Step) (member : operation ∈ applicationSteps round.cut.endpoints .server)
    (nonempty : operation.readBytes ≠ []) : operation = round.read.localStep := by
  let prior := applicationSteps initial.start.next.endpoints .server ++
    [round.released.delivery.localStep, round.acked.facts.localStep]
  have history : applicationSteps round.cut.endpoints .server = prior ++ [round.read.localStep] := by
    simpa only [prior, List.append_assoc, List.cons_append, List.nil_append] using round.server_history
  have allReads := congrArg (List.flatMap Protocol.TCP.ApplicationTrace.Step.readBytes) history
  have lastRead : round.read.localStep.readBytes = request.bytes := round.read.localRead
  have split : request.bytes = prior.flatMap Protocol.TCP.ApplicationTrace.Step.readBytes ++ request.bytes := by
    simpa only [round.server_read, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      lastRead, List.append_nil] using allReads
  have lengths := congrArg List.length split
  simp only [List.length_append] at lengths
  have empty : prior.flatMap Protocol.TCP.ApplicationTrace.Step.readBytes = [] :=
    List.length_eq_zero_iff.mp (by omega)
  rw [history] at member
  rcases List.mem_append.mp member with old | last
  · exact False.elim (nonempty ((List.flatMap_eq_nil_iff.mp empty) operation old))
  · exact List.mem_singleton.mp last

end Netlib.Check.CampusTCPRoundReverse
