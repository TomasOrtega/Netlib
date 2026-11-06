import Netlib.Check.CampusTCPRoundPhaseBase
import Netlib.Check.CampusTCPRoundMonitorFacts

/-!
# Reverse phases at the current checked cut

Clock slots can precede each selected action.
The action uses the current report and retains the actual packet records.
-/

namespace Netlib.Check.CampusTCPRoundPhaseReverse

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRoundPhaseBase CampusTCPRoundGuards
open CampusTCPRound (Cut)

namespace F
export CampusTCPRoundMonitorFacts
  (observe_action observeAssignment_eq observeService_eq observeReceipt_eq advanceRead_eq output_pending service_pending)
end F
namespace M
export CampusTCPRoundMonitor (Monitor nextAction advance observeAssignment observeService observeReceipt ticketAction linkAction)
end M

variable {input : Input} {events : List Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}
variable {initial : Initial report complete request} {native : NativeEnv initial}
variable {sent : Sent initial native} {assigned : Assigned sent} {service : DataServed assigned}
variable {released : Released service}

private def network_move (current : Cut input complete) (actual : Step input)
    (before : actual.before = current.report.final) (supported : actual.result.supported = true)
    (passed : actual.result.passed = true) (network : CampusTCPRoundClock.NetworkAction actual.event) : Move current actual :=
  ⟨current.appendNetwork actual before supported network, before, supported, passed, rfl, rfl⟩

theorem assign_ack_at (ack : Acked released) (current : Cut input complete) (placement : At ack.hop.post current) :
    ∃ next : AckAssigned ack, next.hop.before = current := by
  have environment := ack.anchor.environment.trans placement.frame.environment.symm
  have guards := Frame.guards placement.frame ack.anchor.guards
  have source : current.report.final.outputs[ack.index]? = some ack.facts.produced := by
    rw [placement.frame.outputs]
    exact ack.source
  have pending : IngressPending current.report.final ack.index := by
    simpa only [IngressPending, placement.frame.custody, Acked.index] using ack.pending
  obtain ⟨actual, facts⟩ := CampusTCPRoundAssignment.Report.assign_enabled current.report ack.index native.ackIngress
    ack.facts.produced source (native.route_at current.report.final environment ack.facts.produced.actor) pending
  let ticket := CampusTCPRoundAssignment.ticket current.report.final ack.index native.ackIngress ack.facts.produced
  let move := network_move current actual facts.beforeEq facts.supported facts.passed (by
    rw [facts.event]
    exact .assign _ _)
  let hop : Hop ack.hop.post (ack.hop.monitor (config initial native)) := ⟨current, placement, actual, move⟩
  have nextAt : M.nextAction (config initial native) actual.before (ack.hop.monitor (config initial native)) =
      some (.assign ack.index native.ackIngress) := by
    rw [facts.beforeEq, Frame.nextAction placement.frame]
    exact ack.anchor.next
  have findNew : actual.result.state.work.pending.find? (fun item => item.id == actual.before.work.nextID) = some ticket :=
    CampusTCPRoundMonitorFacts.AssignmentFacts.find_new facts
  have observed : hop.monitor (config initial native) =
      { phase := .ackTicket, refs := { (ack.hop.monitor (config initial native)).refs with ackTicket := some ticket.id } } := by
    change CampusTCPRoundMonitor.observe _ _ actual = _
    rw [F.observe_action _ _ actual (.assign ack.index native.ackIngress) facts.supported facts.passed nextAt facts.event,
      M.advance, ack.anchor.phaseEq]
    exact F.observeAssignment_eq _ actual .server .ackTicket ticket findNew
  have findTicket : actual.result.state.work.pending.find? (fun item => item.id == ticket.id) = some ticket := by
    simpa only [ticket, CampusTCPRoundAssignment.ticket_id, facts.beforeEq] using findNew
  have gateway : beforeService input hop.post.report.final .primary = beforeService input service.hop.post.report.final .primary := by
    change beforeService input actual.result.state .primary = _
    rw [CampusTCPRoundLocal.step_service_nonservice actual (by rw [facts.event]; trivial), facts.beforeEq,
      placement.frame.beforeService]
    exact ack.gateway
  have afterEnvironment : CampusTCPRoundEnvironment.environment initial.state =
      CampusTCPRoundEnvironment.environment hop.post.report.final := by
    change _ = CampusTCPRoundEnvironment.environment actual.result.state
    exact environment.trans (by simpa only [facts.beforeEq] using
      CampusTCPRoundEnvironment.Step.environment actual (by rw [facts.event]; trivial))
  refine ⟨{
    hop, facts, ticket, ticketEq := rfl, sender := ?_, payload := ?_, gateway,
    pending := facts.pending, anchor := ⟨?_, ?_, guards,
      ack.anchor.retained.trans (placement.retained.trans move.retained), afterEnvironment⟩ }, rfl⟩
  · exact (placement.frame.endpointEq .client).trans ack.sender
  · change (endpoint current.endpoints .server).core.received = _
    rw [placement.frame.endpointEq .server]
    exact ack.payload
  · rw [observed]
  · change M.nextAction _ actual.result.state (hop.monitor _) = _
    simp only [observed, M.nextAction, M.ticketAction, findTicket, bind, Option.bind, pure]

variable {ack : Acked released}

private theorem assignment_primary (assignment : AckAssigned ack) : assignment.ticket.value.gateway = .primary := by
  rw [assignment.ticketEq]
  exact native.owner_at assignment.hop.before.report.final
    (ack.anchor.environment.trans assignment.hop.placement.frame.environment.symm) ack.facts.produced.actor

private theorem assignment_actor (assignment : AckAssigned ack) : assignment.ticket.value.produced.actor = .server := by
  rw [assignment.ticketEq]
  change ack.facts.produced.actor = .server
  rw [ack.facts.production]
  rfl

theorem serve_ack_at (assignment : AckAssigned ack) (current : Cut input complete) (placement : At assignment.hop.post current) :
    ∃ next : AckServed assignment, next.hop.before = current := by
  have environment := assignment.anchor.environment.trans placement.frame.environment.symm
  have guards := Frame.guards placement.frame assignment.anchor.guards
  have pending : assignment.ticket ∈ current.report.final.work.pending := by
    rw [placement.frame.work]
    exact assignment.pending
  have gateway : beforeService input current.report.final .primary = beforeService input service.hop.post.report.final .primary :=
    (placement.frame.beforeService .primary).trans assignment.gateway
  have phase : (beforeService input current.report.final .primary).admission.phase = .data service.session := by
    rw [gateway]
    exact service.phase
  have valid : (beforeService input current.report.final .primary).tracker.Valid := by rw [gateway]; exact service.trackerValid
  have records : (beforeService input current.report.final .primary).tracker.records = [⟨initial.entry, true⟩] := by
    rw [gateway]
    exact service.records
  have fields : AckFields (complete := complete) (request := request) assignment.ticket.value.produced := by
    rw [assignment.ticketEq]
    exact ack.fields
  have ready : CampusTCPService.ExistingDataReady (input.contextFor assignment.ticket.value.gateway)
      (beforeService input current.report.final assignment.ticket.value.gateway) assignment.ticket.value.source input.zone
      assignment.ticket.value.ingress ⟨initial.entry.flow, .reply⟩ service.session assignment.ticket.value.produced.actor.nextHop := by
    have ingress : assignment.ticket.value.ingress = native.ackIngress := by rw [assignment.ticketEq]; rfl
    rw [assignment_primary assignment, assignment_actor assignment, ingress]
    apply CampusTCPRoundGateway.reply_ready input complete initial.aligned service.geometry native.reply
      (beforeService input current.report.final .primary) (initial.service_environment current.report.final environment)
      assignment.ticket.value.source fields.header valid records phase fields.sequence
    · simpa only [Ticket.source, service.sourceFields.payload] using fields.acknowledgment
    · exact fields.profile
    · exact fields.payload
    · exact fields.ttl
  have servicePhase : CampusTCPGatewayEnabled.ServicePhaseReady current.report.final assignment.ticket.value.gateway := by
    rw [assignment_primary assignment]
    exact native.service_phase_at current.report.final environment
  obtain ⟨actual, served, emission, emitted, facts⟩ := CampusTCPRoundService.Report.serve_enabled current.report
    assignment.ticket pending servicePhase ⟨initial.entry.flow, .reply⟩ service.session ready
  let move := network_move current actual facts.beforeEq facts.supported facts.passed (by rw [facts.event]; exact .serve _ _)
  let hop : Hop assignment.hop.post (assignment.hop.monitor (config initial native)) := ⟨current, placement, actual, move⟩
  have nextAt : M.nextAction (config initial native) actual.before (assignment.hop.monitor (config initial native)) =
      some (.serve assignment.ticket.id) := by
    rw [facts.beforeEq, Frame.nextAction placement.frame]
    exact assignment.anchor.next
  obtain ⟨id, pendingID⟩ := F.service_pending actual served facts.recorded emission emitted
  have observed : hop.monitor (config initial native) =
      { phase := .ackLink, refs := { (assignment.hop.monitor (config initial native)).refs with
        ackService := some actual.before.services.length, ackLinkPacket := some id } } := by
    change CampusTCPRoundMonitor.observe _ _ actual = _
    rw [F.observe_action _ _ actual (.serve assignment.ticket.id) facts.supported facts.passed nextAt facts.event,
      M.advance, assignment.anchor.phaseEq]
    exact F.observeService_eq _ actual .server .ackLink served facts.recorded emission emitted pendingID
  have stored : actual.result.state.services[actual.before.services.length]? = some served := by
    simpa only [facts.beforeEq] using facts.serviceIndex
  have afterPending : CampusTCPDeliveryEnabled.LinkPending actual.result.state actual.before.services.length := by
    obtain ⟨packet, member, _, payload, _⟩ := facts.link
    exact ⟨packet, member, by simp only [payload, facts.beforeEq, Transit.linkAt, beq_self_eq_true]⟩
  have sourceFields : AckFields (complete := complete) (request := request) served.ticket.value.produced := by
    rw [facts.ticket]
    exact fields
  refine ⟨{
    hop, served, emission, emitted, facts, sourceFields,
    sender := (placement.frame.endpointEq .client).trans assignment.sender,
    payload := ?_, stored, pending := afterPending,
    anchor := ⟨?_, ?_, guards, assignment.anchor.retained.trans (placement.retained.trans move.retained), ?_⟩ }, rfl⟩
  · change (endpoint current.endpoints .server).core.received = _
    rw [placement.frame.endpointEq .server]
    exact assignment.payload
  · rw [observed]
  · change M.nextAction _ actual.result.state (hop.monitor _) = _
    simp only [observed, M.nextAction, M.linkAction, stored, emitted, pendingID,
      bind, Option.bind, beq_self_eq_true, ite_true, pure]
    rfl
  · exact environment.trans facts.environment

variable {assignment : AckAssigned ack}

private theorem served_actor (reverse : AckServed assignment) : reverse.served.ticket.value.produced.actor = .server := by
  rw [reverse.facts.ticket]
  exact assignment_actor assignment

theorem deliver_ack_at (reverse : AckServed assignment) (current : Cut input complete) (placement : At reverse.hop.post current) :
    ∃ next : Retired reverse, next.hop.before = current := by
  have environment := reverse.anchor.environment.trans placement.frame.environment.symm
  have guards := Frame.guards placement.frame reverse.anchor.guards
  have source : current.report.final.services[reverse.index]? = some reverse.served := by
    rw [placement.frame.services]
    exact reverse.stored
  have pending : CampusTCPDeliveryEnabled.LinkPending current.report.final reverse.index := by
    simpa only [CampusTCPDeliveryEnabled.LinkPending, placement.frame.custody, AckServed.index] using reverse.pending
  have application : CampusTCPDeliveryEnabled.ApplicationSource reverse.served.ticket.value.produced := by
    rw [reverse.facts.ticket, assignment.ticketEq]
    change CampusTCPDeliveryEnabled.ApplicationSource ack.facts.produced
    rw [ack.facts.production]
    trivial
  have sender : endpoint current.endpoints .client =
      Endpoint.sendState (endpoint initial.start.next.endpoints .client) request.bytes.length :=
    (placement.frame.endpointEq .client).trans reverse.sender
  obtain ⟨recovery, reaction, ready⟩ := CampusTCPRoundEmission.ack_ready initial reverse.emission reverse.facts.target
    reverse.sourceFields.sequence reverse.sourceFields.acknowledgment reverse.sourceFields.payload reverse.sourceFields.profile
  have selectedReady : CampusTCPDeliveryEnabled.FullAckReady
      (endpoint current.endpoints reverse.served.ticket.value.produced.actor.other) reverse.emission.asInput recovery reaction := by
    rw [served_actor reverse]
    change CampusTCPDeliveryEnabled.FullAckReady (endpoint current.endpoints .client) _ _ _
    rw [sender]
    exact ready
  obtain ⟨delivery⟩ := CampusTCPRoundDelivery.Report.deliver_full_ack current.report complete current.endpoints current.connection
    reverse.index reverse.served source reverse.emission reverse.emitted application pending recovery reaction selectedReady
  let after : Cut input complete := ⟨_, delivery.toDelivery.append current.supported current.finished,
    delivery.toDelivery.append_supported _ _, rfl, delivery.updated, delivery.connection⟩
  let move : Move current delivery.step :=
    ⟨after, delivery.beforeEq, delivery.supported, delivery.passed, rfl, rfl⟩
  let hop : Hop reverse.hop.post (reverse.hop.monitor (config initial native)) := ⟨current, placement, delivery.step, move⟩
  have nextAt : M.nextAction (config initial native) delivery.step.before (reverse.hop.monitor (config initial native)) =
      some (.deliver reverse.index reverse.emission.bytes true) := by
    rw [delivery.beforeEq, Frame.nextAction placement.frame]
    exact reverse.anchor.next
  have receiptActor : delivery.receipt.actor = .client := by
    have receiver := delivery.receipt.receiver
    rw [delivery.receiptService, served_actor reverse] at receiver
    exact receiver
  have recorded : delivery.step.result.application = some (.client, delivery.localStep) := by
    simpa only [served_actor reverse, Actor.other] using delivery.recorded
  have observed : hop.monitor (config initial native) =
      { phase := .needRead, refs := { (reverse.hop.monitor (config initial native)).refs with
        ackReceipt := some delivery.step.before.receipts.length, ackReceiveStamp := some delivery.localStep.stamp } } := by
    change CampusTCPRoundMonitor.observe _ _ delivery.step = _
    rw [F.observe_action _ _ delivery.step (.deliver reverse.index reverse.emission.bytes true)
      delivery.supported delivery.passed nextAt delivery.event, M.advance, reverse.anchor.phaseEq]
    exact F.observeReceipt_eq _ delivery.step .client .needRead delivery.receipt delivery.receiptAt receiptActor
      delivery.localStep recorded
  have senderAfter : endpoint hop.post.endpoints .client = delivery.after := by
    change endpoint delivery.updated .client = _
    simpa only [served_actor reverse, Actor.other] using delivery.selected
  have peer : endpoint delivery.updated .server = endpoint current.endpoints .server := by
    simpa only [served_actor reverse, Actor.other] using delivery.peer
  refine ⟨{
    hop, delivery, actual := rfl, sender := senderAfter, payload := ?_,
    anchor := ⟨?_, ?_, CampusTCPRoundGuards.AckDelivered.guards delivery guards,
      reverse.anchor.retained.trans (placement.retained.trans move.retained), environment.trans delivery.environment⟩ }, rfl⟩
  · change (endpoint delivery.updated .server).core.received = _
    rw [peer, placement.frame.endpointEq .server]
    exact reverse.payload
  · rw [observed]
  · rw [observed]
    rfl

variable {reverse : AckServed assignment}

theorem read_at (retired : Retired reverse) (current : Cut input complete) (placement : At retired.hop.post current) :
    ∃ next : Read retired, next.hop.before = current := by
  have environment := retired.anchor.environment.trans placement.frame.environment.symm
  have guards := Frame.guards placement.frame retired.anchor.guards
  have payload : (endpoint current.endpoints .server).core.received = request.bytes := by
    rw [placement.frame.endpointEq .server]
    exact retired.payload
  have fits : request.bytes.length ≤ (endpoint current.endpoints .server).core.received.length := by
    rw [payload]
    exact Nat.le_refl _
  have earlier := (CampusTCPChronology.Report.application_before current.report complete current.endpoints current.connection).2
  obtain ⟨effect, computed, supported, _, returned, application⟩ := CampusTCPEnabled.read_enabled current.report.final
    complete current.endpoints current.connection .server request.bytes.length earlier fits
  let actual : Step input := ⟨_, _, effect, computed⟩
  let operation := ApplicationTrace.Step.make (endpoint current.endpoints .server) (endpoint_valid current.endpoints .server)
    (.read request.bytes.length) current.report.final.time
  have recorded : actual.result.application = some (.server, operation) := application
  obtain ⟨appended⟩ := current.appendLocal actual rfl supported .server (.read request.bytes.length)
    (.read request.bytes.length) operation recorded
  have passed : actual.result.passed = true := CampusTCPRoundLocal.step_local_passed actual .server _ (.read _)
  let move : Move current actual := ⟨appended.next, rfl, supported, passed, appended.history, appended.final⟩
  let hop : Hop retired.hop.post (retired.hop.monitor (config initial native)) := ⟨current, placement, actual, move⟩
  have read : actual.result.read = request.bytes := by simpa only [payload, List.take_length] using returned
  have localRead : operation.result.read = request.bytes := by
    change (Endpoint.read (endpoint current.endpoints .server) request.bytes.length).read = _
    rw [Endpoint.read_of_fits _ _ (endpoint_valid _ _) fits]
    simp only [payload, List.take_length]
  have nextAt : M.nextAction (config initial native) actual.before (retired.hop.monitor (config initial native)) =
      some (.read .server request.bytes.length) := by
    change M.nextAction _ current.report.final _ = _
    rw [Frame.nextAction placement.frame]
    exact retired.anchor.next
  have observed : hop.monitor (config initial native) =
      { phase := .done, refs := { (retired.hop.monitor (config initial native)).refs with
        readStamp := some operation.stamp, readBytes := request.bytes } } := by
    change CampusTCPRoundMonitor.observe _ _ actual = _
    rw [F.observe_action _ _ actual (.read .server request.bytes.length) supported passed nextAt rfl]
    exact F.advanceRead_eq _ _ retired.anchor.phaseEq actual operation recorded read
  have afterGuards : Guards hop.post.endpoints :=
    guards_frame current.endpoints appended.next.endpoints .server
      (CampusTCPRoundGuards.read_step_guarded operation request.bytes.length rfl fits (guards .server))
      appended.selected appended.peer guards
  have afterEnvironment : CampusTCPRoundEnvironment.environment initial.state =
      CampusTCPRoundEnvironment.environment hop.post.report.final := by
    change _ = CampusTCPRoundEnvironment.environment move.after.report.final
    rw [move.final]
    exact environment.trans (CampusTCPRoundEnvironment.Step.environment actual trivial)
  have sender : endpoint hop.post.endpoints .client = retired.delivery.after := by
    change endpoint appended.next.endpoints .client = _
    exact appended.peer.trans ((placement.frame.endpointEq .client).trans retired.sender)
  refine ⟨{
    hop, event := rfl, operation, recorded, localBefore := rfl, localEvent := rfl, localStamp := rfl,
    returned := read, localRead, sender,
    anchor := ⟨?_, ?_, afterGuards,
      retired.anchor.retained.trans (placement.retained.trans move.retained), afterEnvironment⟩ }, rfl⟩
  · rw [observed]
  · simp only [observed, M.nextAction]

end Netlib.Check.CampusTCPRoundPhaseReverse
