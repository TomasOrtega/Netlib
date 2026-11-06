import Netlib.Check.CampusTCPGatewayEnabled
import Netlib.Check.CampusTCPRoundGateway

/-!
# Actual gateway service in one TCP round

The selected pending ticket supplies the current source and gateway.
The checked service retains its preparation, output, and new link identity.
-/

namespace Netlib.Check.CampusTCPRoundService

open CampusTCPModel
open Protocol

namespace O
export Theory.Outstanding (Item Completed complete)
end O

@[simp] private theorem write_connection (before : State input) (gateway : Gateway) (resident : Local) :
    (before.write gateway resident).connection = before.connection := by cases gateway <;> rfl
@[simp] private theorem write_outputs (before : State input) (gateway : Gateway) (resident : Local) :
    (before.write gateway resident).outputs = before.outputs := by cases gateway <;> rfl
@[simp] private theorem write_receipts (before : State input) (gateway : Gateway) (resident : Local) :
    (before.write gateway resident).receipts = before.receipts := by cases gateway <;> rfl

private theorem resident_transport (before : State input) (gateway : Gateway) (resident : Local)
    (work : Work.State (Ticket input.active input.passive)) (services : List (Served input))
    (custody : Custody input) (time : Nat) :
    ({ before.write gateway resident with work, services, custody, time }.resident gateway).transport = resident.transport := by
  cases gateway <;> rfl

theorem Step.serve_frame (actual : Step input) (id : Nat)
    (observed : Option (List UInt8 × Option (List UInt8))) (event : actual.event = .serve id observed)
    (served : Served input) (recorded : actual.result.service = some served) :
    ∃ completed : O.Completed actual.before.work id,
      O.complete actual.before.work id = .ok completed ∧ served.ticket = completed.item ∧
      served.before = beforeService input actual.before served.ticket.value.gateway ∧
      actual.result.state.work = completed.state ∧
      (actual.result.state.resident served.ticket.value.gateway).transport =
        ⟨served.evidence.tracker, served.evidence.admission⟩ ∧
      actual.result.state.connection = actual.before.connection ∧
      actual.result.state.outputs = actual.before.outputs ∧ actual.result.state.receipts = actual.before.receipts := by
  obtain ⟨effect, custody, computed, final⟩ := actual.processed
  have service : effect.service = some served := by simpa only [final] using recorded
  rw [event] at computed
  simp only [processCore] at computed
  cases completedAt : O.complete actual.before.work id with
  | error reason => simp [completedAt, Except.mapError, bind, Except.bind] at computed
  | ok completed =>
    simp only [completedAt, Except.mapError, bind, Except.bind] at computed
    repeat' first
      | (solve | cases computed; simp only [CampusTCPModel.unsupported] at service; cases service)
      | (solve
        | simp only [Option.some.injEq] at service
          subst served
          rw [final]
          exact ⟨completed, rfl, rfl, rfl, rfl,
            resident_transport actual.before _ _ _ _ custody _, write_connection _ _ _, write_outputs _ _ _, write_receipts _ _ _⟩)
      | (cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

theorem Processing.attachment (processing : CampusTCPService.Processing context before source zone)
    (ready : CampusTCPService.ExistingDataReady context before source zone ingress hit session hop) :
    processing.prepared.attachment.entry = session.entry ∧
      processing.prepared.attachment.direction = hit.direction ∧ processing.prepared.attachment.fresh = false := by
  obtain ⟨record, prepared, _, member, same, attached, attachment, _⟩ :=
    ConntrackLifecycle.prepare_existing_completes before.tracker (CampusTCPService.packetInput before source zone).lifecycle
      hit ready.tracker.valid ready.tracker.zone ready.tracker.transport ready.tracker.candidate ready.tracker.lookup
  have actual : processing.prepared = prepared := Except.ok.inj (processing.attached.symm.trans attached)
  rw [actual, attachment]
  exact ⟨ready.binding record member same, rfl, rfl⟩

structure ServiceFacts (before : State input) (item : O.Item (Ticket input.active input.passive))
    (hit : FlowNAT.Hit) (session : TCP.Admission.Session) (actual : Step input) (served : Served input)
    (emission : TCP.WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission) : Prop where
  beforeEq : actual.before = before
  event : actual.event = .serve item.id none
  supported : actual.result.supported = true
  passed : actual.result.passed = true
  recorded : actual.result.service = some served
  ticket : served.ticket = item
  current : served.before = beforeService input before item.value.gateway
  target : emission.target = hit.output
  processing : ∃ processing : CampusTCPService.Processing (input.contextFor served.ticket.value.gateway)
      served.before served.ticket.value.source input.zone,
    served.evidence.processing = some processing ∧ processing.outcome.nextHop = some item.value.produced.actor.nextHop ∧
      processing.prepared.attachment.entry = session.entry ∧
      processing.prepared.attachment.direction = hit.direction ∧ processing.prepared.attachment.fresh = false
  completed : ∃ completed : O.Completed actual.before.work item.id,
    O.complete actual.before.work item.id = .ok completed ∧ completed.item = item ∧
      actual.result.state.work = completed.state
  transport : (actual.result.state.resident item.value.gateway).transport =
    ⟨served.evidence.tracker, served.evidence.admission⟩
  connection : actual.result.state.connection = before.connection
  outputs : actual.result.state.outputs = before.outputs
  receipts : actual.result.state.receipts = before.receipts
  environment : CampusTCPRoundEnvironment.environment before = CampusTCPRoundEnvironment.environment actual.result.state
  serviceIndex : actual.result.state.services[before.services.length]? = some served
  link : ∃ packet ∈ actual.result.state.custody.pending, packet.value.parent = none ∧
    packet.value.payload = .link before.services.length served emission emitted ∧ packet.value.payload.bytes = emission.bytes

theorem Report.serve_enabled (report : Report input events) (item : O.Item (Ticket input.active input.passive))
    (member : item ∈ report.final.work.pending)
    (phase : CampusTCPGatewayEnabled.ServicePhaseReady report.final item.value.gateway)
    (hit : FlowNAT.Hit) (session : TCP.Admission.Session)
    (ready : CampusTCPService.ExistingDataReady (input.contextFor item.value.gateway)
      (beforeService input report.final item.value.gateway) item.value.source input.zone item.value.ingress
      hit session item.value.produced.actor.nextHop) :
    ∃ actual : Step input, ∃ served : Served input,
      ∃ emission : TCP.WireForwarding.Emission served.ticket.value.source.packet,
      ∃ emitted : served.evidence.output = some emission, ServiceFacts report.final item hit session actual served emission emitted := by
  obtain ⟨actual, beforeEq, event, supported, passed, served, recorded, ticketEq, _, _, _, _, _, _, _⟩ :=
    CampusTCPGatewayEnabled.Report.serve_enabled report item member phase hit session ready
  obtain ⟨completed, completedAt, selected, current, work, transport, connection, outputs, receipts⟩ :=
    Step.serve_frame actual item.id none event served recorded
  have currentAt : served.before = beforeService input report.final item.value.gateway := by
    simpa only [beforeEq, ticketEq] using current
  have readyAt : CampusTCPService.ExistingDataReady (input.contextFor served.ticket.value.gateway)
      served.before served.ticket.value.source input.zone served.ticket.value.ingress hit session
      served.ticket.value.produced.actor.nextHop := by
    rw [ticketEq, currentAt]
    exact ready
  obtain ⟨evidence, emission, computed, emitted, _, target, _, processing, processingAt, hop⟩ :=
    CampusTCPService.run_existing_enabled (input.contextFor served.ticket.value.gateway) served.before
      served.ticket.value.source input.zone served.ticket.value.ingress hit session
      served.ticket.value.produced.actor.nextHop readyAt
  have evidenceEq : evidence = served.evidence := Except.ok.inj (computed.symm.trans served.computed)
  subst evidence
  have attachment := Processing.attachment processing readyAt
  have environment := CampusTCPRoundEnvironment.Step.environment actual (by rw [event]; trivial)
  have serviceIndex : actual.result.state.services[report.final.services.length]? = some served := by
    rw [CampusTCPOrigins.service_history actual, recorded, beforeEq]
    simp
  obtain ⟨packet, pending, parent, payload, bytes⟩ := CampusTCPCustodyFacts.Step.emission_packet actual served recorded emission emitted
  refine ⟨actual, served, emission, emitted, beforeEq, event, supported, passed, recorded, ticketEq, currentAt,
    target, ?_, ?_, ?_, ?_, ?_, ?_, ?_, serviceIndex, ?_⟩
  · exact ⟨processing, processingAt, by simpa only [ticketEq] using hop, attachment⟩
  · exact ⟨completed, completedAt, selected.symm.trans ticketEq, work⟩
  · simpa only [ticketEq] using transport
  · simpa only [beforeEq] using connection
  · simpa only [beforeEq] using outputs
  · simpa only [beforeEq] using receipts
  · simpa only [beforeEq] using environment
  · exact ⟨packet, pending, parent, by simpa only [beforeEq] using payload, bytes⟩

section

variable {input : Input} {before : State input} {item : O.Item (Ticket input.active input.passive)}
  {hit : FlowNAT.Hit} {session : TCP.Admission.Session} {actual : Step input} {served : Served input}
  {emission : TCP.WireForwarding.Emission served.ticket.value.source.packet}
  {emitted : served.evidence.output = some emission}

theorem ServiceFacts.tracker (facts : ServiceFacts before item hit session actual served emission emitted)
    (processing : CampusTCPService.Processing (input.contextFor served.ticket.value.gateway)
      served.before served.ticket.value.source input.zone)
    (present : served.evidence.processing = some processing) :
    (actual.result.state.resident item.value.gateway).transport.tracker = processing.outcome.state := by
  rw [facts.transport]
  exact (served.evidence.processing_states processing present).1

theorem ServiceFacts.admission (facts : ServiceFacts before item hit session actual served emission emitted)
    (processing : CampusTCPService.Processing (input.contextFor served.ticket.value.gateway)
      served.before served.ticket.value.source input.zone)
    (present : served.evidence.processing = some processing) :
    (actual.result.state.resident item.value.gateway).transport.admission = processing.nextAdmission := by
  rw [facts.transport]
  exact (served.evidence.processing_states processing present).2

end

end Netlib.Check.CampusTCPRoundService
