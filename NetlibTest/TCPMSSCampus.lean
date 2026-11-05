import Netlib.Check.CampusTCP
import Netlib.Protocol.TCP.AdmissionMSSFacts

namespace NetlibTest.TCPMSSCampus

open Netlib Packet Protocol
namespace M
export Check.CampusTCPModel (Input State Step Report Gateway Served)
end M
namespace F
export Check.CampusTCPFacts (At findStep)
end F

private def verify (property : Prop) [Decidable property] (message : String) : Except String { _value : Unit // property } :=
  if accepted : property then .ok ⟨(), accepted⟩ else .error message

structure DataService (report : M.Report input events) (time : Nat) (gateway : M.Gateway)
    (direction : FlowNAT.Direction) (size : Nat) where
  joint : F.At report time
  served : M.Served input
  present : joint.step.result.service = some served
  gatewayEq : served.ticket.value.gateway = gateway
  processing : Check.CampusTCPService.Processing (input.contextFor served.ticket.value.gateway)
    served.before served.ticket.value.source input.zone
  selected : served.evidence.processing = some processing
  session : TCP.Admission.Session
  phase : served.before.admission.phase = .data session
  directionEq : processing.prepared.attachment.direction = direction
  sizeEq : served.ticket.value.source.packet.segment.payload.length = size
  clientOffer : session.clientMSS = TCP.Handshake.receiveOffer input.active
  serverOffer : session.serverMSS = TCP.Handshake.receiveOffer input.passive
  emission : TCP.WireForwarding.Emission served.ticket.value.source.packet
  emitted : served.evidence.output = some emission
  updated : (joint.step.result.state.resident gateway).transport = ⟨processing.outcome.state, processing.nextAdmission⟩

theorem DataService.payload_bound {input : M.Input} {events : List Check.CampusTCPModel.Event}
    {report : M.Report input events} (value : DataService report time gateway direction size) :
    size ≤ (if direction = .original then TCP.Handshake.receiveOffer input.passive
      else TCP.Handshake.receiveOffer input.active).limit := by
  have bound := value.processing.admitted.data_payload_bound value.phase
  change value.served.ticket.value.source.packet.segment.payload.length ≤ _ at bound
  rw [value.directionEq] at bound
  cases direction with
  | original => simpa only [TCP.Admission.Session.peerMSS, value.serverOffer, value.sizeEq, ite_true] using bound
  | reply => simpa only [TCP.Admission.Session.peerMSS, value.clientOffer, value.sizeEq, reduceCtorEq, ite_false] using bound

theorem DataService.preserves_offers {input : M.Input} {events : List Check.CampusTCPModel.Event}
    {report : M.Report input events} (value : DataService report time gateway direction size) :
    ∃ after, (value.joint.step.result.state.resident gateway).transport.admission.phase = .data after ∧
      after.clientMSS = TCP.Handshake.receiveOffer input.active ∧
      after.serverMSS = TCP.Handshake.receiveOffer input.passive := by
  obtain ⟨_, ⟨after, phase, client, server⟩, _⟩ :=
    value.processing.admitted.committed_mss value.phase value.processing.committed
  rw [value.updated]
  exact ⟨after, phase, client.trans value.clientOffer, server.trans value.serverOffer⟩

private def dataService (report : M.Report input events) (time : Nat) (gateway : M.Gateway)
    (direction : FlowNAT.Direction) (size : Nat) : Except String (DataService report time gateway direction size) := do
  let joint ← F.findStep report time
  match present : joint.step.result.service with
  | none => throw "The selected data operation has no actual gateway service."
  | some served =>
    let gatewayEq ← verify (served.ticket.value.gateway = gateway) "The data service used a different gateway."
    match selected : served.evidence.processing with
    | none => throw "The selected data service has no actual transport computation."
    | some processing =>
      match phase : served.before.admission.phase with
      | .data session =>
        let directionEq ← verify (processing.prepared.attachment.direction = direction) "The data direction differs."
        let sizeEq ← verify (served.ticket.value.source.packet.segment.payload.length = size) "The payload size differs."
        let clientOffer ← verify (session.clientMSS = TCP.Handshake.receiveOffer input.active) "The client offer differs from startup."
        let serverOffer ← verify (session.serverMSS = TCP.Handshake.receiveOffer input.passive) "The server offer differs from startup."
        match emitted : served.evidence.output with
        | none => throw "The selected data service emitted no packet."
        | some emission =>
          let updated ← verify ((joint.step.result.state.resident gateway).transport.same
            ⟨processing.outcome.state, processing.nextAdmission⟩ = true) "The service state differs from its actual commit."
          return ⟨joint, served, present, gatewayEq.property, processing, selected, session, phase,
            directionEq.property, sizeEq.property, clientOffer.property, serverOffer.property, emission, emitted,
            (TCP.Checkpoint.Gateway.same_correct _ _).mp updated.property⟩
      | _ => throw "The selected data service has no established gateway history."

def fixturePayload (start count : Nat) : List UInt8 :=
  (List.range count).map (fun index => UInt8.ofNat ((start + index) % 251))

structure Demonstration (input : Check.CampusTCP.Input) where
  report : M.Report input.model input.events
  assurance : Check.CampusTCPTransferFacts.Assurance report
  clientOffer : (TCP.Handshake.receiveOffer input.model.active).limit = 1200
  serverOffer : (TCP.Handshake.receiveOffer input.model.passive).limit = 800
  clientSend : input.model.active.ipSendLimit = 1000
  serverSend : input.model.passive.ipSendLimit = 1500
  primaryClient : DataService report 28 .primary .original 800
  primaryServer : DataService report 33 .primary .reply 1200
  standbyClient : DataService report 55 .standby .original 800
  standbyServer : DataService report 61 .standby .reply 1200
  source : TCP.Admission.Session
  sourcePhase : assurance.installation.checkpoint.snapshot.source.admission.phase = .data source
  sourceClient : source.clientMSS = TCP.Handshake.receiveOffer input.model.active
  sourceServer : source.serverMSS = TCP.Handshake.receiveOffer input.model.passive
  deferred : source.reply.observed = 1201 ∧ source.reply.acknowledged = 0
  acknowledgment : DataService report 50 .standby .original 0
  exactBefore : acknowledgment.joint.step.before.standby.transport = assurance.installation.checkpoint.snapshot.source
  after : TCP.Admission.Session
  afterPhase : acknowledgment.joint.step.result.state.standby.transport.admission.phase = .data after
  removed : after.reply.observed = 1201 ∧ after.reply.acknowledged = 1201 ∧ after.reply.outstanding = 0
  clientRead : assurance.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes = fixturePayload 30 1200 ++ fixturePayload 35 1 ++ fixturePayload 58 1200
  serverRead : assurance.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes = fixturePayload 25 800 ++ fixturePayload 52 800
  denied : F.At report 70
  deniedService : M.Served input.model
  deniedPresent : denied.step.result.service = some deniedService
  unauthorized : (Check.SessionFirewall.stateAt input.model.context.authentication denied.step.before.authentication).auth.authorized = false

theorem Demonstration.seed_limits (value : Demonstration input) :
    value.assurance.application.complete.certificate.activeSeed.effectiveMSS = 800 ∧
      value.assurance.application.complete.certificate.passiveSeed.effectiveMSS = 1200 := by
  have learned := value.assurance.application.complete.certificate.directional_mss
  rw [value.assurance.application.complete.activeConfig, value.assurance.application.complete.passiveConfig] at learned
  simp only [TCP.Handshake.effectiveMSS, TCP.MSS.effective_no_options, value.clientOffer, value.serverOffer,
    value.clientSend, value.serverSend] at learned
  exact ⟨learned.2.2.1.trans (by decide), learned.2.2.2.trans (by decide)⟩

theorem Demonstration.copied_offers (value : Demonstration input) :
    value.assurance.step.result.state.standby.transport.admission.phase = .data value.source ∧
      value.source.clientMSS.limit = 1200 ∧ value.source.serverMSS.limit = 800 := by
  exact ⟨by rw [value.assurance.origin.copied, value.sourcePhase],
    by rw [value.sourceClient, value.clientOffer], by rw [value.sourceServer, value.serverOffer]⟩

theorem Demonstration.nonempty_prefixes (value : Demonstration input) :
    value.assurance.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes <+:
        value.assurance.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.written ∧
      value.assurance.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes <+:
        value.assurance.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.written ∧
      (value.assurance.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes).length = 1600 ∧
      (value.assurance.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes).length = 2401 := by
  have server := congrArg List.length value.serverRead
  have client := congrArg List.length value.clientRead
  simp only [List.length_append, fixturePayload, List.length_map, List.length_range] at server
  simp only [List.length_append, fixturePayload, List.length_map, List.length_range] at client
  exact ⟨value.assurance.application_prefix.1, value.assurance.application_prefix.2, server, client⟩

theorem Demonstration.large_payloads (value : Demonstration input) :
    536 < value.primaryClient.served.ticket.value.source.packet.segment.payload.length ∧
      536 < value.primaryServer.served.ticket.value.source.packet.segment.payload.length ∧
      536 < value.standbyClient.served.ticket.value.source.packet.segment.payload.length ∧
      536 < value.standbyServer.served.ticket.value.source.packet.segment.payload.length := by
  rw [value.primaryClient.sizeEq, value.primaryServer.sizeEq, value.standbyClient.sizeEq, value.standbyServer.sizeEq]
  decide

theorem Demonstration.deferred_ack (value : Demonstration input) :
    value.acknowledgment.joint.step.before.standby.transport = value.assurance.installation.checkpoint.snapshot.source ∧
      value.source.reply.outstanding = 1201 ∧ value.after.reply.outstanding = 0 ∧
      value.after.clientMSS = TCP.Handshake.receiveOffer input.model.active ∧
      value.after.serverMSS = TCP.Handshake.receiveOffer input.model.passive := by
  obtain ⟨after, phase, client, server⟩ := value.acknowledgment.preserves_offers
  change value.acknowledgment.joint.step.result.state.standby.transport.admission.phase = .data after at phase
  have same : value.after = after := TCP.Admission.Phase.data.inj (value.afterPhase.symm.trans phase)
  rw [← same] at client server
  exact ⟨value.exactBefore, by simp only [TCP.Admission.Lane.outstanding, value.deferred.1, value.deferred.2, Nat.sub_zero],
    value.removed.2.2, client, server⟩

theorem Demonstration.revoked_output (value : Demonstration input) : value.deniedService.evidence.output = none :=
  Check.CampusTCPFacts.service_output_none_of_unauthorized value.report value.assurance.application.compliant
    value.denied.step value.denied.member value.deniedService value.deniedPresent value.unauthorized

private def demonstrate (input : Check.CampusTCP.Input) : Except String (Demonstration input) := do
  let report ← input.check.mapError (·.message)
  let assurance ← Check.CampusTCPTransferFacts.assure report
  let clientOffer ← verify ((TCP.Handshake.receiveOffer input.model.active).limit = 1200) "The client receive offer differs."
  let serverOffer ← verify ((TCP.Handshake.receiveOffer input.model.passive).limit = 800) "The server receive offer differs."
  let clientSend ← verify (input.model.active.ipSendLimit = 1000) "The client IP send limit differs."
  let serverSend ← verify (input.model.passive.ipSendLimit = 1500) "The server IP send limit differs."
  let primaryClient ← dataService report 28 .primary .original 800
  let primaryServer ← dataService report 33 .primary .reply 1200
  let standbyClient ← dataService report 55 .standby .original 800
  let standbyServer ← dataService report 61 .standby .reply 1200
  match sourcePhase : assurance.installation.checkpoint.snapshot.source.admission.phase with
  | .data source =>
    let sourceClient ← verify (source.clientMSS = TCP.Handshake.receiveOffer input.model.active) "The copied client offer differs."
    let sourceServer ← verify (source.serverMSS = TCP.Handshake.receiveOffer input.model.passive) "The copied server offer differs."
    let deferred ← verify (source.reply.observed = 1201 ∧ source.reply.acknowledged = 0) "The source has no deferred byte epoch."
    let acknowledgment ← dataService report 50 .standby .original 0
    let exactBefore ← verify (acknowledgment.joint.step.before.standby.transport.same
      assurance.installation.checkpoint.snapshot.source = true) "The deferred ACK did not use the exact installed cut."
    match afterPhase : acknowledgment.joint.step.result.state.standby.transport.admission.phase with
    | .data after =>
      let removed ← verify (after.reply.observed = 1201 ∧ after.reply.acknowledged = 1201 ∧ after.reply.outstanding = 0)
        "The deferred ACK did not acknowledge the copied server byte epoch."
      let clientRead ← verify (assurance.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes =
        fixturePayload 30 1200 ++ fixturePayload 35 1 ++ fixturePayload 58 1200) "The client read differs from actual service across gateways."
      let serverRead ← verify (assurance.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes =
        fixturePayload 25 800 ++ fixturePayload 52 800) "The server read differs from actual service across gateways."
      let denied ← F.findStep report 70
      match deniedPresent : denied.step.result.service with
      | none => throw "The final denied service is missing."
      | some deniedService =>
        let unauthorized ← verify ((Check.SessionFirewall.stateAt input.model.context.authentication
          denied.step.before.authentication).auth.authorized = false) "The final service must use the actual revoked authentication state."
        return ⟨report, assurance, clientOffer.property, serverOffer.property, clientSend.property, serverSend.property,
          primaryClient, primaryServer, standbyClient, standbyServer, source, sourcePhase, sourceClient.property,
          sourceServer.property, deferred.property, acknowledgment,
          (TCP.Checkpoint.Gateway.same_correct _ _).mp exactBefore.property, after, afterPhase, removed.property,
          clientRead.property, serverRead.property, denied, deniedService, deniedPresent, unauthorized.property⟩
    | _ => throw "The deferred ACK lost the established target phase."
  | _ => throw "The copied source has no established MSS history."

def run : IO Unit := do
  let input ← match Check.CampusTCP.Input.parse (← IO.FS.readFile "examples/tcp-mss/trace.json") with
    | .ok input => pure input
    | .error reason => throw (IO.userError reason)
  let value ← match demonstrate input with
    | .ok value => pure value
    | .error reason => throw (IO.userError reason)
  let _ := value.seed_limits
  let _ := value.copied_offers
  let _ := value.nonempty_prefixes
  let _ := value.revoked_output
  let _ := value.deferred_ack
  let _ := value.large_payloads
  let _ := value.primaryClient.payload_bound
  let _ := value.primaryServer.payload_bound
  let _ := value.standbyClient.payload_bound
  let _ := value.standbyServer.payload_bound
  let _ := value.acknowledgment.preserves_offers
  unless value.report.steps.length == 71 && value.report.remaining.isEmpty do
    throw (IO.userError "The MSS transfer witness must contain the full actual replay.")
  unless value.deniedService.ticket.value.gateway == .standby &&
      value.deniedService.evidence.output.isNone &&
      !value.denied.step.result.state.standby.transport.tracker.records.isEmpty &&
      value.denied.step.result.state.standby.transport.tracker == value.denied.step.before.standby.transport.tracker do
    throw (IO.userError "Current standby denial must retain the copied NAT binding and emit no packet.")
  IO.println "Checked campus TCP MSS tests passed."

end NetlibTest.TCPMSSCampus
