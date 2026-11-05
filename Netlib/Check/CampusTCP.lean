import Netlib.Check.CampusTCPFacts

/-!
# Imported campus TCP execution

The input supplies actual stored configuration and observation events.
Endpoint outputs and gateway services supply all packet inputs.
No replacement established state or delivery path enters this checker.
-/

namespace Netlib.Check.CampusTCP

open Packet Protocol CampusTCPModel

abbrev Event := CampusTCPModel.Event

structure Input where
  model : CampusTCPModel.Input
  events : List Event

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

def namespaceFromJson (json : Lean.Json) : Except String IngressAttachment.NamespaceRef := do
  Import.PacketFields.fields json ["id", "birth"]
  return ⟨← (← json.getObjVal? "id").getNat?, ← (← json.getObjVal? "birth").getNat?⟩

def interfaceFromJson (json : Lean.Json) : Except String IngressAttachment.InterfaceRef := do
  Import.PacketFields.fields json ["namespace", "ifindex", "birth"]
  let executionNS ← namespaceFromJson (← json.getObjVal? "namespace")
  let index ← (← json.getObjVal? "ifindex").getNat?
  if bounded : 0 < index ∧ index ≤ 2147483647 then
    return ⟨executionNS, ⟨index, bounded⟩, ← (← json.getObjVal? "birth").getNat?⟩
  else throw "The interface index must be between 1 and 2147483647."

private def directionFromJson (json : Lean.Json) : Except String FlowNAT.Direction := do
  match ← json.getStr? with
  | "original" => return .original
  | "reply" => return .reply
  | _ => throw "Use original or reply as the flow direction."

private def actorFromJson (json : Lean.Json) : Except String Actor := do
  match ← json.getStr? with
  | "client" => return .client
  | "server" => return .server
  | _ => throw "Use client or server as the endpoint actor."

private def scopeFromJson (json : Lean.Json) : Except String Scope := do
  Import.PacketFields.fields json ["resource", "operation"]
  let resource ← (← json.getObjVal? "resource").getStr?
  let operation ← (← json.getObjVal? "operation").getStr?
  require (!resource.isEmpty && !operation.isEmpty) "Scope names must not be empty."
  return ⟨resource, operation⟩

private def specificationFromJson (json : Lean.Json) : Except String Specification := do
  Import.PacketFields.fields json ["id", "direction", "ingress", "match"]
  return ⟨← (← json.getObjVal? "id").getStr?, ← directionFromJson (← json.getObjVal? "direction"),
    ← interfaceFromJson (← json.getObjVal? "ingress"),
    ← DataPlane.Config.parseTrafficSelection (← json.getObjVal? "match").compress⟩

private def guardFromJson (json : Lean.Json) : Except String Guard := do
  Import.PacketFields.fields json ["id", "source"]
  let value ← json.getObjVal? "source"
  Import.PacketFields.fields value ["namespace", "bindings", "ruleset"]
  let executionNS ← namespaceFromJson (← value.getObjVal? "namespace")
  let bindings ← (← (← value.getObjVal? "bindings").getArr?).toList.mapM fun binding => do
    Import.PacketFields.fields binding ["name", "reference"]
    return (⟨← (← binding.getObjVal? "name").getStr?, ← interfaceFromJson (← binding.getObjVal? "reference")⟩ :
      Import.NftablesIngress.Binding)
  let source ← Import.NftablesIngress.Snapshot.fromJson executionNS bindings (← value.getObjVal? "ruleset")
  return ⟨← (← json.getObjVal? "id").getStr?, source⟩

private def hex (json : Lean.Json) : Except String (List UInt8) := do
  Import.EAPOL.bytesFromHex (← json.getStr?)

private def observationFromJson (json : Lean.Json) : Except String (Option (List UInt8 × Option (List UInt8))) := do
  match json with
  | .null => return none
  | _ =>
    Import.PacketFields.fields json ["inputHex", "outputHex"]
    let input ← hex (← json.getObjVal? "inputHex")
    let output ← match ← json.getObjVal? "outputHex" with
      | .null => pure none
      | value => some <$> hex value
    return some (input, output)

private def eventFromJson (json : Lean.Json) : Except String Event := do
  match ← (← json.getObjVal? "kind").getStr? with
  | "authentication" =>
    Import.PacketFields.fields json ["kind", "index"]
    return .authentication (← (← json.getObjVal? "index").getNat?)
  | "install" =>
    Import.PacketFields.fields json ["kind", "configuration"]
    return .install (← (← json.getObjVal? "configuration").getStr?)
  | "stage" =>
    Import.PacketFields.fields json ["kind", "specification"]
    return .stage (← (← json.getObjVal? "specification").getStr?)
  | "installGuard" =>
    Import.PacketFields.fields json ["kind", "guard"]
    return .installGuard (← (← json.getObjVal? "guard").getStr?)
  | "open" =>
    Import.PacketFields.fields json ["kind", "remote", "policyPermitted"]
    return .open (← TCPHandshake.socketFromJson (← json.getObjVal? "remote"))
      (← (← json.getObjVal? "policyPermitted").getBool?)
  | "write" =>
    Import.PacketFields.fields json ["kind", "actor", "payloadHex"]
    return .write (← actorFromJson (← json.getObjVal? "actor")) (← hex (← json.getObjVal? "payloadHex"))
  | "send" =>
    Import.PacketFields.fields json ["kind", "actor", "count", "policyPermitted"]
    return .send (← actorFromJson (← json.getObjVal? "actor")) (← (← json.getObjVal? "count").getNat?)
      (← (← json.getObjVal? "policyPermitted").getBool?)
  | "read" =>
    Import.PacketFields.fields json ["kind", "actor", "count"]
    return .read (← actorFromJson (← json.getObjVal? "actor")) (← (← json.getObjVal? "count").getNat?)
  | "emitAck" =>
    Import.PacketFields.fields json ["kind", "actor", "policyPermitted"]
    return .emitAck (← actorFromJson (← json.getObjVal? "actor")) (← (← json.getObjVal? "policyPermitted").getBool?)
  | "assign" =>
    Import.PacketFields.fields json ["kind", "output", "ingress"]
    return .assign (← (← json.getObjVal? "output").getNat?) (← interfaceFromJson (← json.getObjVal? "ingress"))
  | "serve" =>
    Import.PacketFields.fields json ["kind", "ticket", "observed"]
    return .serve (← (← json.getObjVal? "ticket").getNat?) (← observationFromJson (← json.getObjVal? "observed"))
  | "deliver" =>
    Import.PacketFields.fields json ["kind", "service", "rawIPv4Hex", "policyPermitted"]
    return .deliver (← (← json.getObjVal? "service").getNat?) (← hex (← json.getObjVal? "rawIPv4Hex"))
      (← (← json.getObjVal? "policyPermitted").getBool?)
  | _ => throw "The campus TCP event kind is unknown."

def Input.fromJson (json : Lean.Json) : Except String Input := do
  Import.PacketFields.fields json ["schema", "authentication", "application", "intent", "routing", "configs", "initialConfig",
    "namespace", "authenticationPort", "live", "specifications", "guards", "initialGuard", "active", "passive", "zone", "events"]
  require ((← (← json.getObjVal? "schema").getNat?) == 1) "Use campus TCP schema 1."
  let authentication ← Check.EAP.Input.fromJson (← json.getObjVal? "authentication")
  let application ← scopeFromJson (← json.getObjVal? "application")
  let requirements ← Check.SessionFirewall.requirementsFromJson (← json.getObjVal? "intent")
  if scopes : requirements.all (fun requirement => decide (requirement.scope = application)) = true then
    let routing ← Check.ConntrackLifecycle.routingFromJson (← json.getObjVal? "routing")
    let configs ← (← (← json.getObjVal? "configs").getArr?).toList.zipIdx.mapM fun (value, index) =>
      Check.ConntrackLifecycle.Config.fromJson value index
    require (decide (configs.map (·.id)).Nodup) "Configuration identities must be unique."
    let initialConfigName ← (← json.getObjVal? "initialConfig").getStr?
    let some initialConfig := configs.find? (·.id == initialConfigName) | throw "The initial configuration is unknown."
    let executionNS ← namespaceFromJson (← json.getObjVal? "namespace")
    let authenticationPort ← interfaceFromJson (← json.getObjVal? "authenticationPort")
    let live ← (← (← json.getObjVal? "live").getArr?).toList.mapM interfaceFromJson
    let specifications ← (← (← json.getObjVal? "specifications").getArr?).toList.mapM specificationFromJson
    require (decide (specifications.map (·.id)).Nodup) "Ingress specification identities must be unique."
    let guards ← (← (← json.getObjVal? "guards").getArr?).toList.mapM guardFromJson
    require (decide (guards.map (·.id)).Nodup) "Ingress guard identities must be unique."
    let initialGuardName ← (← json.getObjVal? "initialGuard").getStr?
    let some initialGuard := guards.find? (·.id == initialGuardName) | throw "The initial ingress guard is unknown."
    let active ← TCPHandshake.localFromJson (← json.getObjVal? "active")
    let passive ← TCPHandshake.localFromJson (← json.getObjVal? "passive")
    let zone ← (← json.getObjVal? "zone").getNat?
    require (zone == 0) "The selected campus path uses zone zero."
    let events ← (← (← json.getObjVal? "events").getArr?).toList.mapM eventFromJson
    let context : CampusTCPService.Context := ⟨authentication, requirements, routing, configs, executionNS, specifications.map (·.traffic)⟩
    let model : CampusTCPModel.Input := ⟨context, application, by simpa [List.all_eq_true] using scopes,
      initialConfig, initialGuard, guards, specifications, authenticationPort, live, active, passive, zone⟩
    return ⟨model, events⟩
  else throw "Every application intent must use the declared campus scope."

def Input.parse (text : String) : Except String Input := do Input.fromJson (← Import.Json.parse text)
def Input.check (input : Input) := input.model.check input.events

inductive ApplicationStatus (report : CampusTCPModel.Report input events) where
  | pendingStartup (pending : ∃ stage incomplete, report.final.connection = .startup stage incomplete)
  | failed (reason : String)
  | checked (value : CampusTCPFacts.Assurance report)

def applicationStatus (report : CampusTCPModel.Report input events) : ApplicationStatus report :=
  if report.compliant then
    match selected : report.final.connection with
    | .startup stage incomplete => .pendingStartup ⟨stage, incomplete, selected⟩
    | .application .. => match CampusTCPFacts.assure report with
      | .error reason => .failed reason
      | .ok value => .checked value
  else .failed "The actual joint replay is not compliant."

def ApplicationStatus.passed : ApplicationStatus report → Bool
  | .pendingStartup _ | .checked _ => true
  | .failed _ => false

def ApplicationStatus.json : ApplicationStatus report → Lean.Json
  | .pendingStartup _ => Lean.Json.mkObj [("status", Lean.toJson "pendingStartup")]
  | .failed reason => Lean.Json.mkObj [("status", Lean.toJson "failed"), ("reason", Lean.toJson reason)]
  | .checked value => Lean.Json.mkObj [
    ("status", Lean.toJson "checked"), ("startupReceipts", Lean.toJson (3 : Nat)),
    ("clientWrittenBytes", Lean.toJson (value.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.written).length),
    ("serverWrittenBytes", Lean.toJson (value.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.written).length),
    ("clientReadBytes", Lean.toJson (value.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes).length),
    ("serverReadBytes", Lean.toJson (value.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes).length),
    ("clientReceives", Lean.toJson (value.endpoints.client.steps.filter fun step =>
      match step.event with | .receive _ => true | _ => false).length),
    ("serverReceives", Lean.toJson (value.endpoints.server.steps.filter fun step =>
      match step.event with | .receive _ => true | _ => false).length)]

def namespaceJson (value : IngressAttachment.NamespaceRef) : Lean.Json :=
  Lean.Json.mkObj [("id", Lean.toJson value.id), ("birth", Lean.toJson value.birth)]

def interfaceJson (value : IngressAttachment.InterfaceRef) : Lean.Json := Lean.Json.mkObj [
  ("namespace", namespaceJson value.ns), ("ifindex", Lean.toJson value.ifindex.val), ("birth", Lean.toJson value.birth)]

def actorName : Actor → String | .client => "client" | .server => "server"
def directionName : FlowNAT.Direction → String | .original => "original" | .reply => "reply"

def eventKind : Event → String
  | .authentication _ => "authentication" | .install _ => "install" | .stage _ => "stage" | .installGuard _ => "installGuard"
  | .open .. => "open" | .write .. => "write" | .send .. => "send" | .read .. => "read" | .emitAck .. => "emitAck"
  | .assign .. => "assign" | .serve .. => "serve" | .deliver .. => "deliver"

def eventJson (event : Event) : Lean.Json :=
  Lean.Json.mkObj (("kind", Lean.toJson (eventKind event)) :: match event with
    | .authentication index => [("index", Lean.toJson index)]
    | .install id => [("configuration", Lean.toJson id)]
    | .stage id => [("specification", Lean.toJson id)]
    | .installGuard id => [("guard", Lean.toJson id)]
    | .open remote policy => [("remote", TCPHandshake.socketJson remote), ("policyPermitted", Lean.toJson policy)]
    | .write actor bytes => [("actor", Lean.toJson (actorName actor)), ("payloadHex", Lean.toJson (Import.EAPOL.bytesToHex bytes))]
    | .send actor count policy => [("actor", Lean.toJson (actorName actor)), ("count", Lean.toJson count), ("policyPermitted", Lean.toJson policy)]
    | .read actor count => [("actor", Lean.toJson (actorName actor)), ("count", Lean.toJson count)]
    | .emitAck actor policy => [("actor", Lean.toJson (actorName actor)), ("policyPermitted", Lean.toJson policy)]
    | .assign output ingress => [("output", Lean.toJson output), ("ingress", interfaceJson ingress)]
    | .serve ticket observed => [("ticket", Lean.toJson ticket), ("observed", match observed with
      | none => .null
      | some (input, output) => Lean.Json.mkObj [("inputHex", Lean.toJson (Import.EAPOL.bytesToHex input)),
          ("outputHex", Lean.toJson (output.map Import.EAPOL.bytesToHex))])]
    | .deliver service bytes policy => [("service", Lean.toJson service),
        ("rawIPv4Hex", Lean.toJson (Import.EAPOL.bytesToHex bytes)), ("policyPermitted", Lean.toJson policy)])

def connectionStage : Connection active passive → TCPHandshake.Stage active passive
  | .startup stage _ => stage
  | .application complete _ => .complete complete

def clientState : Connection active passive → Option TCP.Endpoint.State
  | .startup stage _ => stage.activeSeed
  | .application _ endpoints => some endpoints.client.current

def serverState : Connection active passive → Option TCP.Endpoint.State
  | .startup stage _ => stage.passiveSeed
  | .application _ endpoints => some endpoints.server.current

private def field (json : Lean.Json) (name : String) : Lean.Json := match json.getObjVal? name with
  | .ok value => value | .error _ => .null

def stateJson (state : State input) : Lean.Json :=
  let stage := (connectionStage state.connection).json
  Lean.Json.mkObj [
    ("after", Lean.toJson state.authentication), ("configuration", Lean.toJson state.configuration.id), ("guard", Lean.toJson state.guard.id),
    ("activePhase", field stage "activePhase"), ("passivePhase", field stage "passivePhase"),
    ("activeEstablishedAt", field stage "activeEstablishedAt"), ("passiveEstablishedAt", field stage "passiveEstablishedAt"),
    ("client", ((clientState state.connection).map TCPEndpoint.stateJson).getD .null),
    ("server", ((serverState state.connection).map TCPEndpoint.stateJson).getD .null),
    ("admissionPhase", Lean.toJson state.admission.phase.name), ("admissionObservations", Lean.toJson state.admission.observations.length),
    ("records", Lean.toJson (state.tracker.records.map fun record => Lean.Json.mkObj [
      ("zone", Lean.toJson record.entry.flow.originalZone), ("original", Import.PacketFields.headerJson record.entry.flow.original),
      ("translated", Import.PacketFields.headerJson (record.entry.flow.output .original)), ("seenReply", Lean.toJson record.seenReply)])),
    ("outputs", Lean.toJson state.outputs.length), ("pendingTickets", Lean.toJson (state.work.pending.map (·.id))),
    ("services", Lean.toJson state.services.length)]

def producedKind : Produced active passive → String
  | .startup step _ _ => match step.event with | .activeOpen .. => "open" | _ => "startup"
  | .application _ step _ _ => match step.event with | .send .. => "send" | .emitAck .. => "emitAck" | _ => "invalid"

def producedStartupOperation : Produced active passive → Option String
  | .startup step _ _ => some step.event.kind
  | .application .. => none

def producedJson (value : Produced active passive) (id : Nat) : Lean.Json := Lean.Json.mkObj [
  ("id", Lean.toJson id), ("index", Lean.toJson value.time), ("actor", Lean.toJson (actorName value.actor)),
  ("kind", Lean.toJson (producedKind value)), ("startupOperation", Lean.toJson (producedStartupOperation value)),
  ("rawIPv4Hex", Lean.toJson (Import.EAPOL.bytesToHex value.output.bytes)), ("decoded", TCPReceive.decodedJson value.output.packet)]

def disposition : TCP.WireForwarding.Disposition → String
  | .forwarded => "forwarded" | .routeDrop => "routeDrop" | .ttlExpired => "ttlExpired"
  | .forwardDrop => "forwardDrop" | .lateDrop => "lateDrop"

def servedJson (value : Served input) (id : Nat) : Lean.Json :=
  Lean.Json.mkObj [
    ("id", Lean.toJson id), ("index", Lean.toJson value.time), ("ticket", Lean.toJson value.ticket.id),
    ("outputID", Lean.toJson value.ticket.value.outputIndex), ("actor", Lean.toJson (actorName value.ticket.value.produced.actor)),
    ("sourceKind", Lean.toJson (producedKind value.ticket.value.produced)), ("inputHex", Lean.toJson (Import.EAPOL.bytesToHex value.ticket.value.source.bytes)),
    ("output", TCPEndpoint.outputJson (value.evidence.output.map (·.asInput))),
    ("disposition", Lean.toJson (match value.evidence.processing with | none => "earlyDrop" | some p => disposition p.outcome.disposition)),
    ("direction", Lean.toJson (value.evidence.processing.map (fun p => directionName p.prepared.attachment.direction))),
    ("nextHop", Lean.toJson (value.evidence.processing.bind (fun p => p.outcome.nextHop))),
    ("checks", Lean.Json.mkObj [("forward", Lean.toJson value.evidence.checks.forward.passed),
      ("ingress", Lean.toJson value.evidence.checks.guard.passed), ("coverage", Lean.toJson (CampusTCPService.coverage input.context value.ticket.value.source))]),
    ("observationsMatch", Lean.toJson value.observed), ("routeRoleMatch", Lean.toJson value.routeMatched)]

def decisionJson (step : CampusTCPModel.Step input) : Lean.Json :=
  match step.result.application, step.result.startup with
  | some (_, applied), _ => TCPEndpoint.decisionJson applied.result.decision
  | none, some startup => field (startup.json) "decision"
  | none, none => if step.result.supported then Lean.Json.mkObj [
      ("kind", Lean.toJson "accepted"), ("operation", Lean.toJson (eventKind step.event))]
    else Lean.Json.mkObj [("kind", Lean.toJson "unsupported"), ("reason", Lean.toJson step.result.decision)]

def stepJson (step : CampusTCPModel.Step input) : Lean.Json := Lean.Json.mkObj [
  ("index", Lean.toJson step.before.time), ("event", eventJson step.event), ("before", stateJson step.before),
  ("supported", Lean.toJson step.result.supported), ("passed", Lean.toJson step.result.passed),
  ("decision", decisionJson step), ("output", TCPEndpoint.outputJson (step.result.output.map (·.output))),
  ("decodedInput", match step.result.receipt with | none => .null | some receipt => TCPReceive.decodedJson receipt.received.packet),
  ("readHex", Lean.toJson (Import.EAPOL.bytesToHex step.result.read)),
  ("service", (step.result.service.map (fun value => servedJson value step.before.services.length)).getD .null),
  ("state", stateJson step.result.state)]

def assumptions : List String := [
  "The result concerns the selected Lean gateway model, not Linux TCP tracker refinement or native installation.",
  "The caller supplies current interface lifetimes, principal/header ownership, local sequence choices, and IP size evidence.",
  "EAP method acceptance and credential integrity remain supplied evidence. TLS cryptography is outside this model.",
  "Imported policy, NAT, and routing snapshots describe the exclusive selected hook sequence.",
  "The endpoint output policy is local permission. Current gateway permission comes from actual installed policy checks.",
  "The selected TCP history excludes options, retransmission, replacement, close processing, and unbounded sequence reuse.",
  "Actual gateway output supplies receiver bytes in the modeled timeline. Physical delivery and connection-instance identity remain external.",
  "Logoff and checked denial prevent later gateway output. They do not erase bytes already received or buffered.",
  "TCP replication, failover, native Wi-Fi enforcement, and the full campus demonstration remain open."]

def sources : List Standards.Source := [
  ⟨"Transmission Control Protocol", "RFC 9293", "3.4 and 3.10.7", "https://www.rfc-editor.org/rfc/rfc9293.html#section-3.10.7"⟩,
  ⟨"Extensible Authentication Protocol (EAP)", "RFC 3748", "4", "https://www.rfc-editor.org/rfc/rfc3748.html#section-4"⟩,
  ⟨"Linux netfilter NAT", "v6.8", "nf_nat_packet", Protocol.NetfilterNAT.sourceURL⟩,
  ⟨"Linux connection tracking", "v6.8", "ordinary attachment and confirmation", Protocol.ConntrackLifecycle.sourceURL⟩]

def renderJson (report : CampusTCPModel.Report input events)
    (application : ApplicationStatus report := applicationStatus report) : Lean.Json := Lean.Json.mkObj [
  ("scope", Lean.toJson "campus-tcp-application-path"), ("supported", Lean.toJson report.supported),
  ("compliant", Lean.toJson report.compliant), ("inputEvents", Lean.toJson events.length), ("evaluatedEvents", Lean.toJson report.steps.length),
  ("applicationAssurance", application.json),
  ("initial", stateJson input.initial), ("steps", Lean.toJson (report.steps.map stepJson)), ("final", stateJson report.final),
  ("outputs", Lean.toJson (report.final.outputs.zipIdx.map fun (value, id) => producedJson value id)),
  ("services", Lean.toJson (report.final.services.zipIdx.map fun (value, id) => servedJson value id)),
  ("reads", Lean.toJson (report.steps.filterMap fun step => match step.event, step.result.application with
    | .read actor _, some (_, applied) => match applied.result.decision with
      | .accepted (.read _) => some (Lean.Json.mkObj [("index", Lean.toJson step.before.time), ("actor", Lean.toJson (actorName actor)),
          ("readHex", Lean.toJson (Import.EAPOL.bytesToHex step.result.read))])
      | _ => none
    | _, _ => none)),
  ("remainingEvents", Lean.toJson (report.remaining.map eventJson)), ("assumptions", Lean.toJson assumptions),
  ("sources", Lean.toJson (sources.map fun source => Lean.Json.mkObj [
    ("document", Lean.toJson source.document), ("version", Lean.toJson source.version),
    ("clause", Lean.toJson source.clause), ("url", Lean.toJson source.url)]))]

def render (report : CampusTCPModel.Report input events)
    (application : ApplicationStatus report := applicationStatus report) : String :=
  (if report.compliant then "CAMPUS TCP MODEL COMPLIANT\n" else "CAMPUS TCP MODEL NOT COMPLIANT\n") ++
    (renderJson report application).pretty

end Netlib.Check.CampusTCP
