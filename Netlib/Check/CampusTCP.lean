import Netlib.Check.CampusTCPFacts
import Netlib.Check.CampusTCPTransferFacts
import Netlib.Check.CampusTCPAckFacts
import Netlib.Check.CampusTCPGapFacts
import Netlib.Check.TCPAdmissionJSON
import Netlib.Check.CampusTCPCustodyFacts
import Netlib.Check.CampusTCPSparseFacts

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

private def fieldsWithOptional (json : Lean.Json) (required optional : List String) : Except String Unit :=
  Import.PacketFields.fields json (required ++ optional.filter fun name =>
    match json.getObjVal? name with | .ok _ => true | .error _ => false)

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

private def gatewayFromJson (json : Lean.Json) : Except String Gateway := do
  match ← json.getStr? with
  | "primary" => return .primary
  | "standby" => return .standby
  | _ => throw "Use primary or standby as the gateway."

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

private def deploymentFromJson (json : Lean.Json) : Except String Deployment := do
  Import.PacketFields.fields json ["namespace", "routing", "configs", "initialConfig", "authenticationPort", "live",
    "specifications", "guards", "initialGuard"]
  let executionNS ← namespaceFromJson (← json.getObjVal? "namespace")
  let routing ← Check.ConntrackLifecycle.routingFromJson (← json.getObjVal? "routing")
  let configs ← (← (← json.getObjVal? "configs").getArr?).toList.zipIdx.mapM fun (value, index) =>
    Check.ConntrackLifecycle.Config.fromJson value index
  require (decide (configs.map (·.id)).Nodup) "Configuration identities must be unique."
  let initialConfigName ← (← json.getObjVal? "initialConfig").getStr?
  let some initialConfig := configs.find? (·.id == initialConfigName) | throw "The initial configuration is unknown."
  let authenticationPort ← interfaceFromJson (← json.getObjVal? "authenticationPort")
  let live ← (← (← json.getObjVal? "live").getArr?).toList.mapM interfaceFromJson
  let specifications ← (← (← json.getObjVal? "specifications").getArr?).toList.mapM specificationFromJson
  require (decide (specifications.map (·.id)).Nodup) "Ingress specification identities must be unique."
  let guards ← (← (← json.getObjVal? "guards").getArr?).toList.mapM guardFromJson
  require (decide (guards.map (·.id)).Nodup) "Ingress guard identities must be unique."
  let initialGuardName ← (← json.getObjVal? "initialGuard").getStr?
  let some initialGuard := guards.find? (·.id == initialGuardName) | throw "The initial ingress guard is unknown."
  return ⟨routing, configs, executionNS, initialConfig, initialGuard, guards, specifications, authenticationPort, live⟩

private def eventFromJson (json : Lean.Json) : Except String Event := do
  match ← (← json.getObjVal? "kind").getStr? with
  | "authentication" =>
    Import.PacketFields.fields json ["kind", "index"]
    return .authentication (← (← json.getObjVal? "index").getNat?)
  | "install" =>
    fieldsWithOptional json ["kind", "configuration"] ["gateway"]
    let id ← (← json.getObjVal? "configuration").getStr?
    match json.getObjVal? "gateway" with
    | .error _ => return .install id
    | .ok gateway => return .installAt (← gatewayFromJson gateway) id
  | "stage" =>
    fieldsWithOptional json ["kind", "specification"] ["gateway"]
    let id ← (← json.getObjVal? "specification").getStr?
    match json.getObjVal? "gateway" with
    | .error _ => return .stage id
    | .ok gateway => return .stageAt (← gatewayFromJson gateway) id
  | "installGuard" =>
    fieldsWithOptional json ["kind", "guard"] ["gateway"]
    let id ← (← json.getObjVal? "guard").getStr?
    match json.getObjVal? "gateway" with
    | .error _ => return .installGuard id
    | .ok gateway => return .installGuardAt (← gatewayFromJson gateway) id
  | "pause" =>
    Import.PacketFields.fields json ["kind"]
    return .pause
  | "stageCheckpoint" =>
    Import.PacketFields.fields json ["kind"]
    return .stageCheckpoint
  | "installCheckpoint" =>
    Import.PacketFields.fields json ["kind", "namespace"]
    return .installCheckpoint (← namespaceFromJson (← json.getObjVal? "namespace"))
  | "switchRoute" =>
    Import.PacketFields.fields json ["kind", "actor", "gateway"]
    return .switchRoute (← actorFromJson (← json.getObjVal? "actor")) (← gatewayFromJson (← json.getObjVal? "gateway"))
  | "fencePrimary" =>
    Import.PacketFields.fields json ["kind"]
    return .fencePrimary
  | "resume" =>
    Import.PacketFields.fields json ["kind"]
    return .resume
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
  | "enableRecovery" =>
    Import.PacketFields.fields json ["kind", "actor"]
    return .enableRecovery (← actorFromJson (← json.getObjVal? "actor"))
  | "enableAck" =>
    Import.PacketFields.fields json ["kind", "actor"]
    return .enableAck (← actorFromJson (← json.getObjVal? "actor"))
  | "dispatchAck" =>
    Import.PacketFields.fields json ["kind", "actor", "policyPermitted"]
    return .dispatchAck (← actorFromJson (← json.getObjVal? "actor")) (← (← json.getObjVal? "policyPermitted").getBool?)
  | "advanceClock" =>
    Import.PacketFields.fields json ["kind", "actor", "millis"]
    return .advanceClock (← actorFromJson (← json.getObjVal? "actor")) (← (← json.getObjVal? "millis").getNat?)
  | "timeout" =>
    Import.PacketFields.fields json ["kind", "actor", "policyPermitted"]
    return .timeout (← actorFromJson (← json.getObjVal? "actor")) (← (← json.getObjVal? "policyPermitted").getBool?)
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
  | "copyPacket" =>
    Import.PacketFields.fields json ["kind", "packet"]
    return .copyPacket (← (← json.getObjVal? "packet").getNat?)
  | "dropPacket" =>
    Import.PacketFields.fields json ["kind", "packet"]
    return .dropPacket (← (← json.getObjVal? "packet").getNat?)
  | _ => throw "The campus TCP event kind is unknown."

def Input.fromJson (json : Lean.Json) : Except String Input := do
  fieldsWithOptional json ["schema", "authentication", "application", "intent", "routing", "configs", "initialConfig",
    "namespace", "authenticationPort", "live", "specifications", "guards", "initialGuard", "active", "passive", "zone", "events"] ["standby"]
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
    let standby ← match json.getObjVal? "standby" with
      | .error _ => pure none
      | .ok value => some <$> deploymentFromJson value
    if let some deployment := standby then
      require (decide (deployment.executionNS ≠ executionNS)) "The two gateway namespace lifetimes must be distinct."
    let context : CampusTCPService.Context := ⟨authentication, requirements, routing, configs, executionNS, specifications.map (·.traffic)⟩
    let model : CampusTCPModel.Input := ⟨context, application, by simpa [List.all_eq_true] using scopes,
      initialConfig, initialGuard, guards, specifications, authenticationPort, live, active, passive, zone, standby⟩
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

def completedTransfer (report : CampusTCPModel.Report input events) : Bool :=
  report.final.primaryFenced && !report.final.assignmentPaused &&
    decide (report.final.owners.client = .standby) && decide (report.final.owners.server = .standby)

inductive TransferStatus (report : CampusTCPModel.Report input events) where
  | disabled (absent : input.standby.isSome = false)
  | pending (incomplete : completedTransfer report = false)
  | failed (reason : String)
  | checked (value : CampusTCPTransferFacts.Assurance report)

def transferStatus (report : CampusTCPModel.Report input events) : TransferStatus report :=
  match declared : input.standby with
  | none => .disabled (by rw [declared]; rfl)
  | some _ =>
    if report.compliant then
      if completed : completedTransfer report = true then
        match CampusTCPTransferFacts.assure report with
        | .error reason => .failed reason
        | .ok value => .checked value
      else .pending (by cases actual : completedTransfer report <;> simp_all)
    else .failed "The actual joint replay is not compliant."

def TransferStatus.passed : TransferStatus report → Bool
  | .disabled _ | .pending _ | .checked _ => true
  | .failed _ => false

def TransferStatus.json : TransferStatus report → Lean.Json
  | .disabled _ => Lean.Json.mkObj [("status", Lean.toJson "disabled")]
  | .pending _ => Lean.Json.mkObj [("status", Lean.toJson "pending")]
  | .failed reason => Lean.Json.mkObj [("status", Lean.toJson "failed"), ("reason", Lean.toJson reason)]
  | .checked value => Lean.Json.mkObj [
    ("status", Lean.toJson "checked"), ("pausedAt", Lean.toJson value.pause.step.before.time),
    ("stagedAt", Lean.toJson value.staging.step.before.time), ("installedAt", Lean.toJson value.step.before.time),
    ("clientRouteAt", Lean.toJson value.clientRoute.step.before.time), ("serverRouteAt", Lean.toJson value.serverRoute.step.before.time),
    ("fencedAt", Lean.toJson value.fence.step.before.time), ("resumedAt", Lean.toJson value.resume.step.before.time),
    ("historyTransitions", Lean.toJson value.installation.history.length),
    ("sourcePreserved", Lean.toJson (report.final.primary.transport.same value.installation.checkpoint.snapshot.source))]

def ackEnabled (report : CampusTCPModel.Report input events) : Bool :=
  match report.final.connection with
  | .startup .. => false
  | .application _ endpoints => endpoints.client.current.ackReaction.isSome || endpoints.server.current.ackReaction.isSome

inductive AckStatus (report : CampusTCPModel.Report input events) where
  | disabled (absent : ackEnabled report = false)
  | pending (value : CampusTCPAckFacts.Evidence report)
      (owed : (TCP.AckTrace.work value.application.endpoints.client.current).pending ≠ [] ∨
        (TCP.AckTrace.work value.application.endpoints.server.current).pending ≠ [])
  | failed (reason : String)
  | checked (value : CampusTCPAckFacts.Assurance report)

def ackStatus (report : CampusTCPModel.Report input events) : AckStatus report :=
  if enabled : ackEnabled report = true then
    match CampusTCPAckFacts.evidence report with
    | .error reason => .failed reason
    | .ok value =>
      if clientClosed : (TCP.AckTrace.work value.application.endpoints.client.current).pending = [] then
        if serverClosed : (TCP.AckTrace.work value.application.endpoints.server.current).pending = [] then
          .checked ⟨value, clientClosed, serverClosed⟩
        else .pending value (.inr serverClosed)
      else .pending value (.inl clientClosed)
  else .disabled (by cases actual : ackEnabled report <;> simp_all)

def AckStatus.passed : AckStatus report → Bool
  | .disabled _ | .pending .. | .checked _ => true
  | .failed _ => false

private def ackCounts (value : CampusTCPAckFacts.Evidence report) : List (String × Lean.Json) :=
  let client := TCP.AckTrace.work value.application.endpoints.client.current
  let server := TCP.AckTrace.work value.application.endpoints.server.current
  [("clientEnabled", Lean.toJson value.application.endpoints.client.current.ackReaction.isSome),
    ("serverEnabled", Lean.toJson value.application.endpoints.server.current.ackReaction.isSome),
    ("clientCauses", Lean.toJson client.nextID), ("clientDischarges", Lean.toJson client.completed.length),
    ("clientPending", Lean.toJson client.pending.length),
    ("serverCauses", Lean.toJson server.nextID), ("serverDischarges", Lean.toJson server.completed.length),
    ("serverPending", Lean.toJson server.pending.length)]

def AckStatus.json : AckStatus report → Lean.Json
  | .disabled _ => Lean.Json.mkObj [("status", Lean.toJson "disabled")]
  | .failed reason => Lean.Json.mkObj [("scope", Lean.toJson "local-ack-generation"),
      ("status", Lean.toJson "failed"), ("reason", Lean.toJson reason)]
  | .pending value _ => Lean.Json.mkObj ([("scope", Lean.toJson "local-ack-generation"),
      ("status", Lean.toJson "pending")] ++ ackCounts value)
  | .checked value => Lean.Json.mkObj ([("scope", Lean.toJson "local-ack-generation"),
      ("status", Lean.toJson "checked")] ++ ackCounts value.toEvidence)

def receiveGapSeen (report : CampusTCPModel.Report input events) : Bool :=
  match report.final.connection with
  | .startup .. => false
  | .application _ endpoints => endpoints.client.current.receiveStore.seenGap || endpoints.server.current.receiveStore.seenGap

inductive ReceiveGapStatus (report : CampusTCPModel.Report input events) where
  | absent (unseen : receiveGapSeen report = false)
  | pending (value : CampusTCPGapFacts.Evidence report)
      (held : value.application.endpoints.client.current.receiveStore.held ≠ [] ∨
        value.application.endpoints.server.current.receiveStore.held ≠ [])
  | failed (reason : String)
  | checked (value : CampusTCPGapFacts.Assurance report)

def receiveGapStatus (report : CampusTCPModel.Report input events) : ReceiveGapStatus report :=
  if seen : receiveGapSeen report = true then
    match CampusTCPGapFacts.evidence report with
    | .error reason => .failed reason
    | .ok value =>
      if clientClosed : value.application.endpoints.client.current.receiveStore.held = [] then
        if serverClosed : value.application.endpoints.server.current.receiveStore.held = [] then
          .checked ⟨value, clientClosed, serverClosed⟩
        else .pending value (.inr serverClosed)
      else .pending value (.inl clientClosed)
  else .absent (by cases actual : receiveGapSeen report <;> simp_all)

def ReceiveGapStatus.passed : ReceiveGapStatus report → Bool
  | .absent _ | .pending .. | .checked _ => true
  | .failed _ => false

private def receiveGapCounts (value : CampusTCPGapFacts.Evidence report) : List (String × Lean.Json) :=
  let client := value.application.endpoints.client
  let server := value.application.endpoints.server
  [("clientReceipts", Lean.toJson client.current.receiveStore.nextID),
    ("serverReceipts", Lean.toJson server.current.receiveStore.nextID),
    ("clientHeldBytes", Lean.toJson client.current.receiveStore.heldBytes),
    ("serverHeldBytes", Lean.toJson server.current.receiveStore.heldBytes),
    ("clientReleasedBytes", Lean.toJson (client.steps.flatMap TCP.ApplicationTrace.Step.releasedPayload).length),
    ("serverReleasedBytes", Lean.toJson (server.steps.flatMap TCP.ApplicationTrace.Step.releasedPayload).length),
    ("clientReadBytes", Lean.toJson (client.steps.flatMap TCP.ApplicationTrace.Step.readBytes).length),
    ("serverReadBytes", Lean.toJson (server.steps.flatMap TCP.ApplicationTrace.Step.readBytes).length)]

def ReceiveGapStatus.json : ReceiveGapStatus report → Lean.Json
  | .absent _ => Lean.Json.mkObj [("status", Lean.toJson "absent")]
  | .failed reason => Lean.Json.mkObj [("scope", Lean.toJson "ordered-receive-storage"),
      ("status", Lean.toJson "failed"), ("reason", Lean.toJson reason)]
  | .pending value _ => Lean.Json.mkObj ([("scope", Lean.toJson "ordered-receive-storage"),
      ("status", Lean.toJson "pending")] ++ receiveGapCounts value)
  | .checked value => Lean.Json.mkObj ([("scope", Lean.toJson "ordered-receive-storage"),
      ("status", Lean.toJson "checked")] ++ receiveGapCounts value.toEvidence)

def gatewaySparse (state : TCP.Checkpoint.Gateway) : Bool :=
  match state.admission.phase with
  | .data session => TCPAdmissionJSON.sparseSeen session.original || TCPAdmissionJSON.sparseSeen session.reply
  | _ => false

def sparseSeen (report : CampusTCPModel.Report input events) : Bool :=
  gatewaySparse report.final.primary.transport || gatewaySparse report.final.standby.transport

inductive SparseStatus (report : CampusTCPModel.Report input events) where
  | absent (unseen : sparseSeen report = false)
  | failed (reason : String)
  | checked (value : CampusTCPSparseFacts.Assurance report)

def sparseStatus (report : CampusTCPModel.Report input events) : SparseStatus report :=
  if seen : sparseSeen report = true then
    match CampusTCPSparseFacts.assure report with
    | .ok value => .checked value
    | .error reason => .failed reason
  else .absent (by cases actual : sparseSeen report <;> simp_all)

def SparseStatus.passed : SparseStatus report → Bool
  | .absent _ | .checked _ => true
  | .failed _ => false

private def sparseLaneSummary (lane : TCP.Admission.Lane) : Lean.Json := Lean.Json.mkObj [
  ("frontier", Lean.toJson lane.observed), ("highEnd", Lean.toJson lane.highEnd),
  ("uniqueBytes", Lean.toJson lane.uniqueBytes), ("sources", Lean.toJson lane.coverage.runs.length),
  ("prefixComplete", Lean.toJson (decide (lane.observed = lane.highEnd)))]

private def sparseGatewaySummary (name : String) (state : TCP.Checkpoint.Gateway) : Lean.Json :=
  Lean.Json.mkObj (("gateway", Lean.toJson name) :: match state.admission.phase with
    | .data session => [("original", sparseLaneSummary session.original), ("reply", sparseLaneSummary session.reply)]
    | _ => [("original", .null), ("reply", .null)])

def SparseStatus.json : SparseStatus report → Lean.Json
  | .absent _ => Lean.Json.mkObj [("status", Lean.toJson "absent")]
  | .failed reason => Lean.Json.mkObj [("scope", Lean.toJson "gateway-observation-sources"),
      ("status", Lean.toJson "failed"), ("reason", Lean.toJson reason)]
  | .checked _ => Lean.Json.mkObj [("scope", Lean.toJson "gateway-observation-sources"),
      ("status", Lean.toJson "checked"), ("gateways", Lean.toJson [
        sparseGatewaySummary "primary" report.final.primary.transport,
        sparseGatewaySummary "standby" report.final.standby.transport])]

def namespaceJson (value : IngressAttachment.NamespaceRef) : Lean.Json :=
  Lean.Json.mkObj [("id", Lean.toJson value.id), ("birth", Lean.toJson value.birth)]

def interfaceJson (value : IngressAttachment.InterfaceRef) : Lean.Json := Lean.Json.mkObj [
  ("namespace", namespaceJson value.ns), ("ifindex", Lean.toJson value.ifindex.val), ("birth", Lean.toJson value.birth)]

def actorName : Actor → String | .client => "client" | .server => "server"
def directionName : FlowNAT.Direction → String | .original => "original" | .reply => "reply"
def gatewayName : Gateway → String | .primary => "primary" | .standby => "standby"

def eventKind : Event → String
  | .authentication _ => "authentication" | .install _ => "install" | .stage _ => "stage" | .installGuard _ => "installGuard"
  | .installAt .. => "install" | .stageAt .. => "stage" | .installGuardAt .. => "installGuard"
  | .pause => "pause" | .stageCheckpoint => "stageCheckpoint" | .installCheckpoint _ => "installCheckpoint"
  | .switchRoute .. => "switchRoute" | .fencePrimary => "fencePrimary" | .resume => "resume"
  | .open .. => "open" | .write .. => "write" | .send .. => "send" | .read .. => "read" | .emitAck .. => "emitAck"
  | .enableRecovery .. => "enableRecovery" | .advanceClock .. => "advanceClock" | .timeout .. => "timeout"
  | .enableAck .. => "enableAck" | .dispatchAck .. => "dispatchAck"
  | .assign .. => "assign" | .serve .. => "serve" | .deliver .. => "deliver"
  | .copyPacket _ => "copyPacket" | .dropPacket _ => "dropPacket"

def eventJson (event : Event) : Lean.Json :=
  Lean.Json.mkObj (("kind", Lean.toJson (eventKind event)) :: match event with
    | .authentication index => [("index", Lean.toJson index)]
    | .install id => [("configuration", Lean.toJson id)]
    | .stage id => [("specification", Lean.toJson id)]
    | .installGuard id => [("guard", Lean.toJson id)]
    | .installAt gateway id => [("configuration", Lean.toJson id), ("gateway", Lean.toJson (gatewayName gateway))]
    | .stageAt gateway id => [("specification", Lean.toJson id), ("gateway", Lean.toJson (gatewayName gateway))]
    | .installGuardAt gateway id => [("guard", Lean.toJson id), ("gateway", Lean.toJson (gatewayName gateway))]
    | .pause | .stageCheckpoint | .fencePrimary | .resume => []
    | .installCheckpoint executionNS => [("namespace", namespaceJson executionNS)]
    | .switchRoute actor gateway => [("actor", Lean.toJson (actorName actor)), ("gateway", Lean.toJson (gatewayName gateway))]
    | .open remote policy => [("remote", TCPHandshake.socketJson remote), ("policyPermitted", Lean.toJson policy)]
    | .write actor bytes => [("actor", Lean.toJson (actorName actor)), ("payloadHex", Lean.toJson (Import.EAPOL.bytesToHex bytes))]
    | .send actor count policy => [("actor", Lean.toJson (actorName actor)), ("count", Lean.toJson count), ("policyPermitted", Lean.toJson policy)]
    | .enableRecovery actor => [("actor", Lean.toJson (actorName actor))]
    | .enableAck actor => [("actor", Lean.toJson (actorName actor))]
    | .dispatchAck actor policy => [("actor", Lean.toJson (actorName actor)), ("policyPermitted", Lean.toJson policy)]
    | .advanceClock actor millis => [("actor", Lean.toJson (actorName actor)), ("millis", Lean.toJson millis)]
    | .timeout actor policy => [("actor", Lean.toJson (actorName actor)), ("policyPermitted", Lean.toJson policy)]
    | .read actor count => [("actor", Lean.toJson (actorName actor)), ("count", Lean.toJson count)]
    | .emitAck actor policy => [("actor", Lean.toJson (actorName actor)), ("policyPermitted", Lean.toJson policy)]
    | .copyPacket id | .dropPacket id => [("packet", Lean.toJson id)]
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

def recordsJson (state : Protocol.ConntrackLifecycle.State) : Lean.Json :=
  Lean.toJson (state.records.map fun record => Lean.Json.mkObj [
    ("zone", Lean.toJson record.entry.flow.originalZone), ("original", Import.PacketFields.headerJson record.entry.flow.original),
    ("translated", Import.PacketFields.headerJson (record.entry.flow.output .original)), ("seenReply", Lean.toJson record.seenReply)])

abbrev entryJson := TCPAdmissionJSON.entryJson
abbrev laneJson := TCPAdmissionJSON.laneJson
abbrev mssJson := TCPAdmissionJSON.mssJson
abbrev mssFields := TCPAdmissionJSON.mssFields
abbrev seenJson := TCPAdmissionJSON.seenJson
abbrev admissionJson := TCPAdmissionJSON.admissionJson

def transportFields (transport : Protocol.TCP.Checkpoint.Gateway) (transitions : Nat) : List (String × Lean.Json) := [
  ("records", recordsJson transport.tracker), ("confirmed", Check.ConntrackLifecycle.stateJson transport.tracker),
  ("admission", admissionJson transport.admission), ("historyTransitions", Lean.toJson transitions)]

def residentJson (resident : CampusTCPModel.Local) : Lean.Json :=
  Lean.Json.mkObj ([("configuration", Lean.toJson resident.configuration.id), ("guard", Lean.toJson resident.guard.id)] ++
    transportFields resident.transport resident.history.length)

def checkpointJson (checkpoint : CachedCheckpoint) : Lean.Json :=
  Lean.Json.mkObj ([("id", Lean.toJson checkpoint.id), ("stagedAt", Lean.toJson checkpoint.time)] ++
    transportFields checkpoint.snapshot.source checkpoint.snapshot.cut)

def transferJson (state : State input) : Lean.Json := Lean.Json.mkObj [
  ("paused", Lean.toJson state.assignmentPaused), ("installed", Lean.toJson state.installation.isSome),
  ("primarySealed", Lean.toJson state.primarySealed), ("primaryFenced", Lean.toJson state.primaryFenced),
  ("owners", Lean.Json.mkObj [("client", Lean.toJson (gatewayName state.owners.client)), ("server", Lean.toJson (gatewayName state.owners.server))]),
  ("routeEpoch", Lean.toJson state.routeEpoch), ("cache", (state.cache.map checkpointJson).getD .null),
  ("installation", (state.installation.map fun installed => Lean.Json.mkObj [
    ("index", Lean.toJson installed.time), ("checkpoint", Lean.toJson installed.checkpoint.id),
    ("stagedAt", Lean.toJson installed.checkpoint.time), ("historyTransitions", Lean.toJson installed.history.length)]).getD .null)]

def custodyJson (custody : Custody input) : Lean.Json := Lean.Json.mkObj [
  ("nextID", Lean.toJson custody.nextID), ("pending", Lean.toJson (custody.pending.map (·.id))),
  ("resolved", Lean.toJson (custody.resolutions.map fun record => Lean.Json.mkObj [
    ("packet", Lean.toJson record.item.id), ("kind", Lean.toJson (match record.disposition with
      | .assigned => "assigned" | .delivered => "delivered" | .dropped => "dropped"))])),
  ("copies", Lean.toJson (custody.items.countP (·.value.parent.isSome)))]

def packetJson (packet : Theory.PacketCustody.Item (Transit input)) : Lean.Json :=
  let (stage, source) := match packet.value.payload with
    | .ingress index _ => ("ingress", index)
    | .link index .. => ("link", index)
  Lean.Json.mkObj [("id", Lean.toJson packet.id), ("parent", Lean.toJson packet.value.parent),
    ("stage", Lean.toJson stage), ("source", Lean.toJson source),
    ("rawIPv4Hex", Lean.toJson (Import.EAPOL.bytesToHex packet.value.payload.bytes))]

def custodyAssuranceJson (custody : Custody input) : Lean.Json := Lean.Json.mkObj [
  ("scope", Lean.toJson "automatic-packet-custody"), ("status", Lean.toJson "checked"),
  ("pending", Lean.toJson custody.pending.length),
  ("assigned", Lean.toJson (custody.count .assigned)), ("delivered", Lean.toJson (custody.count .delivered)),
  ("dropped", Lean.toJson custody.dropped), ("copies", Lean.toJson (custody.items.countP (·.value.parent.isSome)))]

def stateJson (state : State input) : Lean.Json :=
  let stage := (connectionStage state.connection).json
  Lean.Json.mkObj ([
    ("after", Lean.toJson state.authentication), ("configuration", Lean.toJson state.configuration.id), ("guard", Lean.toJson state.guard.id),
    ("activePhase", field stage "activePhase"), ("passivePhase", field stage "passivePhase"),
    ("activeEstablishedAt", field stage "activeEstablishedAt"), ("passiveEstablishedAt", field stage "passiveEstablishedAt"),
    ("client", ((clientState state.connection).map TCPEndpoint.stateJson).getD .null),
    ("server", ((serverState state.connection).map TCPEndpoint.stateJson).getD .null),
    ("admissionPhase", Lean.toJson state.admission.phase.name), ("admissionObservations", Lean.toJson state.admission.observations.length),
    ("records", recordsJson state.tracker),
    ("outputs", Lean.toJson state.outputs.length), ("pendingTickets", Lean.toJson (state.work.pending.map (·.id))),
    ("services", Lean.toJson state.services.length), ("custody", custodyJson state.custody)] ++ if input.standby.isSome then [
      ("gateways", Lean.Json.mkObj [("primary", residentJson state.primary), ("standby", residentJson state.standby)]),
      ("transfer", transferJson state)] else [])

def producedKind : Produced active passive → String
  | .startup step _ _ => match step.event with | .activeOpen .. => "open" | _ => "startup"
  | .application _ step _ _ => match step.event with
    | .send .. => "send" | .emitAck .. => "emitAck" | .timeout .. => "retry" | .dispatchAck .. => "dispatchAck" | _ => "invalid"

def producedStartupOperation : Produced active passive → Option String
  | .startup step _ _ => some step.event.kind
  | .application .. => none

def attemptJson (step : TCP.ApplicationTrace.Step) : Option Lean.Json := do
  let recovery ← step.before.recovery
  let (kind, original, start, count) ← match step.event with
    | .send count _ => some ("original", some recovery.nextId, recovery.frontier, count)
    | .timeout _ => recovery.outstanding.head?.map (fun entry => ("retry", some entry.id, entry.start, entry.count))
    | .emitAck _ | .dispatchAck _ => some ("ack", none, recovery.frontier, 0)
    | _ => none
  return Lean.Json.mkObj [("kind", Lean.toJson kind), ("clockMillis", Lean.toJson recovery.now),
    ("originalID", Lean.toJson original), ("start", Lean.toJson start), ("count", Lean.toJson count)]

def producedJson (value : Produced active passive) (id : Nat) : Lean.Json := Lean.Json.mkObj ([
  ("id", Lean.toJson id), ("index", Lean.toJson value.time), ("actor", Lean.toJson (actorName value.actor)),
  ("kind", Lean.toJson (producedKind value)), ("startupOperation", Lean.toJson (producedStartupOperation value)),
  ("rawIPv4Hex", Lean.toJson (Import.EAPOL.bytesToHex value.output.bytes)), ("decoded", TCPReceive.decodedJson value.output.packet)] ++
  match value with
  | .startup .. => []
  | .application _ step _ _ => match attemptJson step with | none => [] | some attempt => [("attempt", attempt)])

def disposition : TCP.WireForwarding.Disposition → String
  | .forwarded => "forwarded" | .routeDrop => "routeDrop" | .ttlExpired => "ttlExpired"
  | .forwardDrop => "forwardDrop" | .lateDrop => "lateDrop"

def servedJson (value : Served input) (id : Nat) : Lean.Json :=
  Lean.Json.mkObj ([
    ("id", Lean.toJson id), ("index", Lean.toJson value.time), ("ticket", Lean.toJson value.ticket.id),
    ("outputID", Lean.toJson value.ticket.value.outputIndex), ("actor", Lean.toJson (actorName value.ticket.value.produced.actor)),
    ("sourceKind", Lean.toJson (producedKind value.ticket.value.produced)), ("inputHex", Lean.toJson (Import.EAPOL.bytesToHex value.ticket.value.source.bytes)),
    ("output", TCPEndpoint.outputJson (value.evidence.output.map (·.asInput))),
    ("disposition", Lean.toJson (match value.evidence.processing with | none => "earlyDrop" | some p => disposition p.outcome.disposition)),
    ("direction", Lean.toJson (value.evidence.processing.map (fun p => directionName p.prepared.attachment.direction))),
    ("nextHop", Lean.toJson (value.evidence.processing.bind (fun p => p.outcome.nextHop))),
    ("checks", Lean.Json.mkObj [("forward", Lean.toJson value.evidence.checks.forward.passed),
      ("ingress", Lean.toJson value.evidence.checks.guard.passed), ("coverage", Lean.toJson (CampusTCPService.coverage input.context value.ticket.value.source))]),
    ("observationsMatch", Lean.toJson value.observed), ("routeRoleMatch", Lean.toJson value.routeMatched)] ++
    if input.standby.isSome then [("gateway", Lean.toJson (gatewayName value.ticket.value.gateway)),
      ("routeEpoch", Lean.toJson value.ticket.value.routeEpoch)] else [])

def decisionJson (step : CampusTCPModel.Step input) : Lean.Json :=
  match step.result.application, step.result.startup with
  | some (_, applied), _ => TCPEndpoint.decisionJson applied.result.decision
  | none, some startup => field (startup.json) "decision"
  | none, none => if step.result.supported then Lean.Json.mkObj [
      ("kind", Lean.toJson "accepted"), ("operation", Lean.toJson (eventKind step.event))]
    else Lean.Json.mkObj [("kind", Lean.toJson "unsupported"), ("reason", Lean.toJson step.result.decision)]

def stepJson (step : CampusTCPModel.Step input) : Lean.Json := Lean.Json.mkObj ([
  ("index", Lean.toJson step.before.time), ("event", eventJson step.event), ("before", stateJson step.before),
  ("supported", Lean.toJson step.result.supported), ("passed", Lean.toJson step.result.passed),
  ("decision", decisionJson step), ("output", TCPEndpoint.outputJson (step.result.output.map (·.output))),
  ("decodedInput", match step.result.receipt with | none => .null | some receipt => TCPReceive.decodedJson receipt.received.packet),
  ("readHex", Lean.toJson (Import.EAPOL.bytesToHex step.result.read)),
  ("service", (step.result.service.map (fun value => servedJson value step.before.services.length)).getD .null),
  ("state", stateJson step.result.state)] ++
    match step.result.application with | none => [] | some (_, applied) => TCPEndpoint.receiveFields applied)

def assumptions : List String := [
  "The result concerns the selected Lean gateway model, not Linux TCP tracker refinement or native installation.",
  "The caller supplies current interface lifetimes, principal/header ownership, local sequence choices, and IP size evidence.",
  "EAP method acceptance and credential integrity remain supplied evidence. TLS cryptography is outside this model.",
  "Imported policy, NAT, and routing snapshots describe the exclusive selected hook sequence.",
  "The endpoint output policy is local permission. Current gateway permission comes from actual installed policy checks.",
  "The selected TCP history accepts MSS, NOP, and EOL at startup; application data uses no options.",
  "Optional data recovery uses explicit local clocks, one-MSS unique flight, and at most two retries per outstanding original segment.",
  "Fast recovery, persist, replacement, close processing, other options, and unbounded sequence reuse remain outside the selected history.",
  "Local millisecond readings do not prove native time or coherence with credential expiry.",
  "Every endpoint output and gateway emission allocates packet custody. Assignment and delivery consume actual pending packets.",
  "Copies and link drops use explicit packet identities. An omitted action leaves its packet pending and does not prove loss.",
  "Actual gateway output supplies receiver bytes in the modeled timeline. Bounded TCP progress, physical delivery, and connection-instance identity remain open.",
  "Logoff and checked denial prevent later gateway output. They do not erase bytes already received or buffered.",
  "Native TCP migration, automatic failure recovery, native Wi-Fi enforcement, and the full campus demonstration remain open."]

def sources : List Standards.Source := [
  ⟨"Transmission Control Protocol", "RFC 9293", "3.4 and 3.10.7", "https://www.rfc-editor.org/rfc/rfc9293.html#section-3.10.7"⟩,
  ⟨"Computing TCP's Retransmission Timer", "RFC 6298", "2, 3, and 5", "https://www.rfc-editor.org/rfc/rfc6298.html#section-5"⟩,
  ⟨"TCP Congestion Control", "RFC 5681", "3", "https://www.rfc-editor.org/rfc/rfc5681.html#section-3"⟩,
  ⟨"Extensible Authentication Protocol (EAP)", "RFC 3748", "4", "https://www.rfc-editor.org/rfc/rfc3748.html#section-4"⟩,
  ⟨"Linux netfilter NAT", "v6.8", "nf_nat_packet", Protocol.NetfilterNAT.sourceURL⟩,
  ⟨"Linux connection tracking", "v6.8", "ordinary attachment and confirmation", Protocol.ConntrackLifecycle.sourceURL⟩]

def ackSources : List Standards.Source := [
  ⟨"Transmission Control Protocol", "RFC 9293", "3.8.6.2.2 and 3.8.6.3",
    "https://www.rfc-editor.org/rfc/rfc9293.html#section-3.8.6.2.2"⟩,
  ⟨"TCP Congestion Control", "RFC 5681", "4.2", "https://www.rfc-editor.org/rfc/rfc5681.html#section-4.2"⟩]

def renderJson (report : CampusTCPModel.Report input events)
    (application : ApplicationStatus report := applicationStatus report)
    (transfer : TransferStatus report := transferStatus report)
    (ack : AckStatus report := ackStatus report)
    (gaps : ReceiveGapStatus report := receiveGapStatus report)
    (sparse : SparseStatus report := sparseStatus report) : Lean.Json := Lean.Json.mkObj ([
  ("scope", Lean.toJson "campus-tcp-application-path"), ("supported", Lean.toJson report.supported),
  ("compliant", Lean.toJson report.compliant), ("inputEvents", Lean.toJson events.length), ("evaluatedEvents", Lean.toJson report.steps.length),
  ("applicationAssurance", application.json),
  ("custodyAssurance", custodyAssuranceJson report.final.custody),
  ("initial", stateJson input.initial), ("steps", Lean.toJson (report.steps.map stepJson)), ("final", stateJson report.final),
  ("outputs", Lean.toJson (report.final.outputs.zipIdx.map fun (value, id) => producedJson value id)),
  ("packets", Lean.toJson ((report.final.custody.items.mergeSort (fun first second => first.id ≤ second.id)).map packetJson)),
  ("services", Lean.toJson (report.final.services.zipIdx.map fun (value, id) => servedJson value id)),
  ("reads", Lean.toJson (report.steps.filterMap fun step => match step.event, step.result.application with
    | .read actor _, some (_, applied) => match applied.result.decision with
      | .accepted (.read _) => some (Lean.Json.mkObj [("index", Lean.toJson step.before.time), ("actor", Lean.toJson (actorName actor)),
          ("readHex", Lean.toJson (Import.EAPOL.bytesToHex step.result.read))])
      | _ => none
    | _, _ => none)),
  ("remainingEvents", Lean.toJson (report.remaining.map eventJson)),
  ("assumptions", Lean.toJson (assumptions ++ if ackEnabled report then [
    "ACK assurance covers only the enabled endpoints and timely local generation, with an inclusive 499-ms delayed bound.",
    "Receive-window suppression applies to all enabled endpoint output. Scheduling, native clocks, and eventual delivery remain open."] else [])),
  ("sources", Lean.toJson ((sources ++ if ackEnabled report then ackSources else []).map fun source => Lean.Json.mkObj [
    ("document", Lean.toJson source.document), ("version", Lean.toJson source.version),
    ("clause", Lean.toJson source.clause), ("url", Lean.toJson source.url)]))] ++
    (if input.standby.isSome then [("transferAssurance", transfer.json)] else []) ++
    (if ackEnabled report then [("ackAssurance", ack.json)] else []) ++
    (if receiveGapSeen report then [("receiveGapAssurance", gaps.json)] else []) ++
    (if sparseSeen report then [("sparseAssurance", sparse.json)] else []))

def render (report : CampusTCPModel.Report input events)
    (application : ApplicationStatus report := applicationStatus report)
    (transfer : TransferStatus report := transferStatus report)
    (ack : AckStatus report := ackStatus report)
    (gaps : ReceiveGapStatus report := receiveGapStatus report)
    (sparse : SparseStatus report := sparseStatus report) : String :=
  (if report.compliant then "CAMPUS TCP MODEL COMPLIANT\n" else "CAMPUS TCP MODEL NOT COMPLIANT\n") ++
    (renderJson report application transfer ack gaps sparse).pretty

end Netlib.Check.CampusTCP
