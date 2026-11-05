import Netlib.Check.AttachmentCampus

/-!
# Attachment-campus observation format

Native interface metadata stays separate from packet bytes and authenticated subject names.
The parser retains original JSON and rejects unsupported fields.
-/

namespace Netlib.Check.AttachmentCampus

open Packet Protocol
open StatefulFailover (Gateway)

structure Bundle where
  input : Input
  timeline : List Observation

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def optional (parse : Lean.Json → Except String α) (json : Lean.Json) : Except String (Option α) :=
  match json with
  | .null => return none
  | value => some <$> parse value

private def gateway (json : Lean.Json) : Except String Gateway := do
  match ← json.getStr? with
  | "primary" => return .primary
  | "standby" => return .standby
  | value => throw s!"Unsupported attachment gateway: {value}."

private def direction (json : Lean.Json) : Except String FlowNAT.Direction := do
  match ← json.getStr? with
  | "original" => return .original
  | "reply" => return .reply
  | value => throw s!"Unsupported attachment direction: {value}."

private def source (json : Lean.Json) : Except String Source := do
  let bytes ← Import.EAPOL.bytesFromHex (← json.getStr?)
  match decoded : UDP.decodeIPv4 bytes with
  | .error reason => throw reason
  | .ok packet => return ⟨bytes, packet, decoded⟩

private def traffic (json : Lean.Json) : Except String Match :=
  DataPlane.Config.parseTrafficSelection json.compress

private def maintenance (json : Lean.Json) : Except String Maintenance := do
  Import.PacketFields.fields json ["ingress", "traffic"]
  return ⟨← Import.NftablesIngress.interfaceFromJson (← json.getObjVal? "ingress"), ← traffic (← json.getObjVal? "traffic")⟩

private def parseProbe (json : Lean.Json) : Except String Probe := do
  Import.PacketFields.fields json ["type", "gateway", "ingress", "direction", "rawIPv4", "guard", "observed", "states"]
  let states ← json.getObjVal? "states"
  Import.PacketFields.fields states ["primary", "standby"]
  return ⟨← gateway (← json.getObjVal? "gateway"),
    ← Import.NftablesIngress.interfaceFromJson (← json.getObjVal? "ingress"),
    ← direction (← json.getObjVal? "direction"), ← source (← json.getObjVal? "rawIPv4"),
    ← (← json.getObjVal? "guard").getBool?,
    ← Check.WireForwarding.PacketObservation.fromJson (← json.getObjVal? "observed"),
    ← optional Import.ConntrackNetlink.Snapshot.fromJson (← states.getObjVal? "primary"),
    ← optional Import.ConntrackNetlink.Snapshot.fromJson (← states.getObjVal? "standby")⟩

private def parseObservation (json : Lean.Json) (index : Nat) : Except String Observation := do
  let event ← match ← (← json.getObjVal? "type").getStr? with
    | "authentication" => do
      Import.PacketFields.fields json ["type", "event"]
      pure (.authentication (← (← json.getObjVal? "event").getNat?))
    | "network" => do
      Import.PacketFields.fields json ["type", "event", "ingress", "guard"]
      pure (.network (← (← json.getObjVal? "event").getNat?)
        (← optional Import.NftablesIngress.interfaceFromJson (← json.getObjVal? "ingress"))
        (← optional Lean.Json.getBool? (← json.getObjVal? "guard")))
    | "withdraw" => do
      Import.PacketFields.fields json ["type"]
      pure .withdraw
    | "reset" => do
      Import.PacketFields.fields json ["type"]
      pure .reset
    | "stage" => do
      Import.PacketFields.fields json ["type", "attachment"]
      pure (.stage (← (← json.getObjVal? "attachment").getStr?))
    | "maintenance" => do
      Import.PacketFields.fields json ["type", "entries"]
      pure (.maintenance (← (← (← json.getObjVal? "entries").getArr?).toList.mapM maintenance))
    | "installGuard" => do
      Import.PacketFields.fields json ["type", "guard"]
      pure (.installGuard (← (← json.getObjVal? "guard").getStr?))
    | "protect" => do
      Import.PacketFields.fields json ["type"]
      pure .protect
    | "probe" => .probe <$> parseProbe json
    | value => throw s!"Unsupported attachment timeline operation: {value}."
  return ⟨index, event, json⟩

def Bundle.fromJson (json : Lean.Json) : Except String Bundle := do
  Import.PacketFields.fields json ["schema", "application", "authentication", "intent", "handoff", "namespaces",
    "authenticationPort", "live", "attachments", "guards", "timeline"]
  require ((← (← json.getObjVal? "schema").getNat?) == 1) "Use attachment campus schema 1."
  -- Reuse the old input parser; its timeline is discarded by this adapter.
  let base ← CampusDeployment.Bundle.fromJson (Lean.Json.mkObj [
    ("schema", ← json.getObjVal? "schema"), ("application", ← json.getObjVal? "application"),
    ("authentication", ← json.getObjVal? "authentication"), ("intent", ← json.getObjVal? "intent"),
    ("handoff", ← json.getObjVal? "handoff"),
    ("timeline", Lean.toJson [Lean.Json.mkObj [("type", Lean.toJson "withdraw")]])])
  let namespaces ← json.getObjVal? "namespaces"
  Import.PacketFields.fields namespaces ["primary", "standby"]
  let primary ← Import.NftablesIngress.namespaceFromJson (← namespaces.getObjVal? "primary")
  let standby ← Import.NftablesIngress.namespaceFromJson (← namespaces.getObjVal? "standby")
  require (decide (primary ≠ standby)) "Gateway namespaces must identify distinct lifetimes."
  let authenticationPort ← Import.NftablesIngress.interfaceFromJson (← json.getObjVal? "authenticationPort")
  let live ← (← (← json.getObjVal? "live").getArr?).toList.mapM Import.NftablesIngress.interfaceFromJson
  require (decide live.Nodup && decide (authenticationPort ∈ live)) "Use unique current interfaces, including the authentication port."
  let mut specifications : List Specification := []
  for value in ← (← json.getObjVal? "attachments").getArr? do
    Import.PacketFields.fields value ["id", "gateway", "ingress", "direction", "traffic"]
    let id ← (← value.getObjVal? "id").getStr?
    require (!id.isEmpty && !(specifications.any (·.id == id))) "Attachment IDs must be nonempty and unique."
    let selected ← gateway (← value.getObjVal? "gateway")
    let ingress ← Import.NftablesIngress.interfaceFromJson (← value.getObjVal? "ingress")
    let ns := match selected with | .primary => primary | .standby => standby
    require (decide (ingress.ns = ns) && decide (ingress ∈ live)) "An attachment requires a current interface in its gateway namespace."
    specifications := specifications ++ [⟨id, selected, ingress, ← direction (← value.getObjVal? "direction"),
      ← traffic (← value.getObjVal? "traffic")⟩]
  require (!specifications.isEmpty) "Declare protected application ingress classes."
  let mut guards : List GuardConfig := []
  for value in ← (← json.getObjVal? "guards").getArr? do
    Import.PacketFields.fields value ["id", "gateway", "namespace", "bindings", "ruleset"]
    let id ← (← value.getObjVal? "id").getStr?
    require (!id.isEmpty && !(guards.any (·.id == id))) "Guard IDs must be nonempty and unique."
    let selected ← gateway (← value.getObjVal? "gateway")
    let ns ← Import.NftablesIngress.namespaceFromJson (← value.getObjVal? "namespace")
    let expected := match selected with | .primary => primary | .standby => standby
    require (decide (ns = expected)) "A guard namespace differs from its gateway lifetime."
    let bindings ← Import.NftablesIngress.bindingsFromJson ns (← value.getObjVal? "bindings")
    let source ← Import.NftablesIngress.Snapshot.fromJson ns bindings (← value.getObjVal? "ruleset")
    guards := guards ++ [⟨id, selected, source⟩]
  let input : Input := ⟨base.input, (fun gateway => match gateway with | .primary => primary | .standby => standby),
    authenticationPort, live, specifications, guards⟩
  require (input.initial.check input) "Initial interface lifetimes conflict within a gateway namespace."
  let values ← (← json.getObjVal? "timeline").getArr?
  let mut timeline := []
  for index in [:values.size] do
    timeline := timeline ++ [← (parseObservation values[index]! index).mapError (s!"/timeline/{index}: " ++ ·)]
  return ⟨input, timeline⟩

def Bundle.parse (text : String) : Except String Bundle := do Bundle.fromJson (← Import.Json.parse text)

def Bundle.check (bundle : Bundle) (budget : Nat := 1000000) : Except String (Report bundle.input budget bundle.timeline) :=
  Replay.audit (replay bundle.input budget) bundle.input.initial bundle.timeline

private def gatewayName : Gateway → String
  | .primary => "primary" | .standby => "standby"

private def namespaceJson (value : IngressAttachment.NamespaceRef) : Lean.Json :=
  Lean.Json.mkObj [("id", Lean.toJson value.id), ("birth", Lean.toJson value.birth)]

private def interfaceJson (value : IngressAttachment.InterfaceRef) : Lean.Json := Lean.Json.mkObj [
  ("namespace", namespaceJson value.ns), ("ifindex", Lean.toJson value.ifindex.val), ("birth", Lean.toJson value.birth)]

private def originJson (value : IngressAttachment.Origin) : Lean.Json := Lean.Json.mkObj [
  ("principal", Lean.toJson value.principal), ("afterAuthentication", Lean.toJson value.after),
  ("round", Lean.toJson value.round), ("authenticationPort", interfaceJson value.authenticationPort)]

private def ownerJson : Option IngressAttachment.OwnedBinding → Lean.Json
  | none => .null
  | some owner => Lean.Json.mkObj [("origin", originJson owner.origin),
      ("original", Import.PacketFields.headerJson owner.entry.flow.original)]

private def stateJson (input : Input) (state : State) : Lean.Json := Lean.Json.mkObj [
  ("authenticationConsumed", Lean.toJson state.authentication), ("networkConsumed", Lean.toJson state.network),
  ("guardedSuffix", Lean.toJson state.enforced), ("resetObserved", Lean.toJson state.resetObserved),
  ("authorized", Lean.toJson (current input state).state.auth.authorized),
  ("applicationPermitted", Lean.toJson ((current input state).state.session.permits input.campus.authentication.context input.campus.application)),
  ("withdrawn", Lean.toJson state.deployment.withdrawn),
  ("archivedPrimary", (state.deployment.archive.map Check.ConntrackLifecycle.stateJson).getD .null),
  ("primarySnapshot", Check.ConntrackLifecycle.stateJson state.deployment.handoff.gateways.primary),
  ("standby", Check.ConntrackLifecycle.stateJson state.deployment.handoff.gateways.standby),
  ("live", Lean.toJson (state.live.map interfaceJson)),
  ("historicalOwners", Lean.Json.mkObj [("primary", ownerJson (state.owners .primary)), ("standby", ownerJson (state.owners .standby))]),
  ("attachments", Lean.toJson (state.attachments.map fun attachment => Lean.Json.mkObj [
    ("id", Lean.toJson attachment.specification), ("origin", originJson attachment.value.origin),
    ("ingress", interfaceJson attachment.value.ingress)])),
  ("pendingIDs", Lean.toJson (state.deployment.handoff.work.pending.map (·.id))),
  ("completedIDs", Lean.toJson (state.deployment.handoff.work.completed.map (·.id))),
  ("epoch", Lean.toJson state.deployment.handoff.gateways.epoch)]

private def gateJson (value : Gate input before) : Lean.Json := Lean.Json.mkObj [
  ("gateway", Lean.toJson (gatewayName value.checked.gateway)), ("ingress", interfaceJson value.checked.ingress),
  ("actualAllowed", Lean.toJson value.checked.decision), ("observedAllowed", Lean.toJson value.observed),
  ("equivalent", Lean.toJson value.checked.guardEquivalent), ("applicationCovered", Lean.toJson value.checked.covered),
  ("matched", Lean.toJson value.passed)]

private def detailJson : Detail input before → List (String × Lean.Json)
  | .simple name => [("type", Lean.toJson name)]
  | .authentication evidence => [("type", Lean.toJson "authentication"),
      ("event", Lean.toJson before.authentication), ("authenticationMatched", Lean.toJson evidence.finding.passed)]
  | .ordinary evidence gate => [("type", Lean.toJson "network"), ("event", Lean.toJson before.network),
      ("guard", (gate.map gateJson).getD .null), ("ordinaryExecuted", Lean.toJson true),
      ("ordinaryPolicyMatched", Lean.toJson evidence.certificate.passed),
      ("expected", match evidence.model.served, evidence.model.established with
        | some served, _ => Check.WireForwarding.outcomeToJson served.outcome
        | none, some established => Check.WireForwarding.outcomeToJson established.outcome
        | none, none => .null)]
  | .rejectedServe evidence => [("type", Lean.toJson "earlyRejectedServe"),
      ("event", Lean.toJson before.network), ("guard", gateJson evidence.gate),
      ("ordinaryExecuted", Lean.toJson false), ("expected", .null), ("retiredID", Lean.toJson evidence.dropped.ticket.id)]
  | .probe _ gate execution => [("type", Lean.toJson "probe"), ("guard", gateJson gate),
      ("ordinaryExecuted", Lean.toJson (match execution with | .rejected => false | .processed .. => true)),
      ("expected", match execution with
        | .rejected => .null
        | .processed _ _ result _ _ => Check.WireForwarding.outcomeToJson result.outcome)]

def assumptions : List String := [
  "The controller binds the observed EAP subject and round to the declared authentication port and separate data interfaces.",
  "Namespace and interface lifetime labels describe authentic creation and move observations within one capture.",
  "Process birth comparisons assume the collector and workers share the initial time namespace with unchanged zero clock offsets.",
  "Numeric iif matches kernel ingress metadata; names resolve against contemporaneous same-namespace interface inventories.",
  "Installed rules remain active until their explicit replacement, and all packet observations have the declared linearization.",
  "The guard runs at raw prerouting before ordinary conntrack; allow continues into the existing policy and NAT pipeline.",
  "The guarded suffix follows the explicit empty-table reset; the unsafe prelude has no attachment security claim.",
  "Maintenance classes are disjoint from application classes and use the separately observed replication socket bindings.",
  "Selected whole IPv4 UDP datagrams have no fragment, bridge, tunnel, helper, offload, or earlier tracking bypass.",
  "Ordinary connection lifetime, counters, and authentic observations need the native evidence checks and stated isolation assumptions.",
  "A shared trusted port does not distinguish copied packet bytes; cryptographic data provenance needs separate lower-layer protection.",
  "The withdrawn primary table is historical; later operations cannot query or process its live kernel state."]

def Report.renderJson (report : Report input budget observations) : Lean.Json := Lean.Json.mkObj [
  ("scope", Lean.toJson "checked-interface-bound-campus-suffix"), ("compliant", Lean.toJson (Report.compliant report)),
  ("complete", Lean.toJson report.complete), ("eventCount", Lean.toJson report.findings.length),
  ("subject", Lean.toJson input.campus.authentication.context.consumer),
  ("assumptions", Lean.toJson assumptions), ("final", stateJson input report.final),
  ("findings", Lean.toJson (report.findings.map fun finding => Lean.Json.mkObj (
    [("source", Lean.toJson s!"/timeline/{finding.observation.index}"), ("matched", Lean.toJson finding.passed),
      ("before", stateJson input finding.result.before), ("after", stateJson input finding.result.state)] ++
      detailJson finding.result.transition.detail)))]

def Report.render (report : Report input budget observations) : String :=
  (if Report.compliant report then "ATTACHMENT CAMPUS MATCHES\n" else "ATTACHMENT CAMPUS MISMATCH\n") ++ report.renderJson.pretty

end Netlib.Check.AttachmentCampus
