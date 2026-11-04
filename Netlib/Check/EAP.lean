import Netlib.Import.EAPOL
import Netlib.Import.PacketFields
import Netlib.Protocol.EAPSession
import Netlib.Standards.Basic

/-!
# EAP session observation checks

Ethernet roles select protocol events; observations never set authorization.
The method layer supplies separately bound identity evidence.
Raw framing, logical authorization, and application admission have distinct scopes.
-/

namespace Netlib.Check.EAP

open Protocol
abbrev State := Protocol.EAPSession.State
abbrev Event := Protocol.EAPSession.Event

structure Binding where
  peer : Import.EAPOL.MAC
  authenticator : Import.EAPOL.MAC

def group : Import.EAPOL.MAC := ⟨1, 128, 194, 0, 0, 3⟩

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

def frameEvent (binding : Binding) (frame : Import.EAPOL.EthernetFrame) : Except String Event := do
  let peer := frame.source == binding.peer
  let authenticator := frame.source == binding.authenticator
  require (peer || authenticator) "The EAPOL source does not match the declared peer or authenticator."
  require (frame.destination == group ||
    (peer && frame.destination == binding.authenticator) ||
    (authenticator && frame.destination == binding.peer)) "The EAPOL destination does not match the selected link."
  match frame.frame.body with
  | .start =>
    require peer "Only the selected peer can send EAPOL-Start in this profile."
    return .authentication .start
  | .logoff =>
    require peer "Only the selected peer can send EAPOL-Logoff in this profile."
    return .authentication .logoff
  | .eap decoded =>
    if let some kind := decoded.packet.kind? then
      require (0 < kind.toNat && kind.toNat < 254)
        "The selected EAP session profile excludes reserved and expanded method types."
    match decoded.packet with
    | .response .. =>
      require peer "An EAP Response must come from the selected peer."
      return .authentication (.peer decoded.packet)
    | _ =>
      require authenticator "EAP Requests and terminal packets must come from the selected authenticator."
      return .authentication (.server decoded.packet)

structure Observation where
  index : Nat
  event : Event
  authorized : Option Bool
  accepted : Option Bool
  frame : Option Import.EAPOL.EthernetFrame
  raw : Lean.Json

def expectedRequest (event : Event) (after : State) : Option Bool :=
  match event with
  | .application (.request scope) => some (decide (after.session.admitted = some scope))
  | _ => none

def AuthorizationMatches (observation : Observation) (after : State) : Prop :=
  ∀ value, observation.authorized = some value → after.auth.authorized = value

def authorizationMatches (observation : Observation) (after : State) : Bool :=
  match observation.authorized with
  | none => true
  | some value => decide (after.auth.authorized = value)

theorem authorizationMatches_correct (observation : Observation) (after : State) :
    authorizationMatches observation after = true ↔ AuthorizationMatches observation after := by
  cases observed : observation.authorized <;> simp [authorizationMatches, AuthorizationMatches, observed]

def Matches (observation : Observation) (after : State) : Prop :=
  AuthorizationMatches observation after ∧ observation.accepted = expectedRequest observation.event after

structure Finding where
  observation : Observation
  result : State
  passed : Bool

def finding (observation : Observation) (after : State) : Finding :=
  ⟨observation, after, authorizationMatches observation after &&
    decide (observation.accepted = expectedRequest observation.event after)⟩

theorem finding_correct (observation : Observation) (after : State) :
    (finding observation after).passed = true ↔ Matches observation after := by
  simp [finding, Matches, authorizationMatches_correct]

theorem expectedRequest_admitted (event : Event) (after : State)
    (accepted : expectedRequest event after = some true) :
    ∃ scope, event = .application (.request scope) ∧ after.session.admitted = some scope := by
  cases event with
  | authentication => simp [expectedRequest] at accepted
  | close => simp [expectedRequest] at accepted
  | application action =>
    cases action with
    | install => simp [expectedRequest] at accepted
    | advance => simp [expectedRequest] at accepted
    | revoke => simp [expectedRequest] at accepted
    | request scope => exact ⟨scope, rfl, by simpa [expectedRequest] using accepted⟩

def Agreement (context : Context) : State → List Observation → Prop
  | _, [] => True
  | before, observation :: observations =>
    let after := Protocol.EAPSession.step context before observation.event
    Matches observation after ∧ Agreement context after observations

inductive Trace (context : Context) : State → List Finding → State → Prop
  | nil (state : State) : Trace context state [] state
  | cons {before final : State} {head : Finding} {tail : List Finding}
      (computed : Protocol.EAPSession.step context before head.observation.event = head.result)
      (rest : Trace context head.result tail final) : Trace context before (head :: tail) final

theorem Trace.safe {context : Context} {initial final : State} {findings : List Finding}
    (trace : Trace context initial findings final) (safe : initial.Safe context) :
    final.Safe context ∧ ∀ finding ∈ findings, finding.result.Safe context := by
  induction trace with
  | nil => exact ⟨safe, by simp⟩
  | @cons before final head tail computed rest ih =>
    have next : head.result.Safe context := by
      rw [← computed]
      exact Protocol.EAPSession.step_safe _ _ _ safe
    obtain ⟨last, each⟩ := ih next
    refine ⟨last, ?_⟩
    intro finding member
    rcases List.mem_cons.mp member with rfl | member
    · exact next
    · exact each finding member

theorem Trace.matches {context : Context} {initial final : State} {findings : List Finding}
    (trace : Trace context initial findings final)
    (agreement : Agreement context initial (findings.map Finding.observation)) :
    ∀ finding ∈ findings, Matches finding.observation finding.result := by
  induction trace with
  | nil => simp
  | cons computed rest ih =>
    simp only [List.map_cons, Agreement, computed] at agreement
    intro finding member
    rcases List.mem_cons.mp member with rfl | member
    · exact agreement.1
    · exact ih agreement.2 finding member

structure Report (context : Context) (initial : State) (observations : List Observation) where
  final : State
  findings : List Finding
  covered : findings.map Finding.observation = observations
  trace : Trace context initial findings final
  correct : findings.all Finding.passed = true ↔ Agreement context initial observations

def audit (context : Context) (initial : State) : (observations : List Observation) → Report context initial observations
  | [] => ⟨initial, [], rfl, .nil initial, by simp [Agreement]⟩
  | observation :: observations =>
    let after := Protocol.EAPSession.step context initial observation.event
    let tail := audit context after observations
    ⟨tail.final, finding observation after :: tail.findings,
      by simp only [List.map_cons, finding, tail.covered], .cons rfl tail.trace, by
        simp only [List.all_cons, Bool.and_eq_true, finding_correct, tail.correct, Agreement]
        rfl⟩

namespace Report

def compliant (report : Report context initial observations) : Bool := report.findings.all Finding.passed

theorem compliant_iff (report : Report context initial observations) :
    report.compliant = true ↔ Agreement context initial observations := report.correct

theorem observed_authorization_ready (report : Report context initial observations)
    (safe : initial.Safe context) (compliant : report.compliant = true) :
    ∀ finding ∈ report.findings, finding.observation.authorized = some true →
      EAPAuth.State.Ready (Protocol.EAPSession.authContext context) finding.result.auth := by
  have agreement := report.compliant_iff.mp compliant
  rw [← report.covered] at agreement
  have matched := report.trace.matches agreement
  have eachSafe := (report.trace.safe safe).2
  intro finding member authorized
  exact (eachSafe finding member).1 ((matched finding member).1 true authorized)

theorem observed_admission_valid (report : Report context initial observations)
    (safe : initial.Safe context) (compliant : report.compliant = true) :
    ∀ finding ∈ report.findings, finding.observation.accepted = some true →
      ∃ scope, finding.observation.event = .application (.request scope) ∧
        finding.result.session.admitted = some scope ∧ Session.Valid context finding.result.session scope ∧
        EAPAuth.State.Ready (Protocol.EAPSession.authContext context) finding.result.auth := by
  have agreement := report.compliant_iff.mp compliant
  rw [← report.covered] at agreement
  have matched := report.trace.matches agreement
  have eachSafe := (report.trace.safe safe).2
  intro finding member accepted
  obtain ⟨scope, event, admitted⟩ := expectedRequest_admitted finding.observation.event finding.result
    ((matched finding member).2.symm.trans accepted)
  obtain ⟨authSafe, coupled, sessionSafe⟩ := eachSafe finding member
  have valid := (Session.permits_iff _ _ _).mp (sessionSafe scope admitted)
  have authorized : finding.result.auth.authorized = true := by
    rw [← coupled]
    exact valid.1
  exact ⟨scope, event, admitted, valid, authSafe authorized⟩

end Report

structure Input where
  context : Context
  binding : Binding
  observations : List Observation
  raw : Lean.Json

private def text (json : Lean.Json) (field : String) : Except String String := do
  (← json.getObjVal? field).getStr?

private def optionalBool (json : Lean.Json) : Except String (Option Bool) :=
  match json with
  | .null => .ok none
  | json => some <$> json.getBool?

private def optionalString (json : Lean.Json) : Except String (Option String) :=
  match json with
  | .null => .ok none
  | json => some <$> json.getStr?

private def byte (json : Lean.Json) : Except String UInt8 := do
  let value ← json.getNat?
  require (value < 256) "An EAP method must fit in one byte."
  return UInt8.ofNat value

private def parseScope (json : Lean.Json) : Except String Scope := do
  Import.PacketFields.fields json ["resource", "operation"]
  let resource ← text json "resource"
  let operation ← text json "operation"
  require (!resource.isEmpty && !operation.isEmpty) "Scope names must not be empty."
  return ⟨resource, operation⟩

private def parseCredential (json : Lean.Json) : Except String Credential := do
  Import.PacketFields.fields json ["issuer", "subject", "audience", "scopes", "expiresAt", "integrity"]
  return ⟨← text json "issuer", ← text json "subject", ← text json "audience",
    ← (← (← json.getObjVal? "scopes").getArr?).toList.mapM parseScope,
    ← (← json.getObjVal? "expiresAt").getNat?, ← (← json.getObjVal? "integrity").getBool?⟩

def Input.fromJson (json : Lean.Json) : Except String Input := do
  Import.PacketFields.fields json ["schema", "context", "link", "events"]
  require ((← (← json.getObjVal? "schema").getNat?) == 1) "Use EAP session schema 1."
  let contextJson ← json.getObjVal? "context"
  Import.PacketFields.fields contextJson ["consumer", "producer", "issuer"]
  let context : Context := ⟨← text contextJson "consumer", ← text contextJson "producer", ← text contextJson "issuer"⟩
  require (![context.consumer, context.producer, context.issuer].any String.isEmpty) "Context names must not be empty."
  let link ← json.getObjVal? "link"
  Import.PacketFields.fields link ["peer", "authenticator"]
  let binding : Binding := ⟨← Import.EAPOL.MAC.parse (← text link "peer"),
    ← Import.EAPOL.MAC.parse (← text link "authenticator")⟩
  require (binding.peer != binding.authenticator && binding.peer.a.toNat % 2 == 0 && binding.authenticator.a.toNat % 2 == 0)
    "Bind distinct unicast peer and authenticator MAC addresses."
  let values ← (← json.getObjVal? "events").getArr?
  let mut observations := []
  let mut now := 0
  let mut frames := 0
  for index in [:values.size] do
    let value := values[index]!
    let kind ← text value "type"
    let mut frame := none
    let mut accepted := none
    let event ← match kind with
      | "frame" => do
        Import.PacketFields.fields value ["type", "raw", "authorized"]
        let decoded ← Import.EAPOL.parseHex (← text value "raw")
        frame := some decoded
        frames := frames + 1
        frameEvent binding decoded
      | "method" => do
        Import.PacketFields.fields value ["type", "round", "subject", "method", "accepted", "source", "authorized"]
        pure (.authentication (.method ⟨← (← value.getObjVal? "round").getNat?, ← text value "subject",
          ← byte (← value.getObjVal? "method"), ← (← value.getObjVal? "accepted").getBool?,
          ← optionalString (← value.getObjVal? "source")⟩))
      | "install" => do
        Import.PacketFields.fields value ["type", "credential", "authorized"]
        pure (.application (.install (← parseCredential (← value.getObjVal? "credential"))))
      | "advance" => do
        Import.PacketFields.fields value ["type", "now", "authorized"]
        let next ← (← value.getObjVal? "now").getNat?
        require (now ≤ next) "The session clock cannot move backward."
        now := next
        pure (.application (.advance next))
      | "request" => do
        Import.PacketFields.fields value ["type", "scope", "accepted", "authorized"]
        accepted := some (← (← value.getObjVal? "accepted").getBool?)
        pure (.application (.request (← parseScope (← value.getObjVal? "scope"))))
      | "revoke" => do
        Import.PacketFields.fields value ["type", "authorized"]
        pure (.application .revoke)
      | "begin" | "restart" | "disconnect" | "close" => do
        Import.PacketFields.fields value ["type", "authorized"]
        pure (match kind with
          | "begin" => .authentication .begin
          | "restart" => .authentication .restart
          | "disconnect" => .authentication .disconnect
          | _ => .close)
      | _ => throw s!"/events/{index}: Unsupported EAP session event: {kind}."
    let authorized ← optionalBool (← value.getObjVal? "authorized")
    observations := observations ++ [⟨index, event, authorized, accepted, frame, value⟩]
  require (0 < frames) "Supply at least one raw EAPOL frame."
  require (observations.any fun observation => observation.authorized.isSome || observation.accepted.isSome)
    "Supply at least one authorization or admission observation."
  return ⟨context, binding, observations, json⟩

def Input.parse (text : String) : Except String Input := do
  Input.fromJson (← Import.Json.parse text)

def Input.check (input : Input) : Report input.context Protocol.EAPSession.State.initial input.observations :=
  audit input.context Protocol.EAPSession.State.initial input.observations

private def scopeJson (scope : Scope) : Lean.Json :=
  Lean.Json.mkObj [("resource", Lean.toJson scope.resource), ("operation", Lean.toJson scope.operation)]

private def stateJson (state : State) : Lean.Json := Lean.Json.mkObj [
  ("round", Lean.toJson state.auth.round), ("authorized", Lean.toJson state.auth.authorized),
  ("outerIdentityHex", Lean.toJson (state.auth.outerIdentity.map Import.EAPOL.bytesToHex)),
  ("sessionAuthenticated", Lean.toJson state.session.authenticated), ("credentialPresent", Lean.toJson state.session.credential.isSome),
  ("now", Lean.toJson state.session.now), ("admitted", (state.session.admitted.map scopeJson).getD .null),
  ("methodEvidence", (state.auth.evidence.map fun evidence => Lean.Json.mkObj [
    ("round", Lean.toJson evidence.round), ("subject", Lean.toJson evidence.subject),
    ("method", Lean.toJson evidence.method.toNat), ("accepted", Lean.toJson evidence.accepted),
    ("source", Lean.toJson evidence.source)]).getD .null)]

def Report.assumptions : List String := [
  "The selected Ethernet MAC binding and role attribution describe the intended link; MAC fields do not prove origin integrity.",
  "Method evidence faithfully records cryptographic acceptance, certificate identity policy, and the current local authentication round.",
  "Opaque TLS payloads are not cryptographically verified by this checker; native producer logs remain reviewed evidence.",
  "Declared lower-layer resets and the supplied trace cover the relevant session; local round tags are not wire replay protection.",
  "Credential integrity, issuer policy, clock interpretation, and actual request enforcement remain supplied assumptions.",
  "Native wired authentication-state flags do not establish physical controlled-port or application data-plane enforcement.",
  "The profile uses local failclosed reset rules and does not establish complete IEEE 802.1X, WLAN, or CNSA compliance."]

def Report.sources : List Standards.Source := [
  ⟨"Extensible Authentication Protocol", "RFC 3748", "4, 4.1, 4.2", "https://www.rfc-editor.org/rfc/rfc3748.html"⟩,
  ⟨"EAP-TLS 1.3", "RFC 9190", "2.1.1, 5.6", "https://www.rfc-editor.org/rfc/rfc9190.html"⟩,
  ⟨"EAPOL implementation definitions", "hostapd 2.12", "src/eapol_common/eapol_common.h",
    "https://w1.fi/releases/hostapd-2.12.tar.gz"⟩]

def Report.renderJson (report : Report context initial observations) : Lean.Json := Lean.Json.mkObj [
  ("compliant", Lean.toJson report.compliant), ("scope", Lean.toJson "eap-derived-session-observation-agreement"),
  ("profile", Lean.toJson "Netlib EAP-derived session subset 1"),
  ("sources", Lean.toJson (Report.sources.map fun source => Lean.Json.mkObj [
    ("document", Lean.toJson source.document), ("version", Lean.toJson source.version),
    ("clause", Lean.toJson source.clause), ("url", Lean.toJson source.url)])),
  ("assumptions", Lean.toJson Report.assumptions), ("subject", Lean.toJson context.consumer),
  ("eventCount", Lean.toJson observations.length), ("final", stateJson report.final),
  ("findings", Lean.toJson (report.findings.map fun finding => Lean.Json.mkObj [
    ("source", Lean.toJson s!"/events/{finding.observation.index}"), ("matched", Lean.toJson finding.passed),
    ("expected", stateJson finding.result), ("observedAuthorized", Lean.toJson finding.observation.authorized),
    ("observedAccepted", Lean.toJson finding.observation.accepted),
    ("expectedAccepted", Lean.toJson (expectedRequest finding.observation.event finding.result)),
    ("frame", (finding.observation.frame.map fun frame => Lean.Json.mkObj [
      ("source", Lean.toJson frame.source.render), ("destination", Lean.toJson frame.destination.render),
      ("paddingBytes", Lean.toJson frame.padding.length)]).getD .null)]))]

def Report.render (report : Report context initial observations) : String :=
  (if report.compliant then "EAP SESSION OBSERVATIONS MATCH\n" else "EAP SESSION OBSERVATIONS MISMATCH\n") ++ report.renderJson.pretty

end Netlib.Check.EAP
