import Netlib.Check.SessionInstallation
import Netlib.Protocol.CampusWithdrawal
import Netlib.Examples.SafeHandoffDeployment

/-!
# One authentication, installation, and withdrawal history

Timeline operations consume the next actual authentication or packet observation.
Installed configurations persist through authentication changes.
Each installation and processing operation checks its current authentication prefix.
-/

namespace Netlib.Check.CampusDeployment

open Packet Protocol
open StatefulFailover (Gateway)

structure Input where
  authentication : Check.EAP.Input
  application : Scope
  requirements : List Compile.SessionFirewall.Intent
  scopes : ∀ requirement ∈ requirements, requirement.scope = application
  handoff : Check.SafeHandoff.Input

structure State where
  authentication : Nat := 0
  network : Nat := 0
  deployment : CampusWithdrawal.State

def State.Safe (input : Input) (state : State) : Prop :=
  state.authentication ≤ input.authentication.observations.length ∧
    state.network ≤ input.handoff.events.length ∧ state.deployment.Safe

def State.check (input : Input) (state : State) : Bool :=
  decide (state.authentication ≤ input.authentication.observations.length) &&
    decide (state.network ≤ input.handoff.events.length) && state.deployment.check

theorem State.check_correct (input : Input) (state : State) : state.check input = true ↔ state.Safe input := by
  simp [check, Safe, CampusWithdrawal.State.check_correct, and_assoc]

def Input.initial (input : Input) : State :=
  ⟨0, 0, CampusWithdrawal.State.initial
    (Check.SafeHandoff.configuration input.handoff.routing .primary input.handoff.primary)
    (Check.SafeHandoff.configuration input.handoff.routing .standby input.handoff.standby)⟩

theorem Input.initial_safe (input : Input) : input.initial.Safe input :=
  ⟨Nat.zero_le _, Nat.zero_le _, CampusWithdrawal.State.initial_safe _ _⟩

inductive Event where
  | authentication (index : Nat)
  | network (index : Nat)
  | withdraw
  deriving Repr, BEq, DecidableEq

structure Observation where
  index : Nat
  event : Event
  raw : Lean.Json

inductive Certification (input : Input) (after : Nat) : Option Protocol.SafeHandoff.Configuration → Type
  | absent : Certification input after none
  | present (active : Protocol.SafeHandoff.Configuration)
      (checked : SessionInstallation.Checked input.authentication input.requirements after active) :
      Certification input after (some active)

def Certification.passed : Certification input after active → Bool
  | .absent => true
  | .present _ checked => checked.passed

def Certification.Valid : Certification input after active → Prop
  | .absent => True
  | .present _ checked => checked.passed = true

theorem Certification.passed_correct (certificate : Certification input after active) :
    certificate.passed = true ↔ certificate.Valid := by
  cases certificate <;> simp [Certification.passed, Certification.Valid]

def certify (input : Input) (after : Nat) : (active : Option Protocol.SafeHandoff.Configuration) → Nat →
    Except String (Certification input after active)
  | none, _ => return .absent
  | some configuration, budget => do
    let checked ← SessionInstallation.check input.authentication input.requirements after configuration input.handoff.configs budget
    return .present configuration checked

def policyTarget (before : Protocol.SafeHandoff.State) (event : Protocol.SafeHandoff.Event) (result : Protocol.SafeHandoff.Result) :
    Option Protocol.SafeHandoff.Configuration :=
  match result.served with
  | some served => some served.configuration
  | none => match event with
    | .install _ configuration => some configuration
    | .establish _ => some (before.configurations .primary)
    | _ => none

structure AuthenticationEvidence (input : Input) (before : State) where
  available : before.authentication < input.authentication.observations.length

def AuthenticationEvidence.source (evidence : AuthenticationEvidence input before) : Check.EAP.Observation :=
  input.authentication.observations[before.authentication]'evidence.available

def AuthenticationEvidence.finding (evidence : AuthenticationEvidence input before) : Check.EAP.Finding :=
  Check.EAP.finding evidence.source (SessionInstallation.current input.authentication (before.authentication + 1))

structure NetworkEvidence (input : Input) (before : State) where
  available : before.network < input.handoff.events.length
  event : Protocol.SafeHandoff.Event
  converted : (input.handoff.events[before.network]'available).event.toModel input.handoff.routing input.handoff.configs
    before.deployment.handoff = .ok event
  operated : CampusWithdrawal.Result
  computed : CampusWithdrawal.step before.deployment (.operation event) = .ok operated
  model : Protocol.SafeHandoff.Result
  selected : operated.operation = some model
  certificate : Certification input before.authentication (policyTarget before.deployment.handoff event model)

def NetworkEvidence.source (evidence : NetworkEvidence input before) : Check.SafeHandoff.Observation :=
  input.handoff.events[before.network]'evidence.available

theorem NetworkEvidence.actual_step (evidence : NetworkEvidence input before) :
    Protocol.SafeHandoff.step before.deployment.handoff evidence.event = .ok evidence.model ∧
      evidence.operated.state.handoff = evidence.model.state := by
  obtain ⟨model, selected, computed, state, _⟩ :=
    CampusWithdrawal.step_operation_facts before.deployment evidence.event evidence.operated evidence.computed
  have same : model = evidence.model := Option.some.inj (selected.symm.trans evidence.selected)
  subst model
  exact ⟨computed, state⟩

def NetworkEvidence.passed (evidence : NetworkEvidence input before) : Bool :=
  Check.SafeHandoff.packetMatches evidence.source evidence.model &&
    Check.SafeHandoff.stateMatches evidence.source evidence.model.state && evidence.certificate.passed

def NetworkEvidence.Matches (evidence : NetworkEvidence input before) : Prop :=
  Check.SafeHandoff.Matches evidence.source evidence.model ∧ evidence.certificate.Valid

theorem NetworkEvidence.passed_correct (evidence : NetworkEvidence input before) :
    evidence.passed = true ↔ evidence.Matches := by
  simp [passed, Matches, Check.SafeHandoff.Matches, Check.SafeHandoff.packetMatches_correct,
    Check.SafeHandoff.stateMatches_correct, Certification.passed_correct, and_assoc]

structure WithdrawalEvidence (before : State) where
  operated : CampusWithdrawal.Result
  computed : CampusWithdrawal.step before.deployment .withdraw = .ok operated

inductive Payload (input : Input) (before : State) where
  | authentication (evidence : AuthenticationEvidence input before)
  | network (evidence : NetworkEvidence input before)
  | withdraw (evidence : WithdrawalEvidence before)

def Payload.state : Payload input before → State
  | .authentication _ => { before with authentication := before.authentication + 1 }
  | .network evidence => { before with network := before.network + 1, deployment := evidence.operated.state }
  | .withdraw evidence => { before with deployment := evidence.operated.state }

def Payload.passed : Payload input before → Bool
  | .authentication evidence => evidence.finding.passed
  | .network evidence => evidence.passed
  | .withdraw _ => true

def Payload.Matches : Payload input before → Prop
  | .authentication evidence => Check.EAP.Matches evidence.source evidence.finding.result
  | .network evidence => evidence.Matches
  | .withdraw _ => True

theorem Payload.passed_correct (payload : Payload input before) : payload.passed = true ↔ payload.Matches := by
  cases payload with
  | authentication evidence => exact Check.EAP.finding_correct _ _
  | network evidence => exact evidence.passed_correct
  | withdraw => simp [passed, Matches]

theorem Payload.safe (payload : Payload input before) (safe : before.Safe input) : payload.state.Safe input := by
  cases payload with
  | authentication evidence => exact ⟨Nat.succ_le_of_lt evidence.available, safe.2⟩
  | network evidence => exact ⟨safe.1, Nat.succ_le_of_lt evidence.available, evidence.operated.safe⟩
  | withdraw evidence => exact ⟨safe.1, safe.2.1, evidence.operated.safe⟩

structure Result (input : Input) where
  before : State
  payload : Payload input before
  safe : payload.state.Safe input

def Result.state (result : Result input) : State := result.payload.state

def process (input : Input) (before : State) (observation : Observation) (budget : Nat) :
    Except String (Payload input before) := do
  match observation.event with
  | .authentication index =>
    if index != before.authentication then throw "Consume the next authentication observation exactly once."
    if available : before.authentication < input.authentication.observations.length then
      return .authentication ⟨available⟩
    else throw "No authentication observation remains."
  | .network index =>
    if index != before.network then throw "Consume the next network observation exactly once."
    if available : before.network < input.handoff.events.length then
      let source := input.handoff.events[before.network]
      if before.deployment.withdrawn && source.primary.isSome then
        throw "A withdrawn gateway has no live primary table observation."
      match converted : source.event.toModel input.handoff.routing input.handoff.configs before.deployment.handoff with
      | .error reason => throw reason
      | .ok event =>
        match computed : CampusWithdrawal.step before.deployment (.operation event) with
        | .error reason => throw reason
        | .ok operated =>
          match selected : operated.operation with
          | none => throw "A network operation has no computed packet/control result."
          | some model =>
            let certificate ← certify input before.authentication
              (policyTarget before.deployment.handoff event model) budget
            return .network ⟨available, event, converted, operated, computed, model, selected, certificate⟩
    else throw "No network observation remains."
  | .withdraw =>
    match computed : CampusWithdrawal.step before.deployment .withdraw with
    | .error reason => throw reason
    | .ok operated => return .withdraw ⟨operated, computed⟩

def step (input : Input) (budget : Nat) (before : State) (observation : Observation) : Except String (Result input) := do
  if valid : before.check input = true then
    let payload ← process input before observation budget
    return ⟨before, payload, payload.safe ((State.check_correct input before).mp valid)⟩
  else throw "The campus replay state violates its prefix or withdrawal invariant."

theorem step_before (input : Input) (budget : Nat) (before : State) (observation : Observation) (result : Result input)
    (accepted : step input budget before observation = .ok result) : result.before = before := by
  unfold step at accepted
  split at accepted
  · rename_i valid
    cases computed : process input before observation budget with
    | error reason => simp [computed, bind, Except.bind] at accepted
    | ok payload =>
      have same : (⟨before, payload, payload.safe ((State.check_correct input before).mp valid)⟩ : Result input) = result := by
        simpa [computed, bind, Except.bind, pure, Except.pure] using accepted
      rw [← same]
  · simp at accepted

def replay (input : Input) (budget : Nat) : Replay.System State Observation (Result input) where
  step := step input budget
  state := Result.state
  passed _ result := result.payload.passed
  Matches _ result := result.payload.Matches
  correct _ result := result.payload.passed_correct

abbrev Finding (input : Input) := Replay.Finding Observation (Result input)
abbrev Report (input : Input) (budget : Nat) (observations : List Observation) :=
  Replay.Report (replay input budget) input.initial observations

def NetworkEvidence.topologyMatches (evidence : NetworkEvidence input before) : Bool :=
  match evidence.model.served, evidence.model.established with
  | some served, _ => decide (served.outcome.nextHop = some (match served.ticket.value.direction with
      | .original => "server" | .reply => "client"))
  | none, some established => decide (established.outcome.nextHop = some "server")
  | none, none => true

def Payload.topologyMatches : Payload input before → Bool
  | .network evidence => evidence.topologyMatches
  | _ => true

def NetworkEvidence.applicationMatches (evidence : NetworkEvidence input before) : Bool :=
  match evidence.model.served, evidence.model.established with
  | some served, _ => input.requirements.any (fun requirement => requirement.test.accepts served.outcome.afterDestination)
  | none, some established => input.requirements.any (fun requirement => requirement.test.accepts established.outcome.afterDestination)
  | none, none => true

def Payload.applicationMatches : Payload input before → Bool
  | .network evidence => evidence.applicationMatches
  | _ => true

structure InitialEvidence (input : Input) where
  primary : SessionInstallation.Checked input.authentication input.requirements 0
    (input.initial.deployment.handoff.configurations .primary)
  standby : SessionInstallation.Checked input.authentication input.requirements 0
    (input.initial.deployment.handoff.configurations .standby)

def InitialEvidence.passed (evidence : InitialEvidence input) : Bool := evidence.primary.passed && evidence.standby.passed

structure CheckedReport (input : Input) (budget : Nat) (observations : List Observation) where
  initial : InitialEvidence input
  execution : Report input budget observations

def CheckedReport.complete (report : CheckedReport input budget observations) : Bool :=
  decide (report.execution.final.authentication = input.authentication.observations.length) &&
    decide (report.execution.final.network = input.handoff.events.length) && report.execution.final.deployment.withdrawn

def CheckedReport.compliant (report : CheckedReport input budget observations) : Bool :=
  report.initial.passed && report.execution.compliant && report.complete &&
    report.execution.findings.all (fun finding => finding.result.payload.topologyMatches && finding.result.payload.applicationMatches)

theorem CheckedReport.execution_compliant (report : CheckedReport input budget observations)
    (passed : report.compliant = true) : report.execution.compliant = true := by
  have values : ((report.initial.passed = true ∧ report.execution.compliant = true) ∧ report.complete = true) ∧
      report.execution.findings.all (fun finding => finding.result.payload.topologyMatches && finding.result.payload.applicationMatches) = true := by
    simpa only [CheckedReport.compliant, Bool.and_eq_true] using passed
  exact values.1.1.2

theorem CheckedReport.finding_matches (report : CheckedReport input budget observations)
    (passed : report.compliant = true) (finding : Finding input) (member : finding ∈ report.execution.findings) :
    finding.result.payload.Matches :=
  report.execution.finding_matches (report.execution_compliant passed) finding member

def check (input : Input) (observations : List Observation) (budget : Nat := 100000) :
    Except String (CheckedReport input budget observations) := do
  let primary ← SessionInstallation.check input.authentication input.requirements 0
    (input.initial.deployment.handoff.configurations .primary) input.handoff.configs budget
  let standby ← SessionInstallation.check input.authentication input.requirements 0
    (input.initial.deployment.handoff.configurations .standby) input.handoff.configs budget
  let execution ← Replay.audit (replay input budget) input.initial observations
  return ⟨⟨primary, standby⟩, execution⟩

structure Bundle where
  input : Input
  timeline : List Observation

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

def Bundle.fromJson (json : Lean.Json) : Except String Bundle := do
  Import.PacketFields.fields json ["schema", "application", "authentication", "intent", "handoff", "timeline"]
  require ((← (← json.getObjVal? "schema").getNat?) == 1) "Use campus deployment schema 1."
  let applicationJson ← json.getObjVal? "application"
  Import.PacketFields.fields applicationJson ["resource", "operation"]
  let application : Scope := ⟨← (← applicationJson.getObjVal? "resource").getStr?,
    ← (← applicationJson.getObjVal? "operation").getStr?⟩
  require (!application.resource.isEmpty && !application.operation.isEmpty) "Application scope names must not be empty."
  let authentication ← Check.EAP.Input.fromJson (← json.getObjVal? "authentication")
  let requirements ← Check.SessionFirewall.requirementsFromJson (← json.getObjVal? "intent")
  require (!requirements.isEmpty) "Bind at least one packet class to the campus application."
  let handoff ← Check.SafeHandoff.Input.fromJson (← json.getObjVal? "handoff")
  if scopes : requirements.all (fun requirement => decide (requirement.scope = application)) = true then
    let input : Input := ⟨authentication, application, requirements,
      by simpa only [List.all_eq_true, decide_eq_true_eq] using scopes, handoff⟩
    let values ← (← json.getObjVal? "timeline").getArr?
    let mut timeline := []
    for index in [:values.size] do
      let value := values[index]!
      let event ← match ← (← value.getObjVal? "type").getStr? with
        | "authentication" => do
          Import.PacketFields.fields value ["type", "event"]
          pure (Event.authentication (← (← value.getObjVal? "event").getNat?))
        | "network" => do
          Import.PacketFields.fields value ["type", "event"]
          pure (Event.network (← (← value.getObjVal? "event").getNat?))
        | "withdraw" => do
          Import.PacketFields.fields value ["type"]
          pure Event.withdraw
        | kind => throw s!"Unsupported campus timeline operation: {kind}."
      timeline := timeline ++ [⟨index, event, value⟩]
    require (timeline.any fun observation => observation.event == .withdraw) "Supply the actual planned primary withdrawal."
    return ⟨input, timeline⟩
  else throw "Every campus packet intent must name the declared application scope."

def Bundle.parse (text : String) : Except String Bundle := do Bundle.fromJson (← Import.Json.parse text)

def Bundle.check (bundle : Bundle) (budget : Nat := 100000) :
    Except String (CheckedReport bundle.input budget bundle.timeline) :=
  CampusDeployment.check bundle.input bundle.timeline budget

private def gatewayName : Gateway → String
  | .primary => "primary" | .standby => "standby"

private def policyJson (checked : SessionInstallation.Checked authentication requirements after active) : Lean.Json :=
  Lean.Json.mkObj [
    ("configuration", Lean.toJson active.id), ("afterAuthentication", Lean.toJson after),
    ("equivalent", Lean.toJson checked.passed), ("partitionCells", Lean.toJson checked.cells),
    ("nativeChain", Lean.toJson checked.source.forward.chain),
    ("authorized", Lean.toJson (SessionInstallation.current authentication after).auth.authorized),
    ("credentialPresent", Lean.toJson (SessionInstallation.current authentication after).session.credential.isSome)]

private def certificateJson : Certification input after active → Lean.Json
  | .absent => .null
  | .present _ checked => policyJson checked

private def stateJson (input : Input) (state : State) : Lean.Json := Lean.Json.mkObj [
  ("authenticationConsumed", Lean.toJson state.authentication), ("networkConsumed", Lean.toJson state.network),
  ("authorized", Lean.toJson (SessionInstallation.current input.authentication state.authentication).auth.authorized),
  ("applicationPermitted", Lean.toJson
    ((SessionInstallation.current input.authentication state.authentication).session.permits input.authentication.context input.application)),
  ("withdrawn", Lean.toJson state.deployment.withdrawn),
  ("archivedPrimary", (state.deployment.archive.map Check.ConntrackLifecycle.stateJson).getD .null),
  ("primarySnapshot", Check.ConntrackLifecycle.stateJson state.deployment.handoff.gateways.primary),
  ("standby", Check.ConntrackLifecycle.stateJson state.deployment.handoff.gateways.standby),
  ("owners", Lean.Json.mkObj [
    ("client", Lean.toJson (gatewayName state.deployment.handoff.gateways.owners.client)),
    ("server", Lean.toJson (gatewayName state.deployment.handoff.gateways.owners.server))]),
  ("configurations", Lean.Json.mkObj [
    ("primary", Lean.toJson (state.deployment.handoff.configurations .primary).id),
    ("standby", Lean.toJson (state.deployment.handoff.configurations .standby).id)]),
  ("pendingIDs", Lean.toJson (state.deployment.handoff.work.pending.map (·.id))),
  ("completedIDs", Lean.toJson (state.deployment.handoff.work.completed.map (·.id))),
  ("epoch", Lean.toJson state.deployment.handoff.gateways.epoch)]

private def payloadJson : Payload input before → List (String × Lean.Json)
  | .authentication evidence => [
    ("type", Lean.toJson "authentication"), ("event", Lean.toJson before.authentication),
    ("policy", .null), ("expected", .null),
    ("authenticationMatched", Lean.toJson evidence.finding.passed)]
  | .network evidence => [
    ("type", Lean.toJson "network"), ("event", Lean.toJson before.network),
    ("policy", certificateJson evidence.certificate),
    ("expected", match evidence.model.served, evidence.model.established with
      | some served, _ => Check.WireForwarding.outcomeToJson served.outcome
      | none, some established => Check.WireForwarding.outcomeToJson established.outcome
      | none, none => .null),
    ("servedID", Lean.toJson (evidence.model.served.map (·.ticket.id))),
    ("assignedGateway", Lean.toJson (evidence.model.served.map (gatewayName ∘ (·.ticket.value.gateway)))),
    ("packetMatched", Lean.toJson (Check.SafeHandoff.packetMatches evidence.source evidence.model)),
    ("tablesMatched", Lean.toJson (Check.SafeHandoff.stateMatches evidence.source evidence.model.state))]
  | .withdraw _ => [("type", Lean.toJson "withdraw"), ("policy", .null), ("expected", .null)]

def assumptions : List String := [
  "One ordered timeline binds actual EAP observations, installed configurations, routed datagrams, and the declared withdrawal.",
  "The reviewed principal-to-packet and interface-to-node mappings describe the same wired deployment and selected application.",
  "Method evidence, credential integrity, frame attribution, and authentic collection retain the EAP checker assumptions.",
  "Native configuration exports faithfully describe each installed policy until its next explicit replacement.",
  "Route reads, gateway packet executions, and configuration changes have the declared linearization and stable packet hooks.",
  "The protected UDP binding has no aging, conflicting writer, replacement, helper, or unmodeled transport behavior.",
  "The withdrawn primary table is an archived execution snapshot and is never claimed to remain a live kernel table.",
  "Physical queues, scheduling, loss, cryptography, wireless key installation, and complete implementation refinement need separate evidence."]

def CheckedReport.renderJson (report : CheckedReport input budget observations) : Lean.Json := Lean.Json.mkObj [
  ("scope", Lean.toJson "checked-wired-campus-deployment"), ("compliant", Lean.toJson report.compliant),
  ("subject", Lean.toJson input.authentication.context.consumer),
  ("application", Lean.Json.mkObj [("resource", Lean.toJson input.application.resource),
    ("operation", Lean.toJson input.application.operation)]),
  ("complete", Lean.toJson report.complete), ("eventCount", Lean.toJson report.execution.findings.length),
  ("assumptions", Lean.toJson assumptions),
  ("initialPolicies", Lean.toJson [policyJson report.initial.primary, policyJson report.initial.standby]),
  ("final", stateJson input report.execution.final),
  ("findings", Lean.toJson (report.execution.findings.map fun finding => Lean.Json.mkObj (
    [("source", Lean.toJson s!"/timeline/{finding.observation.index}"),
      ("matched", Lean.toJson finding.result.payload.passed),
      ("topologyMatched", Lean.toJson finding.result.payload.topologyMatches),
      ("applicationMatched", Lean.toJson finding.result.payload.applicationMatches),
      ("before", stateJson input finding.result.before), ("after", stateJson input finding.result.state)] ++
      payloadJson finding.result.payload)))]

def CheckedReport.render (report : CheckedReport input budget observations) : String :=
  (if report.compliant then "CAMPUS DEPLOYMENT MATCHES\n" else "CAMPUS DEPLOYMENT MISMATCH\n") ++ report.renderJson.pretty

end Netlib.Check.CampusDeployment
