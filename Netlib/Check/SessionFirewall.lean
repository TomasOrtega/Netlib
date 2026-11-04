import Netlib.Check.EAP
import Netlib.Check.StatefulRefinement
import Netlib.Compile.SessionFirewall
import Netlib.Model.DataPlane

/-!
# EAP-derived native firewall snapshots

Each checkpoint selects a consumed authentication-event prefix. Native policy must
equal the generated policy for every state and header at the same hook and priority.
The checks cover supplied snapshots; installation and packet attribution remain explicit.
-/

namespace Netlib.Check.SessionFirewall

open Protocol Packet

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

def requirementsFromJson (json : Lean.Json) : Except String (List Compile.SessionFirewall.Intent) := do
  Import.PacketFields.fields json ["schema", "requirements"]
  require ((← (← json.getObjVal? "schema").getNat?) == 1) "Use session intent schema 1."
  (← (← json.getObjVal? "requirements").getArr?).toList.mapM fun value => do
    Import.PacketFields.fields value ["id", "scope", "match"]
    let scope ← value.getObjVal? "scope"
    Import.PacketFields.fields scope ["resource", "operation"]
    let resource ← (← scope.getObjVal? "resource").getStr?
    let operation ← (← scope.getObjVal? "operation").getStr?
    require (!resource.isEmpty && !operation.isEmpty) "Scope names must not be empty."
    return ⟨← (← value.getObjVal? "id").getStr?, ⟨resource, operation⟩,
      ← DataPlane.Config.parseTrafficSelection (← value.getObjVal? "match").compress⟩

def parseRequirements (text : String) : Except String (List Compile.SessionFirewall.Intent) := do
  requirementsFromJson (← Import.Json.parse text)

def stateAt (authentication : EAP.Input) (after : Nat) : EAPSession.State :=
  (EAP.audit authentication.context EAPSession.State.initial (authentication.observations.take after)).final

theorem stateAt_safe (authentication : EAP.Input) (after : Nat) :
    (stateAt authentication after).Safe authentication.context :=
  ((EAP.audit authentication.context EAPSession.State.initial
    (authentication.observations.take after)).trace.safe (EAPSession.initial_safe authentication.context)).1

structure SnapshotInput where
  index : Nat
  after : Nat
  firewall : Import.NftablesStateful.Snapshot

structure Input where
  authentication : EAP.Input
  requirements : List Compile.SessionFirewall.Intent
  snapshots : List SnapshotInput

def Input.fromJson (json : Lean.Json) : Except String Input := do
  Import.PacketFields.fields json ["schema", "authentication", "intent", "snapshots"]
  require ((← (← json.getObjVal? "schema").getNat?) == 1) "Use session firewall schema 1."
  let authentication ← EAP.Input.fromJson (← json.getObjVal? "authentication")
  let requirements ← requirementsFromJson (← json.getObjVal? "intent")
  let values ← (← json.getObjVal? "snapshots").getArr?
  require (!values.isEmpty) "Supply at least one native firewall snapshot."
  let mut snapshots := []
  let mut previous : Option Nat := none
  for index in [:values.size] do
    let value := values[index]!
    Import.PacketFields.fields value ["after", "firewall"]
    let after ← (← value.getObjVal? "after").getNat?
    require (after ≤ authentication.observations.length) "A snapshot prefix exceeds the event count."
    if let some last := previous then
      require (last < after) "Snapshot prefixes must be strictly increasing."
    previous := some after
    let firewall ← Import.NftablesStateful.Snapshot.fromJson (← value.getObjVal? "firewall")
    snapshots := snapshots ++ [⟨index, after, firewall⟩]
  return ⟨authentication, requirements, snapshots⟩

def Input.parse (text : String) : Except String Input := do
  Input.fromJson (← Import.Json.parse text)

structure Finding (input : Input) where
  checkpoint : SnapshotInput
  compiled : Compile.SessionFirewall.Certified input.authentication.context
    (stateAt input.authentication checkpoint.after) input.requirements
  context : StatefulRefinement.sameContext checkpoint.firewall compiled.statefulSnapshot = true

namespace Finding

def compilationCells (finding : Finding input) : Nat :=
  (Compile.ACL.partition (Compile.SessionFirewall.intents input.authentication.context
    (stateAt input.authentication finding.checkpoint.after) input.requirements)).cellCount

def comparisonCells (finding : Finding input) : Nat :=
  StatefulRefinement.cellCount finding.checkpoint.firewall finding.compiled.statefulSnapshot +
    StatefulRefinement.cellCount finding.compiled.statefulSnapshot finding.checkpoint.firewall

def cells (finding : Finding input) : Nat := finding.compilationCells + finding.comparisonCells

def passed (finding : Finding input) : Bool :=
  StatefulRefinement.check finding.checkpoint.firewall finding.compiled.statefulSnapshot &&
    StatefulRefinement.check finding.compiled.statefulSnapshot finding.checkpoint.firewall

def Equivalent (finding : Finding input) : Prop :=
  ∀ state header, finding.checkpoint.firewall.permits state header = finding.compiled.snapshot.permits header

theorem correct (finding : Finding input) : finding.passed = true ↔ finding.Equivalent := by
  simp only [passed, Bool.and_eq_true, StatefulRefinement.check_correct]
  constructor
  · rintro ⟨stronger, weaker⟩ state header
    rw [← finding.compiled.statefulSnapshot_permits state header]
    exact Bool.eq_iff_iff.mpr ⟨stronger state header, weaker state header⟩
  · intro equivalent
    constructor
    · intro state header allowed
      rw [finding.compiled.statefulSnapshot_permits, ← equivalent state header]
      exact allowed
    · intro state header allowed
      rw [equivalent state header]
      exact (finding.compiled.statefulSnapshot_permits state header).symm.trans allowed

theorem permitted_valid (finding : Finding input) (passed : finding.passed = true)
    (state : StatefulACL.CTState) (header : Header)
    (permitted : finding.checkpoint.firewall.permits state header = true) :
    ∃ requirement ∈ input.requirements, requirement.test.Holds header ∧
      Session.Valid input.authentication.context (stateAt input.authentication finding.checkpoint.after).session
        requirement.scope ∧
      EAPAuth.State.Ready (EAPSession.authContext input.authentication.context)
        (stateAt input.authentication finding.checkpoint.after).auth := by
  apply finding.compiled.permitted_valid (stateAt_safe _ _) header
  exact ((finding.correct.mp passed) state header).symm.trans permitted

theorem denied_requirement (finding : Finding input) (passed : finding.passed = true)
    (requirement : Compile.SessionFirewall.Intent) (member : requirement ∈ input.requirements)
    (denied : (stateAt input.authentication finding.checkpoint.after).session.permits
      input.authentication.context requirement.scope = false)
    (state : StatefulACL.CTState) (header : Header) (matched : requirement.test.Holds header) :
    finding.checkpoint.firewall.permits state header = false := by
  rw [(finding.correct.mp passed) state header]
  exact finding.compiled.denied_requirement requirement member denied header matched

end Finding

private structure Checked (input : Input) (snapshots : List SnapshotInput) where
  findings : List (Finding input)
  covered : findings.map Finding.checkpoint = snapshots

private def auditSnapshots (input : Input) :
    (snapshots : List SnapshotInput) → Nat → Except String (Checked input snapshots)
  | [], _ => .ok ⟨[], rfl⟩
  | checkpoint :: snapshots, budget => do
    let compiled ← (Compile.SessionFirewall.compile input.authentication.context
      (stateAt input.authentication checkpoint.after) input.requirements budget).mapError (·.describe)
    if same : StatefulRefinement.sameContext checkpoint.firewall compiled.statefulSnapshot = true then
      let finding : Finding input := ⟨checkpoint, compiled, same⟩
      require (finding.cells ≤ budget) "Session firewall checking exceeds the total partition cell budget."
      let rest ← auditSnapshots input snapshots (budget - finding.cells)
      return ⟨finding :: rest.findings, by simp only [List.map_cons, rest.covered]; rfl⟩
    else throw "Session firewall comparison requires the generated forward hook and priority."

structure Report (input : Input) where
  findings : List (Finding input)
  covered : findings.map Finding.checkpoint = input.snapshots

def Input.check (input : Input) (budget : Nat := 100000) : Except String (Report input) := do
  let checked ← auditSnapshots input input.snapshots budget
  return ⟨checked.findings, checked.covered⟩

namespace Report

def compliant (report : Report input) : Bool :=
  input.authentication.check.compliant && report.findings.all Finding.passed

theorem finding_passed (report : Report input) (compliant : report.compliant = true)
    (finding : Finding input) (member : finding ∈ report.findings) : finding.passed = true := by
  have pair : input.authentication.check.compliant = true ∧ report.findings.all Finding.passed = true := by
    simpa only [Report.compliant, Bool.and_eq_true] using compliant
  exact (List.all_eq_true.mp pair.2) finding member

theorem permitted_valid (report : Report input) (compliant : report.compliant = true)
    (finding : Finding input) (member : finding ∈ report.findings)
    (state : StatefulACL.CTState) (header : Header)
    (permitted : finding.checkpoint.firewall.permits state header = true) :
    ∃ requirement ∈ input.requirements, requirement.test.Holds header ∧
      Session.Valid input.authentication.context (stateAt input.authentication finding.checkpoint.after).session
        requirement.scope ∧
      EAPAuth.State.Ready (EAPSession.authContext input.authentication.context)
        (stateAt input.authentication finding.checkpoint.after).auth :=
  finding.permitted_valid (report.finding_passed compliant finding member) state header permitted

def assumptions : List String := [
  "The reviewed scope-to-packet mapping binds this authenticated principal to the selected ingress and headers.",
  "EAP method evidence, credential integrity, clock interpretation, and Ethernet attribution retain the EAP checker assumptions.",
  "Each supplied export is the installed firewall at its declared authentication-event prefix.",
  "Headers describe valid IPv4 transit packets at forward after destination NAT and before source NAT.",
  "Other native hooks, routes, hardware, and concurrent changes do not bypass or change these decisions.",
  "Snapshot equivalence covers every modeled state and header; it does not measure installation latency or drain old queues."]

private def stateName : StatefulACL.CTState → String
  | .new => "new" | .established => "established" | .related => "related"
  | .invalid => "invalid" | .untracked => "untracked"

private def counterexample (stronger weaker : Import.NftablesStateful.Snapshot) : Lean.Json :=
  (StatefulRefinement.counterexample stronger weaker |>.map fun witness => Lean.Json.mkObj [
    ("state", Lean.toJson (stateName witness.state)), ("header", Import.PacketFields.headerJson witness.header)]).getD .null

def renderJson (report : Report input) : Lean.Json := Lean.Json.mkObj [
  ("compliant", Lean.toJson report.compliant), ("scope", Lean.toJson "eap-derived-native-firewall-snapshots"),
  ("subject", Lean.toJson input.authentication.context.consumer),
  ("authenticationMatches", Lean.toJson input.authentication.check.compliant),
  ("assumptions", Lean.toJson assumptions),
  ("partitionCells", Lean.toJson (report.findings.map Finding.cells).sum),
  ("compilationCells", Lean.toJson (report.findings.map Finding.compilationCells).sum),
  ("comparisonCells", Lean.toJson (report.findings.map Finding.comparisonCells).sum),
  ("snapshots", Lean.toJson (report.findings.map fun finding => Lean.Json.mkObj [
    ("source", Lean.toJson s!"/snapshots/{finding.checkpoint.index}"),
    ("after", Lean.toJson finding.checkpoint.after), ("equivalent", Lean.toJson finding.passed),
    ("authorized", Lean.toJson (stateAt input.authentication finding.checkpoint.after).auth.authorized),
    ("credentialPresent", Lean.toJson (stateAt input.authentication finding.checkpoint.after).session.credential.isSome),
    ("partitionCells", Lean.toJson finding.cells),
    ("compilationCells", Lean.toJson finding.compilationCells),
    ("comparisonCells", Lean.toJson finding.comparisonCells),
    ("unexpectedPermit", counterexample finding.checkpoint.firewall finding.compiled.statefulSnapshot),
    ("missingPermit", counterexample finding.compiled.statefulSnapshot finding.checkpoint.firewall)]))]

def render (report : Report input) : String :=
  (if report.compliant then "SESSION FIREWALL SNAPSHOTS MATCH\n" else "SESSION FIREWALL SNAPSHOTS MISMATCH\n") ++
    report.renderJson.pretty

end Report
end Netlib.Check.SessionFirewall
