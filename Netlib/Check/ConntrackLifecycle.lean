import Netlib.Import.ConntrackNetlink
import Netlib.Import.LinuxRoute
import Netlib.Import.NftablesNAT
import Netlib.Import.NftablesStateful
import Netlib.Protocol.ConntrackOperations

/-!
# Ordinary forwarded-packet replay

The checker derives fresh candidates from the selected NAT table only on a prehook lookup miss.
Observations do not update the modeled state.
Optional table observations compare stable tuples, zones, NAT flags, and seen-reply flags.
Capture decoding, transport validation, namespace identity, and native C refinement remain assumptions.
-/

namespace Netlib.Check.ConntrackLifecycle

open Packet Protocol
open Protocol.ConntrackLifecycle
open Packet.StatefulACL (CTState)

structure Config where
  id : String
  index : Nat
  forward : Import.NftablesStateful.Snapshot
  late : Import.NftablesStateful.Snapshot
  nat : Import.NftablesNAT.Snapshot
  raw : Lean.Json

def Config.pipeline (config : Config) (routing : Import.LinuxRoute.Snapshot) : Pipeline :=
  ⟨routing.compile, config.forward.compile, config.forward.policy, config.late.compile, config.late.policy⟩

structure PacketObservation where
  classification : CTState
  fresh : Bool
  afterDestination : Header
  afterSource : Option Header
  nextHop : Option String
  disposition : Disposition
  output : Option Header
  deriving Repr, BEq, DecidableEq

def PacketObservation.expected (outcome : Outcome) : PacketObservation :=
  ⟨outcome.attachment.classification, outcome.attachment.fresh, outcome.afterDestination,
    outcome.afterSource, outcome.nextHop, outcome.disposition, outcome.output⟩

def stableRecord (record : Record) : Record :=
  { record with entry := { record.entry with flow := { record.entry.flow with remainingTTL := 0 } } }

def stableRecords (state : State) : List Record := state.records.map stableRecord

def snapshotState (snapshot : Import.ConntrackNetlink.Snapshot) : State :=
  ⟨snapshot.entries.map fun row => stableRecord ⟨row.entry, row.status.testBit 1⟩⟩

def SameRecords (left right : State) : Prop :=
  (∀ record ∈ stableRecords left, record ∈ stableRecords right) ∧
    (∀ record ∈ stableRecords right, record ∈ stableRecords left)

def sameRecords (left right : State) : Bool :=
  (stableRecords left).all (fun record => (stableRecords right).any (fun other => decide (record = other))) &&
    (stableRecords right).all (fun record => (stableRecords left).any (fun other => decide (record = other)))

theorem sameRecords_correct (left right : State) : sameRecords left right = true ↔ SameRecords left right := by
  simp [sameRecords, SameRecords, List.all_eq_true, List.any_eq_true]

inductive Event where
  | packet (config : Config) (zone : Nat) (packet : Header) (observed : PacketObservation)
      (state : Option Import.ConntrackNetlink.Snapshot)
  | erase (zone : Nat) (packet : Header) (state : Option Import.ConntrackNetlink.Snapshot)

namespace Event

def toModel (routing : Import.LinuxRoute.Snapshot) (before : State) : Event → Operations.Event
  | .packet config zone header _ _ =>
    let candidate := if (before.model.lookup zone header).isNone then some (config.nat.candidate zone header) else none
    .packet ⟨config.pipeline routing, ⟨zone, header, candidate⟩⟩
  | .erase zone header _ => .erase zone header

def stateObservation : Event → Option Import.ConntrackNetlink.Snapshot
  | .packet _ _ _ _ state | .erase _ _ state => state

def packetObservation : Event → Option PacketObservation
  | .packet _ _ _ observed _ => some observed
  | .erase .. => none

def isPacket : Event → Bool
  | .packet .. => true
  | .erase .. => false

def configID : Event → Option String
  | .packet config .. => some config.id
  | .erase .. => none

theorem existing_binding (routing : Import.LinuxRoute.Snapshot) (before : State) (config : Config)
    (zone : Nat) (header : Header) (observed : PacketObservation) (state : Option Import.ConntrackNetlink.Snapshot)
    (hit : FlowNAT.Hit) (found : before.model.lookup zone header = some hit) :
    toModel routing before (.packet config zone header observed state) =
      .packet ⟨config.pipeline routing, ⟨zone, header, none⟩⟩ := by simp [toModel, found]

theorem fresh_candidate (routing : Import.LinuxRoute.Snapshot) (before : State) (config : Config)
    (zone : Nat) (header : Header) (observed : PacketObservation) (state : Option Import.ConntrackNetlink.Snapshot)
    (missing : before.model.lookup zone header = none) :
    toModel routing before (.packet config zone header observed state) =
      .packet ⟨config.pipeline routing, ⟨zone, header, some (config.nat.candidate zone header)⟩⟩ := by
  simp [toModel, missing]

end Event

structure Observation where
  index : Nat
  event : Event
  raw : Lean.Json

def StateMatches (event : Event) (after : State) : Prop :=
  match event.stateObservation with
  | none => True
  | some snapshot => SameRecords after (snapshotState snapshot)

def stateMatches (event : Event) (after : State) : Bool :=
  match event.stateObservation with
  | none => true
  | some snapshot => sameRecords after (snapshotState snapshot)

theorem stateMatches_correct (event : Event) (after : State) :
    stateMatches event after = true ↔ StateMatches event after := by
  cases observed : event.stateObservation <;> simp [stateMatches, StateMatches, observed, sameRecords_correct]

def Matches (observation : Observation) (result : Operations.Result) : Prop :=
  observation.event.packetObservation = result.packet.map PacketObservation.expected ∧
    StateMatches observation.event result.state

structure Finding where
  observation : Observation
  result : Operations.Result
  passed : Bool

def finding (observation : Observation) (result : Operations.Result) : Finding :=
  ⟨observation, result,
    decide (observation.event.packetObservation = result.packet.map PacketObservation.expected) &&
      stateMatches observation.event result.state⟩

theorem finding_correct (observation : Observation) (result : Operations.Result) :
    (finding observation result).passed = true ↔ Matches observation result := by
  simp only [finding, Bool.and_eq_true, decide_eq_true_eq, stateMatches_correct, Matches]

def Agreement (routing : Import.LinuxRoute.Snapshot) : State → List Observation → Prop
  | _, [] => True
  | state, observation :: observations =>
    ∃ result, Operations.step state (observation.event.toModel routing state) = .ok result ∧
      Matches observation result ∧ Agreement routing result.state observations

inductive ReplayTrace (routing : Import.LinuxRoute.Snapshot) : State → List Finding → State → Prop
  | nil (state : State) : ReplayTrace routing state [] state
  | cons {state final : State} {head : Finding} {tail : List Finding}
      (accepted : Operations.step state (head.observation.event.toModel routing state) = .ok head.result)
      (rest : ReplayTrace routing head.result.state tail final) :
      ReplayTrace routing state (head :: tail) final

theorem ReplayTrace.valid {routing : Import.LinuxRoute.Snapshot} {initial final : State} {findings : List Finding}
    (trace : ReplayTrace routing initial findings final) (valid : initial.Valid) :
    final.Valid ∧ ∀ result ∈ findings, result.result.state.Valid := by
  induction trace with
  | nil => exact ⟨valid, by simp⟩
  | @cons state final head tail accepted rest ih =>
    obtain ⟨finalValid, each⟩ := ih head.result.valid
    refine ⟨finalValid, ?_⟩
    intro result member
    rcases List.mem_cons.mp member with rfl | member
    · exact result.result.valid
    · exact each _ member

structure Report (routing : Import.LinuxRoute.Snapshot) (initial : State) (observations : List Observation) where
  final : State
  findings : List Finding
  covered : findings.map Finding.observation = observations
  trace : ReplayTrace routing initial findings final
  correct : findings.all Finding.passed = true ↔ Agreement routing initial observations

def audit (routing : Import.LinuxRoute.Snapshot) (initial : State) :
    (observations : List Observation) → Except String (Report routing initial observations)
  | [] => .ok ⟨initial, [], rfl, .nil initial, by simp [Agreement]⟩
  | observation :: observations => do
    match accepted : Operations.step initial (observation.event.toModel routing initial) with
    | .error error => throw s!"/events/{observation.index}: {error.describe}"
    | .ok result =>
      let tail ← audit routing result.state observations
      return ⟨tail.final, finding observation result :: tail.findings,
        by simp only [List.map_cons, finding, tail.covered],
        .cons accepted tail.trace, by
          simp only [List.all_cons, Bool.and_eq_true, finding_correct, tail.correct, Agreement]
          simp [accepted]⟩

namespace Report

def compliant (report : Report routing initial observations) : Bool := report.findings.all Finding.passed

theorem compliant_iff (report : Report routing initial observations) :
    report.compliant = true ↔ Agreement routing initial observations := report.correct

theorem prefixes_valid (report : Report routing initial observations) (valid : initial.Valid) :
    report.final.Valid ∧ ∀ finding ∈ report.findings, finding.result.state.Valid := report.trace.valid valid

end Report

structure Input where
  routing : Import.LinuxRoute.Snapshot
  configs : List Config
  initialSource : Option Import.ConntrackNetlink.Snapshot
  initial : State
  initialValid : initial.Valid
  events : List Observation
  raw : Lean.Json

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def zone (json : Lean.Json) : Except String Nat := do
  let value ← json.getNat?
  require (value < 65536) "A conntrack zone must fit in 16 bits."
  return value

private def optionalString (json : Lean.Json) : Except String (Option String) :=
  match json with
  | .null => .ok none
  | json => some <$> json.getStr?

private def stateObservation (json : Lean.Json) : Except String (Option Import.ConntrackNetlink.Snapshot) :=
  match json with
  | .null => .ok none
  | json => some <$> Import.ConntrackNetlink.Snapshot.fromJson json

private def parseClassification (json : Lean.Json) : Except String CTState := do
  match ← json.getStr? with
  | "new" => return .new
  | "established" => return .established
  | "related" => return .related
  | "invalid" => return .invalid
  | "untracked" => return .untracked
  | value => throw s!"Unsupported observed conntrack classification: {value}."

private def parseDisposition (json : Lean.Json) : Except String Disposition := do
  match ← json.getStr? with
  | "forwarded" => return .forwarded
  | "routeDrop" => return .routeDrop
  | "forwardDrop" => return .forwardDrop
  | "lateDrop" => return .lateDrop
  | value => throw s!"Unsupported observed disposition: {value}."

private def packetObservation (json : Lean.Json) : Except String PacketObservation := do
  Import.PacketFields.fields json ["classification", "fresh", "afterDestination", "afterSource", "nextHop", "disposition", "output"]
  return ⟨← parseClassification (← json.getObjVal? "classification"),
    ← (← json.getObjVal? "fresh").getBool?,
    ← Import.PacketFields.header (← json.getObjVal? "afterDestination"),
    ← Import.PacketFields.optionalHeader (← json.getObjVal? "afterSource"),
    ← optionalString (← json.getObjVal? "nextHop"),
    ← parseDisposition (← json.getObjVal? "disposition"),
    ← Import.PacketFields.optionalHeader (← json.getObjVal? "output")⟩

private def binding (json : Lean.Json) : Except String Import.LinuxRoute.Binding := do
  Import.PacketFields.fields json ["device", "nextNode", "gateway"]
  let gateway ← match ← json.getObjVal? "gateway" with
    | .null => pure none
    | json => some <$> Import.IPv4.parseAddress (← json.getStr?)
  return ⟨← (← json.getObjVal? "device").getStr?, ← (← json.getObjVal? "nextNode").getStr?, gateway⟩

private def parseRouting (json : Lean.Json) : Except String Import.LinuxRoute.Snapshot := do
  Import.PacketFields.fields json ["version", "bindings", "routes"]
  require ((← (← json.getObjVal? "version").getStr?) == "6.19.0") "Require iproute2 version 6.19.0."
  let bindings ← (← (← json.getObjVal? "bindings").getArr?).toList.mapM binding
  Import.LinuxRoute.Snapshot.fromJson (← json.getObjVal? "routes") bindings

private def parseConfig (json : Lean.Json) (index : Nat) : Except String Config := do
  Import.PacketFields.fields json ["id", "forward", "late", "nat"]
  let id ← (← json.getObjVal? "id").getStr?
  require (!id.isEmpty) "A configuration ID must not be empty."
  let forward ← Import.NftablesStateful.Snapshot.fromJson (← json.getObjVal? "forward")
  require (forward.hook == "forward") "The forward filter must use the forward hook."
  let late ← Import.NftablesStateful.Snapshot.fromJson (← json.getObjVal? "late")
  require (late.hook == "postrouting" && 100 < late.priority && late.priority < 2147483647)
    "The late filter must use postrouting after source NAT and before confirmation."
  let nat ← Import.NftablesNAT.Snapshot.fromJson (← json.getObjVal? "nat")
  return ⟨id, index, forward, late, nat, json⟩

def routingFromJson (json : Lean.Json) : Except String Import.LinuxRoute.Snapshot := parseRouting json

def Config.fromJson (json : Lean.Json) (index : Nat) : Except String Config := parseConfig json index

private def parseEvent (json : Lean.Json) (index : Nat) (configs : List Config) : Except String Observation := do
  let kind ← (← json.getObjVal? "type").getStr?
  let event ← match kind with
    | "packet" => do
      Import.PacketFields.fields json ["type", "config", "zone", "packet", "observed", "state"]
      let id ← (← json.getObjVal? "config").getStr?
      let some config := configs.find? (·.id == id) | throw s!"Unknown configuration ID: {id}."
      pure (.packet config (← zone (← json.getObjVal? "zone"))
        (← Import.PacketFields.header (← json.getObjVal? "packet"))
        (← packetObservation (← json.getObjVal? "observed"))
        (← stateObservation (← json.getObjVal? "state")))
    | "erase" => do
      Import.PacketFields.fields json ["type", "zone", "packet", "state"]
      pure (.erase (← zone (← json.getObjVal? "zone"))
        (← Import.PacketFields.header (← json.getObjVal? "packet"))
        (← stateObservation (← json.getObjVal? "state")))
    | _ => throw s!"Unsupported lifecycle event: {kind}."
  return ⟨index, event, json⟩

def Input.fromJson (json : Lean.Json) : Except String Input := do
  Import.PacketFields.fields json ["schema", "routing", "configs", "initial", "events"]
  require ((← (← json.getObjVal? "schema").getNat?) == 1) "Use lifecycle replay schema 1."
  let routing ← parseRouting (← json.getObjVal? "routing")
  let values ← (← json.getObjVal? "configs").getArr?
  let mut configs := []
  for index in [:values.size] do
    let config ← (parseConfig values[index]! index).mapError (s!"/configs/{index}: " ++ ·)
    require (!(configs.any (·.id == config.id))) "Configuration IDs must be unique."
    configs := configs ++ [config]
  let initialSource ← stateObservation (← json.getObjVal? "initial")
  let initial := (initialSource.map snapshotState).getD State.initial
  if valid : initial.check = true then
    let values ← (← json.getObjVal? "events").getArr?
    let mut events := []
    for index in [:values.size] do
      let event ← (parseEvent values[index]! index configs).mapError (s!"/events/{index}: " ++ ·)
      events := events ++ [event]
    require (events.any (·.event.isPacket)) "Supply at least one packet event."
    return ⟨routing, configs, initialSource, initial, (State.check_correct _).mp valid, events, json⟩
  else throw "The normalized initial table is invalid."

def Input.parse (text : String) : Except String Input := do
  Input.fromJson (← Import.Json.parse text)

def Input.check (input : Input) : Except String (Report input.routing input.initial input.events) :=
  audit input.routing input.initial input.events

private def classificationText : CTState → String
  | .new => "new"
  | .established => "established"
  | .related => "related"
  | .invalid => "invalid"
  | .untracked => "untracked"

private def dispositionText : Disposition → String
  | .forwarded => "forwarded"
  | .routeDrop => "routeDrop"
  | .forwardDrop => "forwardDrop"
  | .lateDrop => "lateDrop"

def PacketObservation.renderJson (observed : PacketObservation) : Lean.Json :=
  Lean.Json.mkObj [
    ("classification", Lean.toJson (classificationText observed.classification)), ("fresh", Lean.toJson observed.fresh),
    ("afterDestination", Import.PacketFields.headerJson observed.afterDestination),
    ("afterSource", Import.PacketFields.optionalHeaderJson observed.afterSource), ("nextHop", Lean.toJson observed.nextHop),
    ("disposition", Lean.toJson (dispositionText observed.disposition)), ("output", Import.PacketFields.optionalHeaderJson observed.output)]

private def recordJson (record : Record) : Lean.Json := Lean.Json.mkObj [
  ("original", Import.PacketFields.headerJson record.entry.flow.original),
  ("reply", Import.PacketFields.headerJson record.entry.flow.reply),
  ("originalZone", Lean.toJson record.entry.flow.originalZone), ("replyZone", Lean.toJson record.entry.flow.replyZone),
  ("sourceNAT", Lean.toJson record.entry.sourceNAT), ("destinationNAT", Lean.toJson record.entry.destinationNAT),
  ("seenReply", Lean.toJson record.seenReply)]

def stateJson (state : State) : Lean.Json := Lean.toJson (state.records.map recordJson)

namespace Report

def assumptions : List String := [
  "The transport tracker accepts the modeled ordinary TCP/UDP attachment; TCP reopen, replacement, and NF_REPEAT are excluded.",
  "No expiry, concurrent table changes, helpers, related traffic, offload, or hidden clash objects affect the selected traffic.",
  "Routing uses the captured IPv4 main table and trusted interface bindings.",
  "The captured NAT and filter chains form the exclusive modeled hook sequence.",
  "The supplied packet trace is complete for selected traffic; supplied observations are faithful. Null state remains unobserved.",
  "Table comparison ignores timeout seconds, native IDs, iteration order, and supported status bits other than NAT flags and seen-reply.",
  "The theorems concern the Lean model, not kernel C refinement. The native experiment covers UDP, not the full TCP lifecycle."]

def renderJson (report : Report routing initial observations) : Lean.Json := Lean.Json.mkObj [
  ("compliant", Lean.toJson report.compliant), ("scope", Lean.toJson "ordinary-forwarded-packet-lifecycle"),
  ("assumptions", Lean.toJson assumptions),
  ("eventCount", Lean.toJson observations.length), ("final", Lean.toJson (report.final.records.map recordJson)),
  ("findings", Lean.toJson (report.findings.map fun finding => Lean.Json.mkObj [
    ("source", Lean.toJson s!"/events/{finding.observation.index}"),
    ("config", Lean.toJson finding.observation.event.configID), ("matched", Lean.toJson finding.passed),
    ("expected", (finding.result.packet.map (PacketObservation.renderJson ∘ PacketObservation.expected)).getD .null),
    ("observed", (finding.observation.event.packetObservation.map PacketObservation.renderJson).getD .null),
    ("stateObserved", Lean.toJson finding.observation.event.stateObservation.isSome),
    ("stateMatched", Lean.toJson (stateMatches finding.observation.event finding.result.state)),
    ("expectedState", Lean.toJson (finding.result.state.records.map recordJson))]))]

def render (report : Report routing initial observations) : String :=
  String.intercalate "\n" ((if report.compliant then "COMPLIANT" else "NONCOMPLIANT") ::
    "Scope: ordinary forwarded-packet lifecycle under supplied route, filter, and NAT snapshots." ::
    (assumptions ++ report.findings.map fun finding =>
      s!"/events/{finding.observation.index}: {if finding.passed then "matched" else "violated"}; " ++
      s!"state {if finding.observation.event.stateObservation.isSome then "observed" else "not observed"}."))

end Report
end Netlib.Check.ConntrackLifecycle
