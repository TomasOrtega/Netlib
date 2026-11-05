import Netlib.Check.ConntrackLifecycle
import Netlib.Check.Wire
import Netlib.Check.Replay
import Netlib.Protocol.WireForwarding

/-!
# Byte-derived tracked forwarding replay

Input and output packet fields come from checked Ethernet bytes.
Null intermediate fields are unobserved; null output asserts no selected UDP transit output.
Native snapshots retain the existing ordinary-table comparison scope.
-/

namespace Netlib.Check.WireForwarding

open Packet Protocol
abbrev Tracker := Netlib.Protocol.ConntrackLifecycle.State
abbrev Config := Check.ConntrackLifecycle.Config

structure WirePacket where
  bytes : List UInt8
  checked : Check.Wire.Checked bytes

def WirePacket.value (packet : WirePacket) : IPv4.Packet × UDP.Datagram :=
  (packet.checked.packet.ip.packet, packet.checked.packet.datagram)

def emissionValue (emission : Netlib.Protocol.WireForwarding.Emission packet) : IPv4.Packet × UDP.Datagram :=
  (emission.decoded.ip.packet, emission.decoded.datagram)

private def agrees [DecidableEq α] (observed : Option α) (expected : α) : Bool :=
  match observed with
  | none => true
  | some value => decide (expected = value)

private def Agrees (observed : Option α) (expected : α) : Prop :=
  ∀ value, observed = some value → expected = value

private theorem agrees_correct [DecidableEq α] (observed : Option α) (expected : α) :
    agrees observed expected = true ↔ Agrees observed expected := by
  cases observed <;> simp [agrees, Agrees]

structure PacketObservation where
  classification : Option StatefulACL.CTState
  fresh : Option Bool
  afterDestination : Option Header
  afterSource : Option Header
  nextHop : Option String
  disposition : Option Netlib.Protocol.WireForwarding.Disposition
  output : Option WirePacket

def PacketObservation.Matches (observed : PacketObservation) (outcome : Netlib.Protocol.WireForwarding.Outcome packet) : Prop :=
  Agrees observed.classification outcome.attachment.classification ∧
    Agrees observed.fresh outcome.attachment.fresh ∧ Agrees observed.afterDestination outcome.afterDestination ∧
    Agrees (observed.afterSource.map some) outcome.afterSource ∧ Agrees (observed.nextHop.map some) outcome.nextHop ∧
    Agrees observed.disposition outcome.disposition ∧
    observed.output.map WirePacket.value = outcome.output.map emissionValue

def PacketObservation.matches (observed : PacketObservation) (outcome : Netlib.Protocol.WireForwarding.Outcome packet) : Bool :=
  agrees observed.classification outcome.attachment.classification &&
    agrees observed.fresh outcome.attachment.fresh && agrees observed.afterDestination outcome.afterDestination &&
    agrees (observed.afterSource.map some) outcome.afterSource && agrees (observed.nextHop.map some) outcome.nextHop &&
    agrees observed.disposition outcome.disposition &&
    decide (observed.output.map WirePacket.value = outcome.output.map emissionValue)

theorem PacketObservation.matches_correct (observed : PacketObservation) (outcome : Netlib.Protocol.WireForwarding.Outcome packet) :
    observed.matches outcome = true ↔ observed.Matches outcome := by
  simp [PacketObservation.matches, PacketObservation.Matches, agrees_correct, and_assoc]

inductive Event where
  | packet (config : Config) (zone : Nat) (packet : WirePacket) (observed : PacketObservation)
      (state : Option Import.ConntrackNetlink.Snapshot)
  | erase (zone : Nat) (packet : WirePacket) (state : Option Import.ConntrackNetlink.Snapshot)

def Event.stateObservation : Event → Option Import.ConntrackNetlink.Snapshot
  | .packet _ _ _ _ state | .erase _ _ state => state

def Event.isPacket : Event → Bool
  | .packet .. => true
  | .erase .. => false

def packetInput (before : Tracker) (config : Config) (zone : Nat) (packet : WirePacket) : Netlib.Protocol.WireForwarding.Input :=
  ⟨zone, packet.checked.packet,
    if (before.model.lookup zone packet.checked.header).isNone then
      some (config.nat.candidate zone packet.checked.header) else none⟩

structure PacketResult where
  input : Netlib.Protocol.WireForwarding.Input
  outcome : Netlib.Protocol.WireForwarding.Outcome input.packet

structure Result where
  state : Tracker
  valid : state.Valid
  packet : Option PacketResult

def step (routing : Import.LinuxRoute.Snapshot) (before : Tracker) : Event → Except String Result
  | .packet config zone packet _ _ => do
    let input := packetInput before config zone packet
    let outcome ← (Netlib.Protocol.WireForwarding.step (config.pipeline routing) before input).mapError (·.describe)
    return ⟨outcome.state, outcome.valid, some ⟨input, outcome⟩⟩
  | .erase zone packet _ => do
    let erased ← (Netlib.Protocol.ConntrackLifecycle.Operations.step before (.erase zone packet.checked.header)).mapError (·.describe)
    return ⟨erased.state, erased.valid, none⟩

structure Observation where
  index : Nat
  event : Event
  raw : Lean.Json

def StateMatches (event : Event) (after : Tracker) : Prop :=
  ∀ snapshot, event.stateObservation = some snapshot →
    Check.ConntrackLifecycle.SameRecords after (Check.ConntrackLifecycle.snapshotState snapshot)

def stateMatches (event : Event) (after : Tracker) : Bool :=
  match event.stateObservation with
  | none => true
  | some snapshot => Check.ConntrackLifecycle.sameRecords after (Check.ConntrackLifecycle.snapshotState snapshot)

theorem stateMatches_correct (event : Event) (after : Tracker) :
    stateMatches event after = true ↔ StateMatches event after := by
  cases source : event.stateObservation <;> simp [stateMatches, StateMatches, source,
    Check.ConntrackLifecycle.sameRecords_correct]

def PacketMatches (event : Event) (result : Result) : Prop :=
  match event, result.packet with
  | .packet _ _ _ observed _, some packet => observed.Matches packet.outcome
  | .erase .., none => True
  | _, _ => False

def packetMatches (event : Event) (result : Result) : Bool :=
  match event, result.packet with
  | .packet _ _ _ observed _, some packet => observed.matches packet.outcome
  | .erase .., none => true
  | _, _ => false

theorem packetMatches_correct (event : Event) (result : Result) :
    packetMatches event result = true ↔ PacketMatches event result := by
  cases result with
  | mk state valid packet =>
    cases event <;> cases packet <;> simp [packetMatches, PacketMatches, PacketObservation.matches_correct]

def Matches (observation : Observation) (result : Result) : Prop :=
  PacketMatches observation.event result ∧ StateMatches observation.event result.state

abbrev Finding := Replay.Finding Observation Result

abbrev Finding.mk (observation : Observation) (result : Result) (passed : Bool) : Finding :=
  Replay.Finding.mk observation result passed

abbrev Finding.observation (finding : Finding) : Observation := Replay.Finding.observation finding
abbrev Finding.result (finding : Finding) : Result := Replay.Finding.result finding
abbrev Finding.passed (finding : Finding) : Bool := Replay.Finding.passed finding

def finding (observation : Observation) (result : Result) : Finding :=
  ⟨observation, result, packetMatches observation.event result && stateMatches observation.event result.state⟩

theorem finding_correct (observation : Observation) (result : Result) :
    (finding observation result).passed = true ↔ Matches observation result := by
  simp [finding, Finding.passed, Matches, packetMatches_correct, stateMatches_correct]

def replay (routing : Import.LinuxRoute.Snapshot) : Replay.System Tracker Observation Result where
  step before observation := step routing before observation.event
  state := Result.state
  passed observation result := packetMatches observation.event result && stateMatches observation.event result.state
  Matches := Matches
  correct := finding_correct

abbrev Agreement (routing : Import.LinuxRoute.Snapshot) := Replay.Agreement (replay routing)
structure Trace (routing : Import.LinuxRoute.Snapshot) (initial : Tracker) (findings : List Finding)
    (final : Tracker) : Prop where
  execution : Replay.Trace (replay routing) initial findings final

structure Report (routing : Import.LinuxRoute.Snapshot) (initial : Tracker) (observations : List Observation) where
  final : Tracker
  findings : List Finding
  covered : findings.map Finding.observation = observations
  trace : Trace routing initial findings final
  correct : findings.all Finding.passed = true ↔ Agreement routing initial observations

theorem Trace.valid (trace : Trace routing initial findings final) (valid : initial.Valid) :
    final.Valid ∧ ∀ finding ∈ findings, finding.result.state.Valid :=
  Replay.Trace.invariant trace.execution Netlib.Protocol.ConntrackLifecycle.State.Valid
    (fun _ _ result _ _ => result.valid) valid

def audit (routing : Import.LinuxRoute.Snapshot) (initial : Tracker) (observations : List Observation) :
    Except String (Report routing initial observations) := do
  let report ← Replay.audit (replay routing) initial observations
  return ⟨report.final, report.findings, report.covered, ⟨report.trace⟩, report.correct⟩

def Report.compliant (report : Report routing initial observations) : Bool := report.findings.all Finding.passed

theorem Report.compliant_iff (report : Report routing initial observations) :
    report.compliant = true ↔ Agreement routing initial observations := report.correct

theorem Trace.steps (trace : Trace routing initial findings final) :
    ∀ finding ∈ findings, ∃ before, step routing before finding.observation.event = .ok finding.result :=
  Replay.Trace.steps trace.execution

theorem Trace.matches (trace : Trace routing initial findings final)
    (agreement : Agreement routing initial (findings.map Finding.observation)) :
    ∀ finding ∈ findings, Matches finding.observation finding.result :=
  Replay.Trace.matches trace.execution agreement

theorem Report.finding_matches (report : Report routing initial observations) (compliant : report.compliant = true)
    (finding : Finding) (member : finding ∈ report.findings) : Matches finding.observation finding.result := by
  have agreement := report.compliant_iff.mp compliant
  rw [← report.covered] at agreement
  exact Trace.matches report.trace agreement finding member

theorem step_packet (routing : Import.LinuxRoute.Snapshot) (before : Tracker) (config : Config)
    (zone : Nat) (packet : WirePacket) (observed : PacketObservation)
    (state : Option Import.ConntrackNetlink.Snapshot) (result : Result)
    (accepted : step routing before (.packet config zone packet observed state) = .ok result) :
    ∃ outcome, Netlib.Protocol.WireForwarding.step (config.pipeline routing) before
        (packetInput before config zone packet) = .ok outcome ∧
      result.packet = some ⟨packetInput before config zone packet, outcome⟩ := by
  cases computed : Netlib.Protocol.WireForwarding.step (config.pipeline routing) before
      (packetInput before config zone packet) with
  | error error => simp [step, computed, Except.mapError, bind, Except.bind] at accepted
  | ok outcome =>
    simp [step, computed, Except.mapError, bind, Except.bind, pure] at accepted
    cases accepted
    exact ⟨outcome, rfl, rfl⟩

theorem Report.observed_output_payload (report : Report routing initial observations)
    (compliant : report.compliant = true) (finding : Finding) (member : finding ∈ report.findings)
    (config : Config) (zone : Nat) (packet : WirePacket) (observed : PacketObservation)
    (state : Option Import.ConntrackNetlink.Snapshot)
    (event : finding.observation.event = .packet config zone packet observed state)
    (output : WirePacket) (seen : observed.output = some output) :
    output.checked.packet.datagram.payload = packet.checked.packet.datagram.payload ∧
      output.checked.packet.ip.packet.ttl.toNat = packet.checked.packet.ip.packet.ttl.toNat - 1 := by
  obtain ⟨before, computed⟩ := Trace.steps report.trace finding member
  rw [event] at computed
  obtain ⟨outcome, stepped, stored⟩ := step_packet routing before config zone packet observed state finding.result computed
  have matched := (report.finding_matches compliant finding member).1
  rw [event] at matched
  simp only [PacketMatches, stored] at matched
  have same := matched.2.2.2.2.2.2
  rw [seen] at same
  cases emitted : outcome.output with
  | none => simp [emitted] at same
  | some emission =>
    simp only [emitted, Option.map_some, Option.some.injEq] at same
    have payload := congrArg (fun value : IPv4.Packet × UDP.Datagram => value.2.payload) same
    have ttl := congrArg (fun value : IPv4.Packet × UDP.Datagram => value.1.ttl.toNat) same
    exact ⟨payload.trans emission.rewritten.payload,
      ttl.trans ((congrArg UInt8.toNat emission.rewritten.ttl).trans
        (Netlib.Protocol.WireForwarding.decrementTTL_exact packet.checked.packet))⟩

structure Input where
  routing : Import.LinuxRoute.Snapshot
  configs : List Config
  initial : Tracker
  initialValid : initial.Valid
  events : List Observation

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def optional (parse : Lean.Json → Except String α) (json : Lean.Json) : Except String (Option α) :=
  match json with
  | .null => .ok none
  | value => some <$> parse value

private def wirePacket (json : Lean.Json) : Except String WirePacket := do
  let bytes ← Import.EAPOL.bytesFromHex (← json.getStr?)
  return ⟨bytes, ← Check.Wire.checkBytes bytes⟩

private def classification (json : Lean.Json) : Except String StatefulACL.CTState := do
  match ← json.getStr? with
  | "new" => return .new
  | "established" => return .established
  | "related" => return .related
  | "invalid" => return .invalid
  | "untracked" => return .untracked
  | value => throw s!"Unsupported conntrack classification: {value}."

private def disposition (json : Lean.Json) : Except String Netlib.Protocol.WireForwarding.Disposition := do
  match ← json.getStr? with
  | "forwarded" => return .forwarded
  | "routeDrop" => return .routeDrop
  | "ttlExpired" => return .ttlExpired
  | "forwardDrop" => return .forwardDrop
  | "lateDrop" => return .lateDrop
  | value => throw s!"Unsupported wire forwarding disposition: {value}."

private def packetObservation (json : Lean.Json) : Except String PacketObservation := do
  Import.PacketFields.fields json ["classification", "fresh", "afterDestination", "afterSource", "nextHop", "disposition", "output"]
  return ⟨← optional classification (← json.getObjVal? "classification"),
    ← optional Lean.Json.getBool? (← json.getObjVal? "fresh"),
    ← optional Import.PacketFields.header (← json.getObjVal? "afterDestination"),
    ← optional Import.PacketFields.header (← json.getObjVal? "afterSource"),
    ← optional Lean.Json.getStr? (← json.getObjVal? "nextHop"),
    ← optional disposition (← json.getObjVal? "disposition"),
    ← optional wirePacket (← json.getObjVal? "output")⟩

private def stateObservation (json : Lean.Json) : Except String (Option Import.ConntrackNetlink.Snapshot) :=
  optional Import.ConntrackNetlink.Snapshot.fromJson json

def Input.fromJson (json : Lean.Json) : Except String Input := do
  Import.PacketFields.fields json ["schema", "routing", "configs", "initial", "events"]
  require ((← (← json.getObjVal? "schema").getNat?) == 1) "Use wire forwarding schema 1."
  let routing ← Check.ConntrackLifecycle.routingFromJson (← json.getObjVal? "routing")
  let values ← (← json.getObjVal? "configs").getArr?
  let mut configs := []
  for index in [:values.size] do
    let config ← Check.ConntrackLifecycle.Config.fromJson values[index]! index
    require (!(configs.any (·.id == config.id))) "Configuration IDs must be unique."
    configs := configs ++ [config]
  let initialSource ← stateObservation (← json.getObjVal? "initial")
  let initial := (initialSource.map Check.ConntrackLifecycle.snapshotState).getD Netlib.Protocol.ConntrackLifecycle.State.initial
  if valid : initial.check = true then
    let values ← (← json.getObjVal? "events").getArr?
    let mut observations := []
    for index in [:values.size] do
      let value := values[index]!
      let kind ← (← value.getObjVal? "type").getStr?
      let event ← match kind with
        | "packet" => do
          Import.PacketFields.fields value ["type", "config", "zone", "raw", "observed", "state"]
          let id ← (← value.getObjVal? "config").getStr?
          let some config := configs.find? (·.id == id) | throw s!"Unknown wire forwarding configuration: {id}."
          let zone ← (← value.getObjVal? "zone").getNat?
          require (zone < 65536) "A conntrack zone must fit in 16 bits."
          pure (.packet config zone (← wirePacket (← value.getObjVal? "raw"))
            (← packetObservation (← value.getObjVal? "observed")) (← stateObservation (← value.getObjVal? "state")))
        | "erase" => do
          Import.PacketFields.fields value ["type", "zone", "raw", "state"]
          let zone ← (← value.getObjVal? "zone").getNat?
          require (zone < 65536) "A conntrack zone must fit in 16 bits."
          pure (.erase zone (← wirePacket (← value.getObjVal? "raw")) (← stateObservation (← value.getObjVal? "state")))
        | _ => throw s!"Unsupported wire forwarding event: {kind}."
      observations := observations ++ [⟨index, event, value⟩]
    require (observations.any (·.event.isPacket)) "Supply at least one wire packet event."
    return ⟨routing, configs, initial, (Netlib.Protocol.ConntrackLifecycle.State.check_correct _).mp valid, observations⟩
  else throw "The initial ordinary conntrack table is invalid."

def Input.parse (text : String) : Except String Input := do
  Input.fromJson (← Import.Json.parse text)

def Input.check (input : Input) : Except String (Report input.routing input.initial input.events) :=
  audit input.routing input.initial input.events

private def dispositionText : Netlib.Protocol.WireForwarding.Disposition → String
  | .forwarded => "forwarded" | .routeDrop => "routeDrop" | .ttlExpired => "ttlExpired"
  | .forwardDrop => "forwardDrop" | .lateDrop => "lateDrop"

private def classificationText : StatefulACL.CTState → String
  | .new => "new" | .established => "established" | .related => "related"
  | .invalid => "invalid" | .untracked => "untracked"

private def outcomeJson (outcome : Netlib.Protocol.WireForwarding.Outcome packet) : Lean.Json := Lean.Json.mkObj [
  ("classification", Lean.toJson (classificationText outcome.attachment.classification)),
  ("fresh", Lean.toJson outcome.attachment.fresh),
  ("afterDestination", Import.PacketFields.headerJson outcome.afterDestination),
  ("afterSource", Import.PacketFields.optionalHeaderJson outcome.afterSource),
  ("nextHop", Lean.toJson outcome.nextHop), ("disposition", Lean.toJson (dispositionText outcome.disposition)),
  ("output", (outcome.output.map fun emission => Lean.Json.mkObj [
    ("rawIPv4", Lean.toJson (Import.EAPOL.bytesToHex emission.bytes)),
    ("header", Import.PacketFields.headerJson emission.decoded.header),
    ("payloadHex", Lean.toJson (Import.EAPOL.bytesToHex emission.decoded.datagram.payload)),
    ("ttl", Lean.toJson emission.decoded.ip.packet.ttl.toNat),
    ("udpChecksum", Lean.toJson emission.decoded.datagram.checksum.val)]).getD .null)]

private def observationJson : Event → Lean.Json
  | .erase .. => .null
  | .packet _ _ packet observed _ => Lean.Json.mkObj [
    ("inputHeader", Import.PacketFields.headerJson packet.checked.header),
    ("inputTTL", Lean.toJson packet.checked.packet.ip.packet.ttl.toNat),
    ("classification", Lean.toJson (observed.classification.map classificationText)),
    ("fresh", Lean.toJson observed.fresh),
    ("afterDestination", Import.PacketFields.optionalHeaderJson observed.afterDestination),
    ("afterSource", Import.PacketFields.optionalHeaderJson observed.afterSource),
    ("nextHop", Lean.toJson observed.nextHop),
    ("disposition", Lean.toJson (observed.disposition.map dispositionText)),
    ("output", (observed.output.map fun packet => Lean.Json.mkObj [
      ("header", Import.PacketFields.headerJson packet.checked.header),
      ("ttl", Lean.toJson packet.checked.packet.ip.packet.ttl.toNat),
      ("payloadHex", Lean.toJson (Import.EAPOL.bytesToHex packet.checked.packet.datagram.payload)),
      ("udpChecksum", Lean.toJson packet.checked.packet.datagram.checksum.val)]).getD .null)]

def Report.assumptions : List String := [
  "Raw input and output bytes faithfully identify the same selected packet at the declared capture stages.",
  "Captured routes and NAT/filter snapshots form the exclusive stable hook sequence for each selected packet.",
  "The ordinary transport tracker accepts the modeled UDP attachment; concurrency, expiry, helpers, and clash recovery are excluded.",
  "The selected transit path has sufficient MTU and performs no encapsulation or fragmentation.",
  "TTL expiry models no selected UDP transit output; generated ICMP packets and their other effects remain outside the model.",
  "Null intermediate observations are unchecked; null output asserts no selected UDP egress within the complete supplied observation scope.",
  "Output comparison checks decoded IP fields and the complete UDP datagram; Ethernet adjacency and IPv4 checksum zero representation are separate.",
  "Table comparison retains the existing supported NAT/seen-reply projection and ignores native IDs, order, and timeout seconds.",
  "These proofs concern the Lean model and supplied replay, not kernel implementation refinement or global policy-installation timing."]

def Report.renderJson (report : Report routing initial observations) : Lean.Json := Lean.Json.mkObj [
  ("compliant", Lean.toJson report.compliant), ("scope", Lean.toJson "byte-derived-ipv4-udp-tracked-forwarding"),
  ("assumptions", Lean.toJson Report.assumptions), ("eventCount", Lean.toJson observations.length),
  ("final", Check.ConntrackLifecycle.stateJson report.final),
  ("findings", Lean.toJson (report.findings.map fun finding => Lean.Json.mkObj [
    ("source", Lean.toJson s!"/events/{finding.observation.index}"), ("matched", Lean.toJson finding.passed),
    ("expected", (finding.result.packet.map fun packet => outcomeJson packet.outcome).getD .null),
    ("observed", observationJson finding.observation.event),
    ("stateObserved", Lean.toJson finding.observation.event.stateObservation.isSome),
    ("stateMatched", Lean.toJson (stateMatches finding.observation.event finding.result.state)),
    ("expectedState", Check.ConntrackLifecycle.stateJson finding.result.state)]))]

def Report.render (report : Report routing initial observations) : String :=
  (if report.compliant then "WIRE FORWARDING OBSERVATIONS MATCH\n" else "WIRE FORWARDING OBSERVATIONS MISMATCH\n") ++
    report.renderJson.pretty

end Netlib.Check.WireForwarding
