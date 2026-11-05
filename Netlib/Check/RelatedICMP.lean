import Netlib.Check.MTUForwarding
import Netlib.Protocol.RelatedICMP

/-! Byte-derived UDP and received RELATED ICMP replay over one confirmed table. -/

namespace Netlib.Check.RelatedICMP

open Packet Protocol

abbrev Tracker := MTUForwarding.Tracker
abbrev Config := MTUForwarding.Config
abbrev Environment := MTUForwarding.Environment
abbrev WirePacket := MTUForwarding.WirePacket
abbrev Model := Netlib.Protocol.RelatedICMP.Input

structure CheckedError (bytes : List UInt8) where
  envelope : Import.EthernetIPv4.Envelope
  source : Netlib.Protocol.RelatedICMP.Source
  ethernet : Import.EthernetIPv4.decode bytes = .ok envelope
  decoded : Netlib.Protocol.RelatedICMP.decode envelope.payload = .ok source

def checkErrorBytes (bytes : List UInt8) : Except String (CheckedError bytes) := do
  match ethernet : Import.EthernetIPv4.decode bytes with
  | .error error => throw error
  | .ok envelope =>
    match decoded : Netlib.Protocol.RelatedICMP.decode envelope.payload with
    | .error error => throw error
    | .ok source => return ⟨envelope, source, ethernet, decoded⟩

structure ErrorPacket where
  bytes : List UInt8
  checked : CheckedError bytes

def ErrorPacket.input (packet : ErrorPacket) (zone : Nat) : Model := ⟨zone, packet.checked.source⟩

def Environment.related (environment : Environment) (config : Config) : Netlib.Protocol.RelatedICMP.Pipeline :=
  ⟨config.pipeline environment.routing, environment.mtu⟩

/-- Fragment boundaries are checked independently of equivalent checksum encodings. -/
abbrev FragmentValue := List (IPv4Fragment.Packet × Nat)

def fragmentValue (fragments : List IPv4Fragment.Decoded) : FragmentValue :=
  (fragments.mergeSort fun first second => first.packet.offset.val ≤ second.packet.offset.val).map fun fragment =>
    ({ fragment.packet with payload := [] }, fragment.packet.payload.length)

structure ErrorValue where
  fragments : FragmentValue
  outer : IPv4.Packet
  kind : ICMP.Kind
  quote : IPv4.Packet
  flags : InternetChecksum.Word
  declaredLength : InternetChecksum.Word
  quoteChecksum : Nat
  deriving DecidableEq

def errorValue (fragments : List IPv4Fragment.Decoded) (outer : IPv4.Packet)
    (kind : ICMP.Kind) (quote : IPv4QuotePrefix.Decoded) : ErrorValue :=
  ⟨fragmentValue fragments, { outer with payload := [] }, kind, quote.packet,
    quote.flags, quote.declaredLength, quote.checksum.val % 65535⟩

structure ErrorFamily where
  fragments : List IPv4Fragments.WireFragment
  packet : IPv4.Packet
  icmp : ICMP.Decoded
  quote : IPv4QuotePrefix.Decoded
  reassembled : IPv4Fragmentation.reassemble (fragments.map (·.checked.fragment)) = .ok packet
  protocol : packet.protocol = Packet.Protocol.icmp
  transport : ICMP.decode packet.payload = .ok icmp
  quotation : IPv4QuotePrefix.decode icmp.message.quote = .ok quote

def ErrorFamily.value (family : ErrorFamily) : ErrorValue :=
  errorValue (family.fragments.map (·.checked.fragment)) family.packet family.icmp.message.kind family.quote

def checkErrorFamily (bytes : List (List UInt8)) : Except String ErrorFamily := do
  let fragments ← bytes.mapM fun bytes => do
    return (⟨bytes, ← IPv4Fragments.checkBytes bytes⟩ : IPv4Fragments.WireFragment)
  match reassembled : IPv4Fragmentation.reassemble (fragments.map (·.checked.fragment)) with
  | .error error => throw error
  | .ok packet =>
    if protocol : packet.protocol = Packet.Protocol.icmp then
      match transport : ICMP.decode packet.payload with
      | .error error => throw error
      | .ok icmp =>
        match quotation : IPv4QuotePrefix.decode icmp.message.quote with
        | .error error => throw error
        | .ok quote => return ⟨fragments, packet, icmp, quote, reassembled, protocol, transport, quotation⟩
    else throw "The reassembled IPv4 packet must carry ICMP."

def emissionValue (emission : Netlib.Protocol.RelatedICMP.Emission before input) : ErrorValue :=
  errorValue emission.family.fragments emission.association.packet emission.association.message.kind emission.association.quote

structure UDPObservation where
  forwarded : Option IPv4Fragments.Family

def UDPObservation.base (observed : UDPObservation) : MTUForwarding.PacketObservation :=
  ⟨none, none, none, none, none, none, none, observed.forwarded⟩

structure ErrorObservation where
  forwarded : Option ErrorFamily

def ErrorObservation.Matches (observed : ErrorObservation)
    (outcome : Netlib.Protocol.RelatedICMP.Outcome before input) : Prop :=
  observed.forwarded.map ErrorFamily.value = outcome.output.map emissionValue

def ErrorObservation.matches (observed : ErrorObservation)
    (outcome : Netlib.Protocol.RelatedICMP.Outcome before input) : Bool :=
  decide (observed.forwarded.map ErrorFamily.value = outcome.output.map emissionValue)

theorem ErrorObservation.matches_correct (observed : ErrorObservation)
    (outcome : Netlib.Protocol.RelatedICMP.Outcome before input) :
    observed.matches outcome = true ↔ observed.Matches outcome := by
  simp [ErrorObservation.matches, ErrorObservation.Matches]

inductive Event where
  | udp (config : Config) (zone : Nat) (packet : WirePacket) (observed : UDPObservation)
      (state : Option Import.ConntrackNetlink.Snapshot)
  | icmp (config : Config) (zone : Nat) (packet : ErrorPacket) (observed : ErrorObservation)
      (state : Option Import.ConntrackNetlink.Snapshot)
  | erase (zone : Nat) (packet : WirePacket) (state : Option Import.ConntrackNetlink.Snapshot)

def Event.stateObservation : Event → Option Import.ConntrackNetlink.Snapshot
  | .udp _ _ _ _ state | .icmp _ _ _ _ state | .erase _ _ state => state

structure ErrorResult where
  before : Tracker
  input : Model
  outcome : Netlib.Protocol.RelatedICMP.Outcome before input

structure Result where
  state : Tracker
  valid : state.Valid
  udp : Option MTUForwarding.PacketResult := none
  icmp : Option ErrorResult := none

def step (environment : Environment) (before : Tracker) : Event → Except String Result
  | .udp config zone packet observed state => do
    let result ← MTUForwarding.step environment before (.packet config zone packet observed.base state)
    return ⟨result.state, result.valid, result.packet, none⟩
  | .icmp config zone packet _ _ => do
    let input := packet.input zone
    let outcome ← (Netlib.Protocol.RelatedICMP.step (environment.related config) before input).mapError (·.describe)
    return ⟨before, outcome.valid, none, some ⟨before, input, outcome⟩⟩
  | .erase zone packet state => do
    let result ← MTUForwarding.step environment before (.erase zone packet state)
    return ⟨result.state, result.valid, none, none⟩

structure Observation where
  index : Nat
  event : Event
  raw : Lean.Json

def StateMatches (event : Event) (after : Tracker) : Prop :=
  ∀ snapshot, event.stateObservation = some snapshot →
    ConntrackLifecycle.SameRecords after (ConntrackLifecycle.snapshotState snapshot)

def stateMatches (event : Event) (after : Tracker) : Bool :=
  match event.stateObservation with
  | none => true
  | some snapshot => ConntrackLifecycle.sameRecords after (ConntrackLifecycle.snapshotState snapshot)

theorem stateMatches_correct (event : Event) (after : Tracker) :
    stateMatches event after = true ↔ StateMatches event after := by
  cases source : event.stateObservation <;> simp [stateMatches, StateMatches, source,
    ConntrackLifecycle.sameRecords_correct]

def PacketMatches (event : Event) (result : Result) : Prop :=
  match event, result.udp, result.icmp with
  | .udp _ _ _ observed _, some packet, none => observed.base.Matches packet.outcome
  | .icmp _ _ _ observed _, none, some packet => observed.Matches packet.outcome
  | .erase .., none, none => True
  | _, _, _ => False

def packetMatches (event : Event) (result : Result) : Bool :=
  match event, result.udp, result.icmp with
  | .udp _ _ _ observed _, some packet, none => observed.base.matches packet.outcome
  | .icmp _ _ _ observed _, none, some packet => observed.matches packet.outcome
  | .erase .., none, none => true
  | _, _, _ => false

theorem packetMatches_correct (event : Event) (result : Result) :
    packetMatches event result = true ↔ PacketMatches event result := by
  cases result with
  | mk state valid udp icmp =>
    cases event <;> cases udp <;> cases icmp <;>
      simp [packetMatches, PacketMatches, MTUForwarding.PacketObservation.matches_correct,
        ErrorObservation.matches_correct]

def Matches (observation : Observation) (result : Result) : Prop :=
  PacketMatches observation.event result ∧ StateMatches observation.event result.state

abbrev Finding := Replay.Finding Observation Result

def replay (environment : Environment) : Replay.System Tracker Observation Result where
  step before observation := step environment before observation.event
  state := Result.state
  passed observation result := packetMatches observation.event result && stateMatches observation.event result.state
  Matches := Matches
  correct observation result := by simp [Matches, packetMatches_correct, stateMatches_correct]

abbrev Agreement (environment : Environment) := Replay.Agreement (replay environment)
abbrev Trace (environment : Environment) := Replay.Trace (replay environment)
abbrev Report (environment : Environment) := Replay.Report (replay environment)

def audit (environment : Environment) (initial : Tracker) (observations : List Observation) :
    Except String (Report environment initial observations) := Replay.audit (replay environment) initial observations

def Report.compliant (report : Report environment initial observations) : Bool := report.findings.all (·.passed)

theorem Report.compliant_iff (report : Report environment initial observations) :
    report.compliant = true ↔ Agreement environment initial observations := report.correct

theorem Report.valid (report : Report environment initial observations) (valid : initial.Valid) :
    report.final.Valid ∧ ∀ finding ∈ report.findings, finding.result.state.Valid :=
  report.trace.invariant Netlib.Protocol.ConntrackLifecycle.State.Valid (fun _ _ result _ _ => result.valid) valid

theorem step_icmp (environment : Environment) (before : Tracker) (config : Config)
    (zone : Nat) (packet : ErrorPacket) (observed : ErrorObservation)
    (state : Option Import.ConntrackNetlink.Snapshot) (result : Result)
    (accepted : step environment before (.icmp config zone packet observed state) = .ok result) :
    ∃ outcome, Netlib.Protocol.RelatedICMP.step (environment.related config) before (packet.input zone) = .ok outcome ∧
      result.state = before ∧ result.udp = none ∧ result.icmp = some ⟨before, packet.input zone, outcome⟩ := by
  cases computed : Netlib.Protocol.RelatedICMP.step (environment.related config) before (packet.input zone) with
  | error error => simp [step, computed, Except.mapError, bind, Except.bind] at accepted
  | ok outcome =>
    simp [step, computed, Except.mapError, bind, Except.bind, pure] at accepted
    cases accepted
    exact ⟨outcome, rfl, rfl, rfl, rfl⟩

theorem Report.observed_output (report : Report environment initial observations)
    (compliant : report.compliant = true) (finding : Finding) (member : finding ∈ report.findings)
    (config : Config) (zone : Nat) (packet : ErrorPacket) (observed : ErrorObservation)
    (state : Option Import.ConntrackNetlink.Snapshot)
    (event : finding.observation.event = .icmp config zone packet observed state)
    (output : ErrorFamily) (seen : observed.forwarded = some output) :
    ∃ (before : Tracker) (outcome : Netlib.Protocol.RelatedICMP.Outcome before (packet.input zone))
      (emission : Netlib.Protocol.RelatedICMP.Emission before (packet.input zone)),
      Netlib.Protocol.RelatedICMP.step (environment.related config) before (packet.input zone) = .ok outcome ∧
      outcome.output = some emission ∧ output.value = emissionValue emission ∧ finding.result.state = before := by
  obtain ⟨before, computed⟩ := report.trace.steps finding member
  change step environment before finding.observation.event = .ok finding.result at computed
  rw [event] at computed
  obtain ⟨outcome, stepped, frozen, noUDP, stored⟩ := step_icmp environment before config zone packet observed state finding.result computed
  have matched := (Replay.Report.finding_matches report compliant finding member).1
  change PacketMatches finding.observation.event finding.result at matched
  rw [event] at matched
  simp only [PacketMatches, noUDP, stored, ErrorObservation.Matches] at matched
  rw [seen] at matched
  cases emitted : outcome.output with
  | none => simp [emitted] at matched
  | some emission =>
    simp only [emitted, Option.map_some, Option.some.injEq] at matched
    exact ⟨before, outcome, emission, stepped, emitted, matched, frozen⟩

/-- Output evidence carries the actual reverse-quote association and both NAT stages. -/
structure OutputFacts (before : Tracker) (input : Model) (output : ErrorFamily)
    (emission : Netlib.Protocol.RelatedICMP.Emission before input) : Prop where
  compared : output.value = emissionValue emission
  member : emission.association.record ∈ before.records
  key : emission.association.entry.flow.key emission.association.direction =
    (input.zone, (IPv4QuotePrefix.header input.source.quote).reverse)
  destination : input.source.ip.packet.destination =
    (emission.association.entry.flow.input emission.association.direction).destination
  destinationStage : IPv4QuotePrefix.header emission.association.destinationQuote = emission.association.innerDestinationTarget
  sourceStage : IPv4QuotePrefix.header emission.association.quote = emission.association.innerSourceTarget
  quoteHeader : IPv4QuotePrefix.header emission.association.quote =
    emission.association.entry.flow.input (Netlib.Protocol.RelatedICMP.opposite emission.association.direction)
  appPrefix : emission.association.quote.packet.payload.drop 8 = input.source.quote.packet.payload.drop 8
  checksumValidity : InternetChecksum.valid (IPv4QuotePrefix.headerBytes emission.association.quote) =
    InternetChecksum.valid (IPv4QuotePrefix.headerBytes input.source.quote)
  checksumOmission : ICMPNAT.quotedChecksum emission.association.quote.packet.payload = 0 ↔
    ICMPNAT.quotedChecksum input.source.quote.packet.payload = 0
  ttl : emission.association.packet.ttl.toNat = input.source.ip.packet.ttl.toNat - 1

theorem Report.observed_output_facts (report : Report environment initial observations)
    (compliant : report.compliant = true) (finding : Finding) (member : finding ∈ report.findings)
    (config : Config) (zone : Nat) (packet : ErrorPacket) (observed : ErrorObservation)
    (state : Option Import.ConntrackNetlink.Snapshot)
    (event : finding.observation.event = .icmp config zone packet observed state)
    (output : ErrorFamily) (seen : observed.forwarded = some output) :
    ∃ (before : Tracker) (outcome : Netlib.Protocol.RelatedICMP.Outcome before (packet.input zone))
      (emission : Netlib.Protocol.RelatedICMP.Emission before (packet.input zone)),
      Netlib.Protocol.RelatedICMP.step (environment.related config) before (packet.input zone) = .ok outcome ∧
      outcome.output = some emission ∧ finding.result.state = before ∧ OutputFacts before (packet.input zone) output emission := by
  obtain ⟨before, outcome, emission, stepped, emitted, same, frozen⟩ :=
    report.observed_output compliant finding member config zone packet observed state event output seen
  exact ⟨before, outcome, emission, stepped, emitted, frozen, same, emission.association.member,
    emission.association.attached, emission.association.outerDestination, emission.association.destinationQuote_header,
    emission.association.sourceQuote_header, emission.association.quote_header, emission.association.quoted_app_prefix,
    emission.association.quoted_ip_checksum, emission.association.quoted_checksum_omission, emission.association.ttl⟩

structure Input where
  environment : Environment
  configs : List Config
  initial : Tracker
  initialValid : initial.Valid
  events : List Observation

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def stateObservation (json : Lean.Json) : Except String (Option Import.ConntrackNetlink.Snapshot) :=
  match json with
  | .null => .ok none
  | value => some <$> Import.ConntrackNetlink.Snapshot.fromJson value

private def wirePacket (json : Lean.Json) : Except String WirePacket := do
  let bytes ← Import.EAPOL.bytesFromHex (← json.getStr?)
  return ⟨bytes, ← Wire.checkBytes bytes⟩

private def errorPacket (json : Lean.Json) : Except String ErrorPacket := do
  let bytes ← Import.EAPOL.bytesFromHex (← json.getStr?)
  return ⟨bytes, ← checkErrorBytes bytes⟩

private def outputBytes (json : Lean.Json) : Except String (List (List UInt8)) := do
  (← json.getArr?).toList.mapM fun value => do Import.EAPOL.bytesFromHex (← value.getStr?)

private def observedBytes (json : Lean.Json) : Except String (List (List UInt8)) := do
  Import.PacketFields.fields json ["forwarded", "icmpOutput"]
  require (← (← json.getObjVal? "icmpOutput").getArr?).isEmpty
    "Locally generated ICMP output is outside the received-error replay scope."
  outputBytes (← json.getObjVal? "forwarded")

private def udpObservation (json : Lean.Json) : Except String UDPObservation := do
  let bytes ← observedBytes json
  return ⟨← if bytes.isEmpty then pure none else some <$> IPv4Fragments.checkFamily bytes⟩

private def errorObservation (json : Lean.Json) : Except String ErrorObservation := do
  let bytes ← observedBytes json
  return ⟨← if bytes.isEmpty then pure none else some <$> checkErrorFamily bytes⟩

def Input.fromJson (json : Lean.Json) : Except String Input := do
  Import.PacketFields.fields json ["schema", "routing", "mtus", "configs", "initial", "events"]
  let base ← MTUForwarding.domainFromJson json
  let values ← (← json.getObjVal? "events").getArr?
  let mut events := []
  for index in [:values.size] do
    let value := values[index]!
    let kind ← (← value.getObjVal? "type").getStr?
    let zone ← (← value.getObjVal? "zone").getNat?
    require (zone < 65536) "A conntrack zone must fit in 16 bits."
    let state ← stateObservation (← value.getObjVal? "state")
    let event ← if kind == "erase" then do
        Import.PacketFields.fields value ["type", "zone", "raw", "state"]
        pure (.erase zone (← wirePacket (← value.getObjVal? "raw")) state)
      else do
        Import.PacketFields.fields value ["type", "config", "zone", "raw", "observed", "state"]
        let id ← (← value.getObjVal? "config").getStr?
        let some config := base.configs.find? (·.id == id) | throw s!"Unknown related forwarding configuration: {id}."
        match kind with
        | "udp" => pure (.udp config zone (← wirePacket (← value.getObjVal? "raw"))
            (← udpObservation (← value.getObjVal? "observed")) state)
        | "icmp" => pure (.icmp config zone (← errorPacket (← value.getObjVal? "raw"))
            (← errorObservation (← value.getObjVal? "observed")) state)
        | _ => throw s!"Unsupported related forwarding event: {kind}."
    events := events ++ [⟨index, event, value⟩]
  require (events.any fun observation => match observation.event with | .erase .. => false | _ => true)
    "Supply at least one UDP or received ICMP event."
  return ⟨base.environment, base.configs, base.initial, base.initialValid, events⟩

def Input.parse (text : String) : Except String Input := do Input.fromJson (← Import.Json.parse text)

def Input.check (input : Input) : Except String (Report input.environment input.initial input.events) :=
  audit input.environment input.initial input.events

private def udpDispositionText : Netlib.Protocol.MTUForwarding.Disposition → String
  | .forwarded => "forwarded" | .routeDrop => "routeDrop" | .ttlExpired => "ttlExpired"
  | .mtuExceeded => "mtuExceeded" | .forwardDrop => "forwardDrop" | .lateDrop => "lateDrop"

private def errorDispositionText : Netlib.Protocol.RelatedICMP.Disposition → String
  | .unrelated => "unrelated" | .forwarded => "forwarded" | .routeDrop => "routeDrop"
  | .ttlExpired => "ttlExpired" | .mtuExceeded => "mtuExceeded" | .forwardDrop => "forwardDrop" | .lateDrop => "lateDrop"

private def kindJson : ICMP.Kind → Lean.Json
  | .timeExceeded => Lean.Json.mkObj [("type", Lean.toJson (11 : Nat)), ("code", Lean.toJson (0 : Nat))]
  | .fragmentationNeeded mtu => Lean.Json.mkObj [("type", Lean.toJson (3 : Nat)),
      ("code", Lean.toJson (4 : Nat)), ("mtu", Lean.toJson mtu.val)]

private def rawOutputJson (bytes : List (List UInt8)) : Lean.Json :=
  Lean.Json.mkObj [("rawIPv4", Lean.toJson (bytes.map Import.EAPOL.bytesToHex))]

private def outcomeJson (result : Result) : Lean.Json :=
  match result.udp, result.icmp with
  | some packet, _ => Lean.Json.mkObj [
      ("type", Lean.toJson "udp"), ("disposition", Lean.toJson (udpDispositionText packet.outcome.disposition)),
      ("afterDestination", Import.PacketFields.headerJson packet.outcome.afterDestination),
      ("afterSource", Import.PacketFields.optionalHeaderJson packet.outcome.afterSource),
      ("nextHop", Lean.toJson packet.outcome.nextHop), ("mtu", Lean.toJson (packet.outcome.selectedMTU.map (·.val))),
      ("output", (packet.outcome.output.map fun output => rawOutputJson output.bytes).getD .null)]
  | _, some packet => Lean.Json.mkObj [
      ("type", Lean.toJson "icmp"), ("disposition", Lean.toJson (errorDispositionText packet.outcome.disposition)),
      ("associated", Lean.toJson packet.outcome.association.isSome),
      ("afterDestination", Import.PacketFields.optionalHeaderJson packet.outcome.afterDestination),
      ("afterSource", Import.PacketFields.optionalHeaderJson packet.outcome.afterSource),
      ("nextHop", Lean.toJson packet.outcome.nextHop), ("kind", kindJson packet.input.source.icmp.message.kind),
      ("output", (packet.outcome.output.map fun output => rawOutputJson output.family.bytes).getD .null)]
  | _, _ => Lean.Json.mkObj [("type", Lean.toJson "erase")]

def Report.assumptions : List String := [
  "Raw Ethernet bytes identify the complete selected input and output family; adjacency and padding are ignored.",
  "Routes, effective MTUs, NAT and filter snapshots remain stable at the declared hooks.",
  "UDP attachment and administrative erasure use the modeled ordinary conntrack table.",
  "Received ICMP association uses the reverse quoted tuple, zone and outer destination; the outer source is unauthenticated.",
  "Outer IPv4 and ICMP checksums are verified; quoted checksums, lengths and raw flags remain untrusted data.",
  "Received errors preserve conntrack state and produce no further ICMP error on TTL or MTU failure.",
  "Strict reassembly rejects overlaps, gaps, duplicates and mixed metadata; allocation and output succeed.",
  "Fragment fields, boundaries and recovered ICMP/quote data are compared, ignoring equivalent checksum zero encodings.",
  "The capture excludes locally generated control output, concurrency, expiry, helpers, offload and additional encapsulation.",
  "Table comparison ignores native IDs, order and timeout seconds; observations never replace computed state.",
  "These proofs concern the Lean model and supplied observations; native refinement remains a separate claim."]

def Report.renderJson (report : Report environment initial observations) : Lean.Json := Lean.Json.mkObj [
  ("compliant", Lean.toJson report.compliant), ("scope", Lean.toJson "received-icmp-tracked-forwarding"),
  ("assumptions", Lean.toJson Report.assumptions), ("eventCount", Lean.toJson observations.length),
  ("final", ConntrackLifecycle.stateJson report.final),
  ("findings", Lean.toJson (report.findings.map fun finding => Lean.Json.mkObj [
    ("source", Lean.toJson s!"/events/{finding.observation.index}"), ("matched", Lean.toJson finding.passed),
    ("expected", outcomeJson finding.result), ("observed", finding.observation.raw),
    ("stateObserved", Lean.toJson finding.observation.event.stateObservation.isSome),
    ("stateMatched", Lean.toJson (stateMatches finding.observation.event finding.result.state)),
    ("expectedState", ConntrackLifecycle.stateJson finding.result.state)]))]

def Report.render (report : Report environment initial observations) : String :=
  (if report.compliant then "RELATED ICMP OBSERVATIONS MATCH\n" else "RELATED ICMP OBSERVATIONS MISMATCH\n") ++ report.renderJson.pretty

end Netlib.Check.RelatedICMP
