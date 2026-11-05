import Netlib.Check.MTUForwarding
import Netlib.Check.ICMPError
import Netlib.Protocol.ICMPForwardingFacts

namespace Netlib.Check.ICMPForwarding

open Packet Protocol

abbrev Tracker := MTUForwarding.Tracker

structure Profile where
  outerTtl : UInt8
  broadcasts : List Address

structure Environment where
  transit : MTUForwarding.Environment
  profile : Profile

structure Config where
  id : String
  output : Import.NftablesStateful.Snapshot
  icmpLate : Import.NftablesStateful.Snapshot

def Environment.returnPath (environment : Environment) (address : Address) :
    Option Netlib.Protocol.ICMPForwarding.ReturnPath := do
  let route ← environment.transit.routing.selected address
  let hop ← route.nextNode
  let source ← route.preferredSource
  return ⟨hop, source, environment.transit.mtu hop, environment.profile.outerTtl⟩

def Environment.pipeline (environment : Environment) (config : Config) (transit : MTUForwarding.Config) :
    Netlib.Protocol.ICMPForwarding.Pipeline :=
  ⟨environment.transit.pipeline transit,
    ⟨environment.returnPath, environment.profile.broadcasts, config.output.compile, config.output.policy,
      config.icmpLate.compile, config.icmpLate.policy⟩⟩

structure ICMPFrame where
  bytes : List UInt8
  checked : ICMPError.Checked bytes

def ICMPFrame.value (frame : ICMPFrame) : ICMPError.Value := frame.checked.value

def emissionValue (emission : Netlib.Protocol.ICMPForwarding.Emission source) : ICMPError.Value :=
  ({ emission.packet with payload := [] }, emission.kind, emission.quote.packet, emission.quote.declaredLength)

structure Observation where
  base : MTUForwarding.Observation
  config : Option Config
  icmpOutput : Option ICMPFrame

structure PacketResult where
  input : Netlib.Protocol.ICMPForwarding.Input
  outcome : Netlib.Protocol.ICMPForwarding.Outcome input.transit.packet

structure Result where
  state : Tracker
  valid : state.Valid
  packet : Option PacketResult

def Result.base (result : Result) : MTUForwarding.Result :=
  ⟨result.state, result.valid, result.packet.map fun packet => ⟨packet.input.transit, packet.outcome.transit⟩⟩

def packetInput (before : Tracker) (config : MTUForwarding.Config) (zone : Nat)
    (packet : MTUForwarding.WirePacket) : Netlib.Protocol.ICMPForwarding.Input :=
  ⟨MTUForwarding.packetInput before config zone packet, packet.checked.envelope.destination.a.toNat % 2 == 1⟩

def Observation.identification (observation : Observation) : InternetChecksum.Word :=
  (observation.icmpOutput.map (·.checked.ip.packet.identification)).getD 0

def step (environment : Environment) (before : Tracker) (observation : Observation) : Except String Result := do
  match observation.base.event with
  | .packet config zone packet _ _ =>
    let some control := observation.config | throw "A packet needs an ICMP output configuration."
    let input := packetInput before config zone packet
    let outcome ← (Netlib.Protocol.ICMPForwarding.step (environment.pipeline control config) before input
      observation.identification).mapError (·.describe)
    return ⟨outcome.transit.state, outcome.transit.valid, some ⟨input, outcome⟩⟩
  | .erase zone packet _ =>
    let erased ← (Netlib.Protocol.ConntrackLifecycle.Operations.step before
      (.erase zone packet.checked.header)).mapError (·.describe)
    return ⟨erased.state, erased.valid, none⟩

def Result.icmpValue (result : Result) : Option ICMPError.Value := do
  let packet ← result.packet
  let emission ← packet.outcome.control.output
  return emissionValue emission

def Matches (observation : Observation) (result : Result) : Prop :=
  MTUForwarding.Matches observation.base result.base ∧
    observation.icmpOutput.map ICMPFrame.value = result.icmpValue

def observationMatches (observation : Observation) (result : Result) : Bool :=
  MTUForwarding.packetMatches observation.base.event result.base &&
    MTUForwarding.stateMatches observation.base.event result.state &&
    decide (observation.icmpOutput.map ICMPFrame.value = result.icmpValue)

theorem matches_correct (observation : Observation) (result : Result) :
    observationMatches observation result = true ↔ Matches observation result := by
  simp [observationMatches, Matches, MTUForwarding.Matches, MTUForwarding.packetMatches_correct,
    MTUForwarding.stateMatches_correct, Result.base, and_assoc]

def replay (environment : Environment) : Replay.System Tracker Observation Result where
  step := step environment
  state := Result.state
  passed := observationMatches
  Matches := Matches
  correct := matches_correct

abbrev Finding := Replay.Finding Observation Result
abbrev Agreement (environment : Environment) := Replay.Agreement (replay environment)
structure Report (environment : Environment) (initial : Tracker) (observations : List Observation)
    extends Replay.Report (replay environment) initial observations

def audit (environment : Environment) (initial : Tracker) (observations : List Observation) :
    Except String (Report environment initial observations) := do
  return ⟨← Replay.audit (replay environment) initial observations⟩

def Report.compliant (report : Report environment initial observations) : Bool := report.findings.all (·.passed)

theorem Report.compliant_iff (report : Report environment initial observations) :
    report.compliant = true ↔ Agreement environment initial observations := report.correct

theorem Report.valid (report : Report environment initial observations) (valid : initial.Valid) :
    report.final.Valid ∧ ∀ finding ∈ report.findings, finding.result.state.Valid :=
  report.trace.invariant Netlib.Protocol.ConntrackLifecycle.State.Valid (fun _ _ result _ _ => result.valid) valid

theorem Report.finding_matches (report : Report environment initial observations) (compliant : report.compliant = true)
    (finding : Finding) (member : finding ∈ report.findings) : Matches finding.observation finding.result :=
  Replay.Report.finding_matches report.toReport compliant finding member

theorem step_packet (environment : Environment) (before : Tracker) (observation : Observation)
    (config : MTUForwarding.Config) (zone : Nat) (packet : MTUForwarding.WirePacket)
    (observed : MTUForwarding.PacketObservation) (state : Option Import.ConntrackNetlink.Snapshot)
    (control : Config) (event : observation.base.event = .packet config zone packet observed state)
    (configured : observation.config = some control) (result : Result)
    (accepted : step environment before observation = .ok result) :
    ∃ outcome, Netlib.Protocol.ICMPForwarding.step (environment.pipeline control config) before
        (packetInput before config zone packet) observation.identification = .ok outcome ∧
      result.packet = some ⟨packetInput before config zone packet, outcome⟩ := by
  cases computed : Netlib.Protocol.ICMPForwarding.step (environment.pipeline control config) before
      (packetInput before config zone packet) observation.identification with
  | error error => simp [step, event, configured, computed, Except.mapError, bind, Except.bind] at accepted
  | ok outcome =>
    simp [step, event, configured, computed, Except.mapError, bind, Except.bind, pure] at accepted
    cases accepted
    exact ⟨outcome, rfl, rfl⟩

theorem Report.observed_output (report : Report environment initial observations)
    (compliant : report.compliant = true) (finding : Finding) (member : finding ∈ report.findings)
    (config : MTUForwarding.Config) (zone : Nat) (packet : MTUForwarding.WirePacket)
    (observed : MTUForwarding.PacketObservation) (state : Option Import.ConntrackNetlink.Snapshot)
    (control : Config) (event : finding.observation.base.event = .packet config zone packet observed state)
    (configured : finding.observation.config = some control) (output : ICMPFrame)
    (seen : finding.observation.icmpOutput = some output) :
    ∃ (before : Tracker) (outcome : Netlib.Protocol.ICMPForwarding.Outcome packet.checked.packet)
      (emission : Netlib.Protocol.ICMPForwarding.Emission packet.checked.packet),
      Netlib.Protocol.ICMPForwarding.step (environment.pipeline control config) before
        (packetInput before config zone packet) finding.observation.identification = .ok outcome ∧
      outcome.control.output = some emission ∧ output.value = emissionValue emission := by
  obtain ⟨before, computed⟩ := report.trace.steps finding member
  obtain ⟨outcome, stepped, stored⟩ := step_packet environment before finding.observation
    config zone packet observed state control event configured finding.result computed
  have same := (report.finding_matches compliant finding member).2
  simp only [seen, Option.map_some, Result.icmpValue, stored, bind, Option.bind] at same
  cases emitted : outcome.control.output with
  | none => simp [emitted] at same
  | some emission =>
    simp only [emitted, pure, Option.some.injEq] at same
    exact ⟨before, outcome, emission, stepped, emitted, same⟩

theorem Report.observed_quote (report : Report environment initial observations)
    (compliant : report.compliant = true) (finding : Finding) (member : finding ∈ report.findings)
    (config : MTUForwarding.Config) (zone : Nat) (packet : MTUForwarding.WirePacket)
    (observed : MTUForwarding.PacketObservation) (state : Option Import.ConntrackNetlink.Snapshot)
    (control : Config) (event : finding.observation.base.event = .packet config zone packet observed state)
    (configured : finding.observation.config = some control) (output : ICMPFrame)
    (seen : finding.observation.icmpOutput = some output) :
    ∃ (before : Tracker) (outcome : Netlib.Protocol.ICMPForwarding.Outcome packet.checked.packet)
      (emission : Netlib.Protocol.ICMPForwarding.Emission packet.checked.packet),
      Netlib.Protocol.ICMPForwarding.step (environment.pipeline control config) before
        (packetInput before config zone packet) finding.observation.identification = .ok outcome ∧
      outcome.control.output = some emission ∧
      Netlib.Protocol.ICMPForwarding.GenerationFacts (environment.pipeline control config).control
        (packetInput before config zone packet) outcome.transit finding.observation.identification emission ∧
      output.checked.quote.packet = (IPv4Quote.make packet.checked.packet emission.length).packet ∧
      output.checked.quote.declaredLength.val = packet.checked.packet.ip.packet.wireLength := by
  obtain ⟨before, outcome, emission, stepped, emitted, same⟩ :=
    report.observed_output compliant finding member config zone packet observed state control event configured output seen
  have quote := congrArg (fun value : ICMPError.Value => value.2.2.1) same
  have declared := congrArg (fun value : ICMPError.Value => value.2.2.2.val) same
  have restored := Netlib.Protocol.ICMPForwarding.step_quote_restored (environment.pipeline control config) before
    (packetInput before config zone packet) finding.observation.identification outcome stepped emission emitted
  refine ⟨before, outcome, emission, stepped, emitted,
    Netlib.Protocol.ICMPForwarding.step_output _ _ _ _ _ stepped _ emitted, quote.trans restored, ?_⟩
  exact declared.trans (IPv4Quote.make_declaredLength packet.checked.packet emission.valid emission.length)

structure Input where
  environment : Environment
  configs : List Config
  initial : Tracker
  initialValid : initial.Valid
  events : List Observation

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def project (json : Lean.Json) (keys : List String) : Except String Lean.Json :=
  Lean.Json.mkObj <$> keys.mapM fun key => do return (key, ← json.getObjVal? key)

private def profileFromJson (json : Lean.Json) : Except String Profile := do
  Import.PacketFields.fields json ["quoteLimit", "outerTtl", "outerDontFragment", "errorsUseInboundIfaddr",
    "rateLimit", "rateMask", "tosMask", "tosPrecedence", "broadcasts"]
  for (key, expected) in [("quoteLimit", 548), ("errorsUseInboundIfaddr", 0), ("rateLimit", 0),
      ("rateMask", 0), ("tosMask", 30), ("tosPrecedence", 192)] do
    require ((← (← json.getObjVal? key).getNat?) == expected) s!"Unsupported ICMP profile setting: {key}."
  require (!(← (← json.getObjVal? "outerDontFragment").getBool?)) "ICMP errors must permit fragmentation."
  let ttl ← (← json.getObjVal? "outerTtl").getNat?
  require (0 < ttl && ttl < 256) "The ICMP outer TTL must be between 1 and 255."
  let broadcasts ← (← (← json.getObjVal? "broadcasts").getArr?).toList.mapM fun value =>
    do Import.IPv4.parseAddress (← value.getStr?)
  require (broadcasts.eraseDups.length == broadcasts.length) "ICMP broadcast addresses must be unique."
  return ⟨UInt8.ofNat ttl, broadcasts⟩

private def configFromJson (json : Lean.Json) : Except String Config := do
  Import.PacketFields.fields json ["id", "forward", "late", "nat", "output", "icmpLate"]
  let output ← Import.NftablesStateful.Snapshot.fromJsonFor (← json.getObjVal? "output") ["output"]
  require (output.hook == "output" && output.priority == 0) "The ICMP output filter must use output priority zero."
  let late ← Import.NftablesStateful.Snapshot.fromJsonFor (← json.getObjVal? "icmpLate") ["postrouting"]
  require (late.hook == "postrouting" && 100 < late.priority && late.priority < 2147483647)
    "The ICMP late filter must use postrouting after source NAT and before confirmation."
  return ⟨← (← json.getObjVal? "id").getStr?, output, late⟩

private def icmpOutput (json : Lean.Json) : Except String (Option ICMPFrame) := do
  let values ← json.getArr?
  require (values.size ≤ 1) "An event must contain zero or one ICMP error output."
  if values.isEmpty then return none
  let bytes ← Import.EAPOL.bytesFromHex (← values[0]!.getStr?)
  return some ⟨bytes, ← ICMPError.checkBytes bytes⟩

private def projectEvent (json : Lean.Json) : Except String (Lean.Json × Option ICMPFrame) := do
  let kind ← (← json.getObjVal? "type").getStr?
  if kind == "packet" then
    Import.PacketFields.fields json ["type", "config", "zone", "raw", "observed", "state"]
    let observed ← json.getObjVal? "observed"
    Import.PacketFields.fields observed ["classification", "fresh", "afterDestination", "afterSource",
      "nextHop", "disposition", "mtu", "output", "icmpOutput"]
    let frame ← icmpOutput (← observed.getObjVal? "icmpOutput")
    let projected ← project observed ["classification", "fresh", "afterDestination", "afterSource",
      "nextHop", "disposition", "mtu", "output"]
    return (json.setObjVal! "observed" projected, frame)
  else
    Import.PacketFields.fields json ["type", "zone", "raw", "state"]
    return (json, none)

def Input.fromJson (json : Lean.Json) : Except String Input := do
  Import.PacketFields.fields json ["schema", "routing", "mtus", "configs", "initial", "events", "icmpProfile"]
  let profile ← profileFromJson (← json.getObjVal? "icmpProfile")
  let configValues ← (← json.getObjVal? "configs").getArr?
  let configs ← configValues.toList.mapM configFromJson
  let transitConfigs ← configValues.toList.mapM fun config => project config ["id", "forward", "late", "nat"]
  let eventValues ← (← json.getObjVal? "events").getArr?
  let events ← eventValues.toList.mapM projectEvent
  let projected ← project json ["schema", "routing", "mtus", "configs", "initial", "events"]
  let transit ← MTUForwarding.Input.fromJson ((projected.setObjVal! "configs" (Lean.toJson transitConfigs)).setObjVal!
    "events" (Lean.toJson (events.map Prod.fst)))
  require (transit.environment.routing.routes.all fun route => route.nextNode.isNone || route.preferredSource.isSome)
    "Every unicast route needs an explicit preferred source for ICMP return routing."
  let observations ← (transit.events.zip events).mapM fun (base, _, frame) => do
    let control ← match base.event with
      | .erase .. => pure none
      | .packet config .. => do
        let some control := configs.find? (·.id == config.id) | throw "Missing ICMP control configuration."
        pure (some control)
    return { base, config := control, icmpOutput := frame : Observation }
  return ⟨⟨transit.environment, profile⟩, configs, transit.initial, transit.initialValid, observations⟩

def Input.parse (text : String) : Except String Input := do Input.fromJson (← Import.Json.parse text)

def Input.check (input : Input) : Except String (Report input.environment input.initial input.events) :=
  audit input.environment input.initial input.events

private def classificationText : StatefulACL.CTState → String
  | .new => "new" | .established => "established" | .related => "related"
  | .invalid => "invalid" | .untracked => "untracked"

private def transitDispositionText : Netlib.Protocol.MTUForwarding.Disposition → String
  | .forwarded => "forwarded" | .routeDrop => "routeDrop" | .ttlExpired => "ttlExpired"
  | .mtuExceeded => "mtuExceeded" | .forwardDrop => "forwardDrop" | .lateDrop => "lateDrop"

private def controlDispositionText : Netlib.Protocol.ICMPForwarding.Disposition → String
  | .notNeeded => "notNeeded" | .suppressed => "suppressed" | .noReturnRoute => "noReturnRoute"
  | .outputDrop => "outputDrop" | .lateDrop => "lateDrop" | .sent => "sent"

private def kindJson (kind : ICMP.Kind) : Lean.Json := Lean.Json.mkObj [
  ("type", Lean.toJson (match kind with | .timeExceeded => 11 | .fragmentationNeeded _ => 3 : Nat)),
  ("code", Lean.toJson (match kind with | .timeExceeded => 0 | .fragmentationNeeded _ => 4 : Nat)),
  ("mtu", Lean.toJson (match kind with | .timeExceeded => none | .fragmentationNeeded mtu => some mtu.val))]

private def fragmentJson (fragment : IPv4Fragment.Decoded) : Lean.Json := Lean.Json.mkObj [
  ("wireLength", Lean.toJson fragment.packet.wireLength),
  ("offsetBytes", Lean.toJson (fragment.packet.offset.val * 8)),
  ("moreFragments", Lean.toJson fragment.packet.moreFragments),
  ("dontFragment", Lean.toJson fragment.packet.dontFragment),
  ("tos", Lean.toJson fragment.packet.tos.toNat),
  ("identification", Lean.toJson fragment.packet.identification.val),
  ("ttl", Lean.toJson fragment.packet.ttl.toNat),
  ("ipv4Checksum", Lean.toJson fragment.checksum.val),
  ("payloadHex", Lean.toJson (Import.EAPOL.bytesToHex fragment.packet.payload))]

private def familyJson (fragments : List IPv4Fragment.Decoded) (packet : IPv4.Packet)
    (datagram : UDP.Datagram) : Lean.Json := Lean.Json.mkObj [
  ("fragments", Lean.toJson (fragments.map fragmentJson)),
  ("header", Import.PacketFields.headerJson
    ⟨packet.source, packet.destination, packet.protocol, datagram.sourcePort, datagram.destinationPort⟩),
  ("ttl", Lean.toJson packet.ttl.toNat),
  ("payloadHex", Lean.toJson (Import.EAPOL.bytesToHex datagram.payload)),
  ("udpChecksum", Lean.toJson datagram.checksum.val)]

private def emissionJson (emission : Netlib.Protocol.ICMPForwarding.Emission source) : Lean.Json := Lean.Json.mkObj [
  ("kind", kindJson emission.kind),
  ("header", Import.PacketFields.headerJson emission.afterSource),
  ("nextHop", Lean.toJson emission.path.nextHop),
  ("returnMTU", Lean.toJson emission.path.mtu.val),
  ("ttl", Lean.toJson emission.packet.ttl.toNat),
  ("tos", Lean.toJson emission.packet.tos.toNat),
  ("identification", Lean.toJson emission.identification.val),
  ("dontFragment", Lean.toJson emission.packet.dontFragment),
  ("quoteHeader", Import.PacketFields.headerJson (IPv4Quote.header emission.quote)),
  ("quoteLength", Lean.toJson (IPv4Quote.bytes emission.quote).length),
  ("declaredLength", Lean.toJson emission.quote.declaredLength.val),
  ("quoteTos", Lean.toJson emission.quote.packet.tos.toNat),
  ("quoteTTL", Lean.toJson emission.quote.packet.ttl.toNat),
  ("quoteIdentification", Lean.toJson emission.quote.packet.identification.val),
  ("quoteDontFragment", Lean.toJson emission.quote.packet.dontFragment),
  ("quotePayloadHex", Lean.toJson (Import.EAPOL.bytesToHex emission.quote.packet.payload)),
  ("rawIPv4", Lean.toJson (Import.EAPOL.bytesToHex emission.bytes))]

private def controlJson (control : Netlib.Protocol.ICMPForwarding.Control source) : Lean.Json := Lean.Json.mkObj [
  ("reason", (control.reason.map kindJson).getD .null),
  ("disposition", Lean.toJson (controlDispositionText control.disposition)),
  ("classification", Lean.toJson (if control.beforeSource.isSome then some "related" else none)),
  ("beforeSource", Import.PacketFields.optionalHeaderJson control.beforeSource),
  ("afterSource", Import.PacketFields.optionalHeaderJson control.afterSource),
  ("output", (control.output.map emissionJson).getD .null)]

private def outcomeJson (packet : PacketResult) : Lean.Json :=
  let outcome := packet.outcome.transit
  Lean.Json.mkObj [
    ("classification", Lean.toJson (classificationText outcome.attachment.classification)),
    ("fresh", Lean.toJson outcome.attachment.fresh),
    ("afterDestination", Import.PacketFields.headerJson outcome.afterDestination),
    ("afterSource", Import.PacketFields.optionalHeaderJson outcome.afterSource),
    ("nextHop", Lean.toJson outcome.nextHop),
    ("disposition", Lean.toJson (transitDispositionText outcome.disposition)),
    ("mtu", Lean.toJson (outcome.selectedMTU.map (·.val))),
    ("output", (outcome.output.map fun emission =>
      (familyJson emission.fragments.fragments emission.transit.decoded.ip.packet emission.transit.decoded.datagram).setObjVal!
        "rawIPv4" (Lean.toJson (emission.bytes.map Import.EAPOL.bytesToHex))).getD .null),
    ("icmp", controlJson packet.outcome.control)]

private def observationJson (observation : Observation) : Lean.Json :=
  match observation.base.event with
  | .erase .. => .null
  | .packet _ _ packet observed _ => Lean.Json.mkObj [
    ("inputHeader", Import.PacketFields.headerJson packet.checked.header),
    ("inputTTL", Lean.toJson packet.checked.packet.ip.packet.ttl.toNat),
    ("classification", Lean.toJson (observed.classification.map classificationText)),
    ("fresh", Lean.toJson observed.fresh),
    ("afterDestination", Import.PacketFields.optionalHeaderJson observed.afterDestination),
    ("afterSource", Import.PacketFields.optionalHeaderJson observed.afterSource),
    ("nextHop", Lean.toJson observed.nextHop), ("mtu", Lean.toJson observed.mtu),
    ("disposition", Lean.toJson (observed.disposition.map transitDispositionText)),
    ("output", (observed.output.map fun family =>
      familyJson (family.fragments.map (·.checked.fragment)) family.packet family.datagram).getD .null),
    ("icmpOutput", Lean.toJson (observation.icmpOutput.toList.map (·.checked.renderJson)))]

def Report.assumptions : List String := [
  "Raw bytes identify complete selected UDP transit and ICMP error outputs at the declared capture stages.",
  "Routes, effective MTUs, broadcast addresses, and NAT/filter snapshots form the stable exclusive environment.",
  "ICMP profile 1 disables rate limiting, selects route preferred source addresses, and assumes successful allocation and output.",
  "The outer ICMP identification is a nondeterministic allocator choice supplied by the observed error; its allocator is not proved.",
  "Error existence, kind, quote, addresses, TOS, TTL, DF, output filtering, and related NAT are computed independently of that choice.",
  "The ordinary tracker models UDP attachment; ICMP generation neither confirms a rejected fresh flow nor adds a separate ordinary record.",
  "Inputs are whole IHL-five IPv4 UDP; fragments, options, policy routing, helpers, rerouting, and device failures are excluded.",
  "Null intermediate observations are unchecked; empty output arrays assert no selected transit or ICMP egress.",
  "ICMP comparison checks outer fields, kind, and quoted fields; checked checksum zero representation and Ethernet padding are ignored.",
  "Complete quoted UDP datagrams are validated; partial quotations preserve checksum bytes without claiming complete UDP checksum validity.",
  "Native table comparison ignores IDs, order, and timeout seconds, retaining supported tuples, zones, NAT, and seen-reply fields.",
  "The certificates concern the Lean model and supplied observations; native implementation refinement and capture completeness remain assumptions."]

def Report.renderJson (report : Report environment initial observations) : Lean.Json := Lean.Json.mkObj [
  ("compliant", Lean.toJson report.compliant), ("scope", Lean.toJson "icmp-aware-ipv4-udp-tracked-forwarding"),
  ("assumptions", Lean.toJson Report.assumptions), ("eventCount", Lean.toJson observations.length),
  ("final", Check.ConntrackLifecycle.stateJson report.final),
  ("findings", Lean.toJson (report.findings.map fun finding => Lean.Json.mkObj [
    ("source", Lean.toJson s!"/events/{finding.observation.base.index}"), ("matched", Lean.toJson finding.passed),
    ("expected", (finding.result.packet.map outcomeJson).getD .null),
    ("observed", observationJson finding.observation),
    ("stateObserved", Lean.toJson finding.observation.base.event.stateObservation.isSome),
    ("stateMatched", Lean.toJson (MTUForwarding.stateMatches finding.observation.base.event finding.result.state)),
    ("expectedState", Check.ConntrackLifecycle.stateJson finding.result.state)]))]

def Report.render (report : Report environment initial observations) : String :=
  (if report.compliant then "ICMP FORWARDING OBSERVATIONS MATCH\n" else "ICMP FORWARDING OBSERVATIONS MISMATCH\n") ++
    report.renderJson.pretty

end Netlib.Check.ICMPForwarding
