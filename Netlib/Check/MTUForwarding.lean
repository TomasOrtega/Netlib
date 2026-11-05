import Netlib.Check.ConntrackLifecycle
import Netlib.Check.Wire
import Netlib.Check.Replay
import Netlib.Protocol.MTUForwarding
import Netlib.Check.IPv4Fragments

/-!
# MTU-aware byte-derived forwarding replay

Input and output packet fields come from checked Ethernet bytes.
Null intermediate fields are unobserved. An empty output array asserts no selected UDP egress.
Native snapshots retain the existing ordinary-table comparison scope.
-/

namespace Netlib.Check.MTUForwarding

open Packet Protocol
abbrev Tracker := Netlib.Protocol.ConntrackLifecycle.State
abbrev Config := Check.ConntrackLifecycle.Config
abbrev MTU := IPv4Fragmentation.MTU

structure MTUBinding where
  nextHop : String
  mtu : MTU

structure Environment where
  routing : Import.LinuxRoute.Snapshot
  mtus : List MTUBinding

def Environment.mtu (environment : Environment) (hop : String) : MTU :=
  ((environment.mtus.find? (·.nextHop == hop)).map (·.mtu)).getD ⟨68, by decide⟩

def Environment.pipeline (environment : Environment) (config : Config) : Netlib.Protocol.MTUForwarding.Pipeline :=
  ⟨config.pipeline environment.routing, environment.mtu⟩

structure WirePacket where
  bytes : List UInt8
  checked : Check.Wire.Checked bytes

def WirePacket.value (packet : WirePacket) : IPv4.Packet × UDP.Datagram :=
  (packet.checked.packet.ip.packet, packet.checked.packet.datagram)

def emissionValue (emission : Netlib.Protocol.MTUForwarding.Emission packet) : IPv4Fragments.Value :=
  (IPv4Fragments.normalize emission.fragments.packets, emission.transit.decoded.ip.packet, emission.transit.decoded.datagram)

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
  disposition : Option Netlib.Protocol.MTUForwarding.Disposition
  mtu : Option Nat
  output : Option IPv4Fragments.Family

def PacketObservation.Matches (observed : PacketObservation) (outcome : Netlib.Protocol.MTUForwarding.Outcome packet) : Prop :=
  Agrees observed.classification outcome.attachment.classification ∧
    Agrees observed.fresh outcome.attachment.fresh ∧ Agrees observed.afterDestination outcome.afterDestination ∧
    Agrees (observed.afterSource.map some) outcome.afterSource ∧ Agrees (observed.nextHop.map some) outcome.nextHop ∧
    Agrees observed.disposition outcome.disposition ∧
    Agrees (observed.mtu.map some) (outcome.selectedMTU.map (·.val)) ∧
    observed.output.map IPv4Fragments.Family.value = outcome.output.map emissionValue

def PacketObservation.matches (observed : PacketObservation) (outcome : Netlib.Protocol.MTUForwarding.Outcome packet) : Bool :=
  agrees observed.classification outcome.attachment.classification &&
    agrees observed.fresh outcome.attachment.fresh && agrees observed.afterDestination outcome.afterDestination &&
    agrees (observed.afterSource.map some) outcome.afterSource && agrees (observed.nextHop.map some) outcome.nextHop &&
    agrees observed.disposition outcome.disposition &&
    agrees (observed.mtu.map some) (outcome.selectedMTU.map (·.val)) &&
    decide (observed.output.map IPv4Fragments.Family.value = outcome.output.map emissionValue)

theorem PacketObservation.matches_correct (observed : PacketObservation) (outcome : Netlib.Protocol.MTUForwarding.Outcome packet) :
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

def packetInput (before : Tracker) (config : Config) (zone : Nat) (packet : WirePacket) : Netlib.Protocol.MTUForwarding.Input :=
  ⟨zone, packet.checked.packet,
    if (before.model.lookup zone packet.checked.header).isNone then
      some (config.nat.candidate zone packet.checked.header) else none⟩

structure PacketResult where
  input : Netlib.Protocol.MTUForwarding.Input
  outcome : Netlib.Protocol.MTUForwarding.Outcome input.packet

structure Result where
  state : Tracker
  valid : state.Valid
  packet : Option PacketResult

def step (environment : Environment) (before : Tracker) : Event → Except String Result
  | .packet config zone packet _ _ => do
    let input := packetInput before config zone packet
    let outcome ← (Netlib.Protocol.MTUForwarding.step (environment.pipeline config) before input).mapError (·.describe)
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

def replay (environment : Environment) : Replay.System Tracker Observation Result where
  step before observation := step environment before observation.event
  state := Result.state
  passed observation result := packetMatches observation.event result && stateMatches observation.event result.state
  Matches := Matches
  correct := finding_correct

abbrev Agreement (environment : Environment) := Replay.Agreement (replay environment)
structure Trace (environment : Environment) (initial : Tracker) (findings : List Finding)
    (final : Tracker) : Prop where
  execution : Replay.Trace (replay environment) initial findings final

structure Report (environment : Environment) (initial : Tracker) (observations : List Observation) where
  final : Tracker
  findings : List Finding
  covered : findings.map Finding.observation = observations
  trace : Trace environment initial findings final
  correct : findings.all Finding.passed = true ↔ Agreement environment initial observations

theorem Trace.valid (trace : Trace environment initial findings final) (valid : initial.Valid) :
    final.Valid ∧ ∀ finding ∈ findings, finding.result.state.Valid :=
  Replay.Trace.invariant trace.execution Netlib.Protocol.ConntrackLifecycle.State.Valid
    (fun _ _ result _ _ => result.valid) valid

def audit (environment : Environment) (initial : Tracker) (observations : List Observation) :
    Except String (Report environment initial observations) := do
  let report ← Replay.audit (replay environment) initial observations
  return ⟨report.final, report.findings, report.covered, ⟨report.trace⟩, report.correct⟩

def Report.compliant (report : Report environment initial observations) : Bool := report.findings.all Finding.passed

theorem Report.compliant_iff (report : Report environment initial observations) :
    report.compliant = true ↔ Agreement environment initial observations := report.correct

theorem Trace.steps (trace : Trace environment initial findings final) :
    ∀ finding ∈ findings, ∃ before, step environment before finding.observation.event = .ok finding.result :=
  Replay.Trace.steps trace.execution

theorem Trace.matches (trace : Trace environment initial findings final)
    (agreement : Agreement environment initial (findings.map Finding.observation)) :
    ∀ finding ∈ findings, Matches finding.observation finding.result :=
  Replay.Trace.matches trace.execution agreement

theorem Report.finding_matches (report : Report environment initial observations) (compliant : report.compliant = true)
    (finding : Finding) (member : finding ∈ report.findings) : Matches finding.observation finding.result := by
  have agreement := report.compliant_iff.mp compliant
  rw [← report.covered] at agreement
  exact Trace.matches report.trace agreement finding member

theorem step_packet (environment : Environment) (before : Tracker) (config : Config)
    (zone : Nat) (packet : WirePacket) (observed : PacketObservation)
    (state : Option Import.ConntrackNetlink.Snapshot) (result : Result)
    (accepted : step environment before (.packet config zone packet observed state) = .ok result) :
    ∃ outcome, Netlib.Protocol.MTUForwarding.step (environment.pipeline config) before
        (packetInput before config zone packet) = .ok outcome ∧
      result.packet = some ⟨packetInput before config zone packet, outcome⟩ := by
  cases computed : Netlib.Protocol.MTUForwarding.step (environment.pipeline config) before
      (packetInput before config zone packet) with
  | error error => simp [step, computed, Except.mapError, bind, Except.bind] at accepted
  | ok outcome =>
    simp [step, computed, Except.mapError, bind, Except.bind, pure] at accepted
    cases accepted
    exact ⟨outcome, rfl, rfl⟩

theorem Report.observed_output (report : Report environment initial observations)
    (compliant : report.compliant = true) (finding : Finding) (member : finding ∈ report.findings)
    (config : Config) (zone : Nat) (packet : WirePacket) (observed : PacketObservation)
    (state : Option Import.ConntrackNetlink.Snapshot)
    (event : finding.observation.event = .packet config zone packet observed state)
    (output : IPv4Fragments.Family) (seen : observed.output = some output) :
    ∃ (before : Tracker) (outcome : Netlib.Protocol.MTUForwarding.Outcome packet.checked.packet)
      (emission : Netlib.Protocol.MTUForwarding.Emission packet.checked.packet),
      Netlib.Protocol.MTUForwarding.step (environment.pipeline config) before
        (packetInput before config zone packet) = .ok outcome ∧
      outcome.output = some emission ∧ output.value = emissionValue emission := by
  obtain ⟨before, computed⟩ := Trace.steps report.trace finding member
  rw [event] at computed
  obtain ⟨outcome, stepped, stored⟩ := step_packet environment before config zone packet observed state finding.result computed
  have matched := (report.finding_matches compliant finding member).1
  rw [event] at matched
  simp only [PacketMatches, stored] at matched
  have same := matched.2.2.2.2.2.2.2
  rw [seen] at same
  cases emitted : outcome.output with
  | none => simp [emitted] at same
  | some emission =>
    simp only [emitted, Option.map_some, Option.some.injEq] at same
    exact ⟨before, outcome, emission, stepped, emitted, same⟩

theorem Report.observed_output_payload (report : Report environment initial observations)
    (compliant : report.compliant = true) (finding : Finding) (member : finding ∈ report.findings)
    (config : Config) (zone : Nat) (packet : WirePacket) (observed : PacketObservation)
    (state : Option Import.ConntrackNetlink.Snapshot)
    (event : finding.observation.event = .packet config zone packet observed state)
    (output : IPv4Fragments.Family) (seen : observed.output = some output) :
    output.datagram.payload = packet.checked.packet.datagram.payload ∧
      output.packet.ttl.toNat = packet.checked.packet.ip.packet.ttl.toNat - 1 := by
  obtain ⟨before, outcome, emission, stepped, emitted, same⟩ :=
    report.observed_output compliant finding member config zone packet observed state event output seen
  have payload := congrArg (fun value : IPv4Fragments.Value => value.2.2.payload) same
  have ttl := congrArg (fun value : IPv4Fragments.Value => value.2.1.ttl.toNat) same
  exact ⟨payload.trans emission.transit.rewritten.payload,
    ttl.trans ((congrArg UInt8.toNat emission.transit.rewritten.ttl).trans
      (Netlib.Protocol.WireForwarding.decrementTTL_exact packet.checked.packet))⟩

theorem Report.observed_fragments_fit (report : Report environment initial observations)
    (compliant : report.compliant = true) (finding : Finding) (member : finding ∈ report.findings)
    (config : Config) (zone : Nat) (packet : WirePacket) (observed : PacketObservation)
    (state : Option Import.ConntrackNetlink.Snapshot)
    (event : finding.observation.event = .packet config zone packet observed state)
    (output : IPv4Fragments.Family) (seen : observed.output = some output) :
    ∃ (before : Tracker) (outcome : Netlib.Protocol.MTUForwarding.Outcome packet.checked.packet)
      (emission : Netlib.Protocol.MTUForwarding.Emission packet.checked.packet),
      Netlib.Protocol.MTUForwarding.step (environment.pipeline config) before
        (packetInput before config zone packet) = .ok outcome ∧ outcome.output = some emission ∧
      ∀ fragment ∈ output.fragments, fragment.checked.fragment.packet.wireLength ≤ emission.mtu.val := by
  obtain ⟨before, outcome, emission, stepped, emitted, same⟩ :=
    report.observed_output compliant finding member config zone packet observed state event output seen
  refine ⟨before, outcome, emission, stepped, emitted, ?_⟩
  intro fragment belongs
  have fields := congrArg Prod.fst same
  have normalized : fragment.checked.fragment.packet ∈
      IPv4Fragments.normalize (output.fragments.map (·.checked.fragment.packet)) := by
    simp only [IPv4Fragments.normalize, List.mem_mergeSort]
    exact List.mem_map.mpr ⟨fragment, belongs, rfl⟩
  change IPv4Fragments.normalize (output.fragments.map (·.checked.fragment.packet)) =
    IPv4Fragments.normalize emission.fragments.packets at fields
  rw [fields] at normalized
  simp only [IPv4Fragments.normalize, List.mem_mergeSort, IPv4Fragmentation.Certified.packets] at normalized
  obtain ⟨part, partMember, equal⟩ := List.mem_map.mp normalized
  rw [← equal]
  exact emission.fits part partMember

theorem Report.observed_route_mtu (report : Report environment initial observations)
    (compliant : report.compliant = true) (finding : Finding) (member : finding ∈ report.findings)
    (config : Config) (zone : Nat) (packet : WirePacket) (observed : PacketObservation)
    (state : Option Import.ConntrackNetlink.Snapshot)
    (event : finding.observation.event = .packet config zone packet observed state)
    (output : IPv4Fragments.Family) (seen : observed.output = some output) :
    ∃ (before : Tracker) (outcome : Netlib.Protocol.MTUForwarding.Outcome packet.checked.packet) (hop : String),
      Netlib.Protocol.MTUForwarding.step (environment.pipeline config) before
        (packetInput before config zone packet) = .ok outcome ∧ outcome.nextHop = some hop ∧
      ∀ fragment ∈ output.fragments, fragment.checked.fragment.packet.wireLength ≤ (environment.mtu hop).val := by
  obtain ⟨before, outcome, emission, stepped, emitted, fits⟩ :=
    report.observed_fragments_fit compliant finding member config zone packet observed state event output seen
  obtain ⟨hop, routed, selected⟩ := Netlib.Protocol.MTUForwarding.step_output_routeMTU
    (environment.pipeline config) before (packetInput before config zone packet) outcome stepped emission emitted
  refine ⟨before, outcome, hop, stepped, routed, ?_⟩
  intro fragment belongs
  change fragment.checked.fragment.packet.wireLength ≤ ((environment.pipeline config).mtu hop).val
  rw [← selected]
  exact fits fragment belongs

structure Input where
  environment : Environment
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

private def disposition (json : Lean.Json) : Except String Netlib.Protocol.MTUForwarding.Disposition := do
  match ← json.getStr? with
  | "forwarded" => return .forwarded
  | "routeDrop" => return .routeDrop
  | "ttlExpired" => return .ttlExpired
  | "mtuExceeded" => return .mtuExceeded
  | "forwardDrop" => return .forwardDrop
  | "lateDrop" => return .lateDrop
  | value => throw s!"Unsupported wire forwarding disposition: {value}."

private def outputFamily (json : Lean.Json) : Except String (Option IPv4Fragments.Family) := do
  let values ← json.getArr?
  if values.isEmpty then return none
  let bytes ← values.toList.mapM fun value => do Import.EAPOL.bytesFromHex (← value.getStr?)
  some <$> IPv4Fragments.checkFamily bytes

private def packetObservation (json : Lean.Json) : Except String PacketObservation := do
  Import.PacketFields.fields json ["classification", "fresh", "afterDestination", "afterSource", "nextHop", "disposition", "mtu", "output"]
  return ⟨← optional classification (← json.getObjVal? "classification"),
    ← optional Lean.Json.getBool? (← json.getObjVal? "fresh"),
    ← optional Import.PacketFields.header (← json.getObjVal? "afterDestination"),
    ← optional Import.PacketFields.header (← json.getObjVal? "afterSource"),
    ← optional Lean.Json.getStr? (← json.getObjVal? "nextHop"),
    ← optional disposition (← json.getObjVal? "disposition"),
    ← optional Lean.Json.getNat? (← json.getObjVal? "mtu"),
    ← outputFamily (← json.getObjVal? "output")⟩

private def stateObservation (json : Lean.Json) : Except String (Option Import.ConntrackNetlink.Snapshot) :=
  optional Import.ConntrackNetlink.Snapshot.fromJson json

def Input.fromJson (json : Lean.Json) : Except String Input := do
  Import.PacketFields.fields json ["schema", "routing", "mtus", "configs", "initial", "events"]
  require ((← (← json.getObjVal? "schema").getNat?) == 1) "Use wire forwarding schema 1."
  let routing ← Check.ConntrackLifecycle.routingFromJson (← json.getObjVal? "routing")
  let values ← (← json.getObjVal? "mtus").getArr?
  let mut mtus : List MTUBinding := []
  for value in values do
    Import.PacketFields.fields value ["nextHop", "mtu"]
    let hop ← (← value.getObjVal? "nextHop").getStr?
    let number ← (← value.getObjVal? "mtu").getNat?
    if bounded : 68 ≤ number ∧ number < 65536 then
      require (!(mtus.any (·.nextHop == hop))) "Effective MTU next hops must be unique."
      require (routing.bindings.any (·.nextNode == hop)) "An effective MTU must name a bound route next hop."
      mtus := mtus ++ [⟨hop, ⟨number, bounded⟩⟩]
    else throw "An effective IPv4 MTU must be between 68 and 65535 bytes."
  require (routing.bindings.all fun binding => mtus.any (·.nextHop == binding.nextNode))
    "Supply an effective MTU for every route binding."
  let environment : Environment := ⟨routing, mtus⟩
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
    return ⟨environment, configs, initial, (Netlib.Protocol.ConntrackLifecycle.State.check_correct _).mp valid, observations⟩
  else throw "The initial ordinary conntrack table is invalid."

def Input.parse (text : String) : Except String Input := do
  Input.fromJson (← Import.Json.parse text)

def Input.check (input : Input) : Except String (Report input.environment input.initial input.events) :=
  audit input.environment input.initial input.events

private def dispositionText : Netlib.Protocol.MTUForwarding.Disposition → String
  | .forwarded => "forwarded" | .routeDrop => "routeDrop" | .ttlExpired => "ttlExpired"
  | .mtuExceeded => "mtuExceeded" | .forwardDrop => "forwardDrop" | .lateDrop => "lateDrop"

private def classificationText : StatefulACL.CTState → String
  | .new => "new" | .established => "established" | .related => "related"
  | .invalid => "invalid" | .untracked => "untracked"

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

private def outcomeJson (outcome : Netlib.Protocol.MTUForwarding.Outcome packet) : Lean.Json := Lean.Json.mkObj [
  ("classification", Lean.toJson (classificationText outcome.attachment.classification)),
  ("fresh", Lean.toJson outcome.attachment.fresh),
  ("afterDestination", Import.PacketFields.headerJson outcome.afterDestination),
  ("afterSource", Import.PacketFields.optionalHeaderJson outcome.afterSource),
  ("nextHop", Lean.toJson outcome.nextHop), ("disposition", Lean.toJson (dispositionText outcome.disposition)),
  ("mtu", Lean.toJson (outcome.selectedMTU.map (·.val))),
  ("output", (outcome.output.map fun emission =>
    let family := familyJson emission.fragments.fragments emission.transit.decoded.ip.packet emission.transit.decoded.datagram
    family.setObjVal! "rawIPv4" (Lean.toJson (emission.bytes.map Import.EAPOL.bytesToHex))).getD .null)]

private def observationJson : Event → Lean.Json
  | .erase .. => .null
  | .packet _ _ packet observed _ => Lean.Json.mkObj [
    ("inputHeader", Import.PacketFields.headerJson packet.checked.header),
    ("inputTTL", Lean.toJson packet.checked.packet.ip.packet.ttl.toNat),
    ("classification", Lean.toJson (observed.classification.map classificationText)),
    ("fresh", Lean.toJson observed.fresh),
    ("afterDestination", Import.PacketFields.optionalHeaderJson observed.afterDestination),
    ("afterSource", Import.PacketFields.optionalHeaderJson observed.afterSource),
    ("nextHop", Lean.toJson observed.nextHop), ("mtu", Lean.toJson observed.mtu),
    ("disposition", Lean.toJson (observed.disposition.map dispositionText)),
    ("output", (observed.output.map fun family =>
      familyJson (family.fragments.map (·.checked.fragment)) family.packet family.datagram).getD .null)]

def Report.assumptions : List String := [
  "Raw bytes identify the selected whole input and its complete output fragment family at the declared capture stages.",
  "Routes and NAT/filter snapshots form the exclusive stable hook sequence for each selected packet.",
  "Each route next hop has the supplied effective IPv4 MTU, including any route or path constraints.",
  "The ordinary tracker accepts modeled UDP attachment; concurrency, expiry, helpers, and clash recovery are excluded.",
  "Inputs are unfragmented IHL-five IPv4 UDP; output has no additional encapsulation or transformations.",
  "TTL and DF rejection produce no selected UDP transit output; ICMP generation and its effects remain outside the model.",
  "Fragmentation assumes successful allocation and output; offload, GSO, ignore-DF, rerouting, and device failure are excluded.",
  "Strict reassembly rejects overlaps, gaps, duplicates, and mixed metadata; it does not model native timers or overlap policy.",
  "Null intermediate observations are unchecked; an empty output array asserts no selected UDP egress within the complete observation scope.",
  "Output comparison checks normalized fragment fields and the recovered UDP datagram; adjacency, padding, and checksum zero representation are separate.",
  "Table comparison retains supported NAT and seen-reply fields and ignores native IDs, order, and timeout seconds.",
  "These proofs concern the Lean model and supplied observations; kernel refinement and policy-installation timing remain separate."]

def Report.renderJson (report : Report environment initial observations) : Lean.Json := Lean.Json.mkObj [
  ("compliant", Lean.toJson report.compliant), ("scope", Lean.toJson "mtu-aware-ipv4-udp-tracked-forwarding"),
  ("assumptions", Lean.toJson Report.assumptions), ("eventCount", Lean.toJson observations.length),
  ("final", Check.ConntrackLifecycle.stateJson report.final),
  ("findings", Lean.toJson (report.findings.map fun finding => Lean.Json.mkObj [
    ("source", Lean.toJson s!"/events/{finding.observation.index}"), ("matched", Lean.toJson finding.passed),
    ("expected", (finding.result.packet.map fun packet => outcomeJson packet.outcome).getD .null),
    ("observed", observationJson finding.observation.event),
    ("stateObserved", Lean.toJson finding.observation.event.stateObservation.isSome),
    ("stateMatched", Lean.toJson (stateMatches finding.observation.event finding.result.state)),
    ("expectedState", Check.ConntrackLifecycle.stateJson finding.result.state)]))]

def Report.render (report : Report environment initial observations) : String :=
  (if report.compliant then "MTU FORWARDING OBSERVATIONS MATCH\n" else "MTU FORWARDING OBSERVATIONS MISMATCH\n") ++
    report.renderJson.pretty

end Netlib.Check.MTUForwarding
