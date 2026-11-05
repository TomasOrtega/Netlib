import Netlib.Check.Replay
import Netlib.Check.WireForwarding
import Netlib.Protocol.StatefulFailover

/-!
# Observed replication and gateway handoff

Both ordinary tables start empty and evolve from packet processing and explicit replica commitment.
Cache observations compare daemon attributes without pretending they are kernel Netlink records.
Endpoint route changes and the primary fence remain explicit ordered inputs.
-/

namespace Netlib.Check.StatefulFailover

open Packet Protocol
open Netlib.Protocol.StatefulFailover (Gateway Leg Replica)
abbrev ModelState := Netlib.Protocol.StatefulFailover.State
abbrev ModelResult := Netlib.Protocol.StatefulFailover.Result
abbrev Config := Check.ConntrackLifecycle.Config

structure Routing where
  primary : Import.LinuxRoute.Snapshot
  standby : Import.LinuxRoute.Snapshot

def Routing.table (routing : Routing) : Gateway → Import.LinuxRoute.Snapshot
  | .primary => routing.primary
  | .standby => routing.standby

structure InputPacket where
  bytes : List UInt8
  packet : UDP.DecodedIPv4
  decoded : UDP.decodeIPv4 bytes = .ok packet

structure CacheEntry where
  original : Header
  zone : Nat
  sourceNAT : Option Endpoint
  destinationNAT : Option Endpoint
  seenReply : Bool
  deriving Repr, BEq, DecidableEq

def CacheEntry.ofReplica (replica : Replica) : CacheEntry :=
  let record := replica.record
  ⟨record.entry.flow.original, record.entry.flow.originalZone,
    if record.entry.sourceNAT then some record.entry.flow.reply.destinationEndpoint else none,
    if record.entry.destinationNAT then some record.entry.flow.reply.sourceEndpoint else none,
    record.seenReply⟩

def cacheEntries (state : ModelState) : List CacheEntry := state.cache.toList.map CacheEntry.ofReplica

inductive Event where
  | packet (gateway : Gateway) (leg : Leg) (config : Config) (zone : Nat) (packet : InputPacket)
      (observed : Check.WireForwarding.PacketObservation)
  | stage (zone : Nat) (packet : Header)
  | commit (timeout : Nat)
  | handoff (leg : Leg) (gateway : Gateway)
  | fence (gateway : Gateway)
  | erase (gateway : Gateway) (zone : Nat) (packet : Header)
  | forget

def Event.toModel (routing : Routing) (before : ModelState) : Event → Netlib.Protocol.StatefulFailover.Event
  | .packet gateway leg config zone wire _ =>
    let state := before.table gateway
    let input : Protocol.WireForwarding.Input := ⟨zone, wire.packet,
      if (state.model.lookup zone wire.packet.header).isNone then
        some (config.nat.candidate zone wire.packet.header) else none⟩
    .packet ⟨gateway, leg, config.pipeline (routing.table gateway), input⟩
  | .stage zone key => .stage zone key
  | .commit timeout => .commit timeout
  | .handoff leg gateway => .handoff leg gateway
  | .fence gateway => .fence gateway
  | .erase gateway zone key => .erase gateway zone key
  | .forget => .forget

structure Observation where
  index : Nat
  event : Event
  primary : Option Import.ConntrackNetlink.Snapshot
  standby : Option Import.ConntrackNetlink.Snapshot
  cache : Option (List CacheEntry)
  raw : Lean.Json

def step (routing : Routing) (before : ModelState) (observation : Observation) : Except String ModelResult :=
  Netlib.Protocol.StatefulFailover.step before (observation.event.toModel routing before)

private def tableMatches (observed : Option Import.ConntrackNetlink.Snapshot)
    (expected : ConntrackLifecycle.State) : Bool :=
  match observed with
  | none => true
  | some snapshot => Check.ConntrackLifecycle.sameRecords expected (Check.ConntrackLifecycle.snapshotState snapshot)

private def TableMatches (observed : Option Import.ConntrackNetlink.Snapshot)
    (expected : ConntrackLifecycle.State) : Prop :=
  ∀ snapshot, observed = some snapshot →
    Check.ConntrackLifecycle.SameRecords expected (Check.ConntrackLifecycle.snapshotState snapshot)

private theorem tableMatches_correct (observed : Option Import.ConntrackNetlink.Snapshot)
    (expected : ConntrackLifecycle.State) : tableMatches observed expected = true ↔ TableMatches observed expected := by
  cases observed <;> simp [tableMatches, TableMatches, Check.ConntrackLifecycle.sameRecords_correct]

private def cacheMatches (observed : Option (List CacheEntry)) (expected : ModelState) : Bool :=
  match observed with
  | none => true
  | some values => decide (cacheEntries expected = values)

private def CacheMatches (observed : Option (List CacheEntry)) (expected : ModelState) : Prop :=
  ∀ values, observed = some values → cacheEntries expected = values

private theorem cacheMatches_correct (observed : Option (List CacheEntry)) (expected : ModelState) :
    cacheMatches observed expected = true ↔ CacheMatches observed expected := by
  cases observed <;> simp [cacheMatches, CacheMatches]

def stateMatches (observation : Observation) (state : ModelState) : Bool :=
  tableMatches observation.primary state.primary && tableMatches observation.standby state.standby &&
    cacheMatches observation.cache state

def StateMatches (observation : Observation) (state : ModelState) : Prop :=
  TableMatches observation.primary state.primary ∧ TableMatches observation.standby state.standby ∧
    CacheMatches observation.cache state

theorem stateMatches_correct (observation : Observation) (state : ModelState) :
    stateMatches observation state = true ↔ StateMatches observation state := by
  simp [stateMatches, StateMatches, tableMatches_correct, cacheMatches_correct, and_assoc]

def packetMatches (observation : Observation) (result : ModelResult) : Bool :=
  match observation.event, result.packet with
  | .packet _ _ _ _ _ observed, some packet => observed.matches packet.outcome
  | .packet .., none => false
  | _, none => true
  | _, some _ => false

def PacketMatches (observation : Observation) (result : ModelResult) : Prop :=
  match observation.event, result.packet with
  | .packet _ _ _ _ _ observed, some packet => observed.Matches packet.outcome
  | .packet .., none => False
  | _, none => True
  | _, some _ => False

theorem packetMatches_correct (observation : Observation) (result : ModelResult) :
    packetMatches observation result = true ↔ PacketMatches observation result := by
  cases observation with
  | mk index event primary standby cache raw =>
    cases result with
    | mk state valid packet installed =>
      cases event <;> cases packet <;>
        simp [packetMatches, PacketMatches, Check.WireForwarding.PacketObservation.matches_correct]

def Matches (observation : Observation) (result : ModelResult) : Prop :=
  PacketMatches observation result ∧ StateMatches observation result.state

def replay (routing : Routing) : Replay.System ModelState Observation ModelResult where
  step := step routing
  state := (·.state)
  passed observation result := packetMatches observation result && stateMatches observation result.state
  Matches := Matches
  correct observation result := by
    simp [Matches, packetMatches_correct, stateMatches_correct]

abbrev Finding := Replay.Finding Observation ModelResult
abbrev Report (routing : Routing) (observations : List Observation) :=
  Replay.Report (replay routing) Netlib.Protocol.StatefulFailover.State.initial observations

def audit (routing : Routing) (observations : List Observation) : Except String (Report routing observations) :=
  Replay.audit (replay routing) Netlib.Protocol.StatefulFailover.State.initial observations

theorem prefixes_valid (report : Report routing observations) :
    report.final.Valid ∧ ∀ finding ∈ report.findings, finding.result.state.Valid :=
  report.trace.invariant (·.Valid) (fun _ _ result _ _ => result.valid)
    Netlib.Protocol.StatefulFailover.State.initial_valid

structure Input where
  routing : Routing
  configs : List Config
  events : List Observation

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def optional (parse : Lean.Json → Except String α) (json : Lean.Json) : Except String (Option α) :=
  match json with
  | .null => .ok none
  | value => some <$> parse value

private def gateway (json : Lean.Json) : Except String Gateway := do
  match ← json.getStr? with
  | "primary" => return .primary
  | "standby" => return .standby
  | value => throw s!"Unsupported gateway: {value}."

private def leg (json : Lean.Json) : Except String Leg := do
  match ← json.getStr? with
  | "client" => return .client
  | "server" => return .server
  | value => throw s!"Unsupported endpoint route: {value}."

private def zone (json : Lean.Json) : Except String Nat := do
  let value ← json.getNat?
  require (value == 0) "The selected replication profile requires zone zero."
  return value

private def inputPacket (json : Lean.Json) : Except String InputPacket := do
  let bytes ← Import.EAPOL.bytesFromHex (← json.getStr?)
  match decoded : UDP.decodeIPv4 bytes with
  | .error reason => throw reason
  | .ok packet => return ⟨bytes, packet, decoded⟩

private def cacheEntry (json : Lean.Json) : Except String CacheEntry := do
  Import.PacketFields.fields json ["original", "zone", "sourceNAT", "destinationNAT", "seenReply"]
  let original ← Import.PacketFields.header (← json.getObjVal? "original")
  require (original.protocol == Packet.Protocol.udp) "Require UDP cache attributes."
  return ⟨original, ← zone (← json.getObjVal? "zone"),
    ← optional Import.PacketFields.endpoint (← json.getObjVal? "sourceNAT"),
    ← optional Import.PacketFields.endpoint (← json.getObjVal? "destinationNAT"),
    ← (← json.getObjVal? "seenReply").getBool?⟩

private def parseCache (json : Lean.Json) : Except String (List CacheEntry) := do
  let values ← json.getArr?
  require (values.size ≤ 1) "The selected external cache has at most one record."
  values.toList.mapM cacheEntry

private def parseObservation (json : Lean.Json) (index : Nat) (configs : List Config) : Except String Observation := do
  let kind ← (← json.getObjVal? "type").getStr?
  let common := ["type", "states", "cache"]
  let event ← match kind with
    | "packet" => do
      Import.PacketFields.fields json (common ++ ["gateway", "leg", "config", "zone", "rawIPv4", "observed"])
      let id ← (← json.getObjVal? "config").getStr?
      let some config := configs.find? (·.id == id) | throw s!"Unknown failover configuration: {id}."
      pure (.packet (← gateway (← json.getObjVal? "gateway")) (← leg (← json.getObjVal? "leg")) config
        (← zone (← json.getObjVal? "zone")) (← inputPacket (← json.getObjVal? "rawIPv4"))
        (← Check.WireForwarding.PacketObservation.fromJson (← json.getObjVal? "observed")))
    | "stage" => do
      Import.PacketFields.fields json (common ++ ["zone", "key"])
      pure (.stage (← zone (← json.getObjVal? "zone")) (← Import.PacketFields.header (← json.getObjVal? "key")))
    | "commit" => do
      Import.PacketFields.fields json (common ++ ["timeout"])
      let timeout ← (← json.getObjVal? "timeout").getNat?
      require (0 < timeout && timeout < 4294967296) "Require a positive commit timeout below 2^32."
      pure (.commit timeout)
    | "handoff" => do
      Import.PacketFields.fields json (common ++ ["leg", "gateway"])
      pure (.handoff (← leg (← json.getObjVal? "leg")) (← gateway (← json.getObjVal? "gateway")))
    | "fence" => do
      Import.PacketFields.fields json (common ++ ["gateway"])
      pure (.fence (← gateway (← json.getObjVal? "gateway")))
    | "erase" => do
      Import.PacketFields.fields json (common ++ ["gateway", "zone", "key"])
      pure (.erase (← gateway (← json.getObjVal? "gateway")) (← zone (← json.getObjVal? "zone"))
        (← Import.PacketFields.header (← json.getObjVal? "key")))
    | "forget" => do
      Import.PacketFields.fields json common
      pure .forget
    | _ => throw s!"Unsupported failover event: {kind}."
  let states ← json.getObjVal? "states"
  Import.PacketFields.fields states ["primary", "standby"]
  return ⟨index, event,
    ← optional Import.ConntrackNetlink.Snapshot.fromJson (← states.getObjVal? "primary"),
    ← optional Import.ConntrackNetlink.Snapshot.fromJson (← states.getObjVal? "standby"),
    ← optional parseCache (← json.getObjVal? "cache"), json⟩

def Input.fromJson (json : Lean.Json) : Except String Input := do
  Import.PacketFields.fields json ["schema", "routing", "configs", "events"]
  require ((← (← json.getObjVal? "schema").getNat?) == 1) "Use stateful failover schema 1."
  let source ← json.getObjVal? "routing"
  Import.PacketFields.fields source ["primary", "standby"]
  let routing : Routing := ⟨← Check.ConntrackLifecycle.routingFromJson (← source.getObjVal? "primary"),
    ← Check.ConntrackLifecycle.routingFromJson (← source.getObjVal? "standby")⟩
  let values ← (← json.getObjVal? "configs").getArr?
  let mut configs := []
  for index in [:values.size] do
    let config ← Check.ConntrackLifecycle.Config.fromJson values[index]! index
    require (!(configs.any (·.id == config.id))) "Configuration IDs must be unique."
    configs := configs ++ [config]
  let values ← (← json.getObjVal? "events").getArr?
  let mut events := []
  for index in [:values.size] do
    events := events ++ [← (parseObservation values[index]! index configs).mapError (s!"/events/{index}: " ++ ·)]
  require (events.any fun observation => match observation.event with | .packet .. => true | _ => false)
    "Supply at least one packet event."
  return ⟨routing, configs, events⟩

def Input.parse (text : String) : Except String Input := do
  Input.fromJson (← Import.Json.parse text)

def Input.check (input : Input) : Except String (Report input.routing input.events) := audit input.routing input.events

private def gatewayText : Gateway → String
  | .primary => "primary"
  | .standby => "standby"

private def cacheJson (entry : CacheEntry) : Lean.Json := Lean.Json.mkObj [
  ("original", Import.PacketFields.headerJson entry.original), ("zone", Lean.toJson entry.zone),
  ("sourceNAT", (entry.sourceNAT.map Import.PacketFields.endpointJson).getD .null),
  ("destinationNAT", (entry.destinationNAT.map Import.PacketFields.endpointJson).getD .null),
  ("seenReply", Lean.toJson entry.seenReply)]

private def stateJson (state : ModelState) : Lean.Json := Lean.Json.mkObj [
  ("primary", Check.ConntrackLifecycle.stateJson state.primary),
  ("standby", Check.ConntrackLifecycle.stateJson state.standby),
  ("cache", Lean.toJson ((cacheEntries state).map cacheJson)),
  ("cacheSourceEpoch", Lean.toJson (state.cache.map (·.sourceEpoch))),
  ("owners", Lean.Json.mkObj [("client", Lean.toJson (gatewayText state.owners.client)),
    ("server", Lean.toJson (gatewayText state.owners.server))]),
  ("fenced", Lean.toJson (state.fenced.map gatewayText)), ("epoch", Lean.toJson state.epoch)]

def assumptions : List String := Check.WireForwarding.Report.assumptions ++ [
  "Both modeled kernel tables and the selected external cache start empty.",
  "Daemon cache observations faithfully join received FTFW attributes to the corresponding actual external cache object.",
  "Staging selects the primary's computed record; ACKs and command exit status do not establish cache or kernel success.",
  "Commit models a successful collision-free installation with a positive configured timeout; observed target tables independently check its result.",
  "Timeout is installation metadata; no aging, expiry, reliable synchronization, replacement, or deletion propagation is proved.",
  "Each endpoint route handoff and the data-interface fence has a faithful ordered command and readback binding.",
  "The endpoint leg and selected gateway identify the actual packet path; automatic failure detection and routing convergence are outside scope.",
  "Packets do not interleave the commands inside one declared handoff or fence operation.",
  "Current packet policy remains independent of the cached record; replication conveys no authentication or permission."]

def renderJson (report : Report routing observations) : Lean.Json := Lean.Json.mkObj [
  ("compliant", Lean.toJson report.compliant), ("scope", Lean.toJson "ordered-native-stateful-failover"),
  ("assumptions", Lean.toJson assumptions), ("eventCount", Lean.toJson observations.length),
  ("final", stateJson report.final),
  ("findings", Lean.toJson (report.findings.map fun finding => Lean.Json.mkObj [
    ("source", Lean.toJson s!"/events/{finding.observation.index}"), ("matched", Lean.toJson finding.passed),
    ("stateMatched", Lean.toJson (stateMatches finding.observation finding.result.state)),
    ("primaryObserved", Lean.toJson finding.observation.primary.isSome),
    ("standbyObserved", Lean.toJson finding.observation.standby.isSome),
    ("cacheObserved", Lean.toJson finding.observation.cache.isSome),
    ("expected", (finding.result.packet.map fun packet => Check.WireForwarding.outcomeToJson packet.outcome).getD .null),
    ("expectedState", stateJson finding.result.state)]))]

def render (report : Report routing observations) : String :=
  (if report.compliant then "STATEFUL FAILOVER OBSERVATIONS MATCH\n" else "STATEFUL FAILOVER OBSERVATIONS MISMATCH\n") ++
    (renderJson report).pretty

theorem Event.toModel_stage (event : Event) (routing : Routing) (before : ModelState) (zone : Nat) (packet : Header)
    (selected : event.toModel routing before = .stage zone packet) : event = .stage zone packet := by
  cases event <;> simp_all [Event.toModel]

theorem trace_cache_source (trace : Replay.Trace (replay routing) initial findings final) (selected : Replica)
    (cached : final.cache = some selected) :
    initial.cache = some selected ∨ ∃ prior stageFinding later beforeStage zone packet,
      findings = prior ++ stageFinding :: later ∧
      Replay.Trace (replay routing) initial prior beforeStage ∧
      step routing beforeStage stageFinding.observation = .ok stageFinding.result ∧
      stageFinding.observation.event = .stage zone packet ∧
      stageFinding.result.state.cache = some selected ∧
      selected.source = beforeStage.primary ∧ selected.sourceEpoch = beforeStage.epoch ∧
      selected.record ∈ beforeStage.primary.records ∧
      selected.record.entry.flow.key selected.direction = (zone, packet) := by
  induction trace with
  | nil => exact Or.inl cached
  | @cons before final head tail computed rest ih =>
    rcases ih cached with previous | staged
    · have actual : Netlib.Protocol.StatefulFailover.step before
          (head.observation.event.toModel routing before) = .ok head.result := computed
      rcases Netlib.Protocol.StatefulFailover.step_cache_origin _ _ _ _ actual previous with old | current
      · exact Or.inl old
      · obtain ⟨zone, packet, event, source, epoch, member, attached⟩ := current
        exact Or.inr ⟨[], head, tail, before, zone, packet, rfl, .nil before, computed,
          Event.toModel_stage _ _ _ _ _ event, previous, source, epoch, member, attached⟩
    · obtain ⟨prior, finding, later, preceding, zone, packet, covered, prefixTrace, accepted,
        event, cached, source, epoch, member, attached⟩ := staged
      exact Or.inr ⟨head :: prior, finding, later, preceding, zone, packet, by simp [covered],
        .cons computed prefixTrace, accepted, event, cached, source, epoch, member, attached⟩

theorem Report.cache_source (report : Report routing observations) (selected : Replica)
    (cached : report.final.cache = some selected) :
    ∃ prior stageFinding later beforeStage zone packet,
      report.findings = prior ++ stageFinding :: later ∧
      Replay.Trace (replay routing) Netlib.Protocol.StatefulFailover.State.initial prior beforeStage ∧
      step routing beforeStage stageFinding.observation = .ok stageFinding.result ∧
      stageFinding.observation.event = .stage zone packet ∧
      stageFinding.result.state.cache = some selected ∧
      selected.source = beforeStage.primary ∧ selected.sourceEpoch = beforeStage.epoch ∧
      selected.record ∈ beforeStage.primary.records ∧
      selected.record.entry.flow.key selected.direction = (zone, packet) := by
  rcases trace_cache_source report.trace selected cached with seeded | staged
  · simp [Netlib.Protocol.StatefulFailover.State.initial] at seeded
  · exact staged

theorem Report.commit_source (report : Report routing observations) (finding : Finding)
    (member : finding ∈ report.findings) (timeout : Nat)
    (event : finding.observation.event = .commit timeout) (installed : ConntrackReplication.Installed)
    (seen : finding.result.installed = some installed) :
    ∃ commitPrior commitLater beforeCommit selected stagePrior stageFinding stageLater beforeStage zone packet,
      report.findings = commitPrior ++ finding :: commitLater ∧
      Replay.Trace (replay routing) Netlib.Protocol.StatefulFailover.State.initial commitPrior beforeCommit ∧
      step routing beforeCommit finding.observation = .ok finding.result ∧
      beforeCommit.cache = some selected ∧
      ConntrackReplication.commit beforeCommit.standby selected timeout = .ok installed ∧
      installed.selection = selected ∧
      commitPrior = stagePrior ++ stageFinding :: stageLater ∧
      Replay.Trace (replay routing) Netlib.Protocol.StatefulFailover.State.initial stagePrior beforeStage ∧
      step routing beforeStage stageFinding.observation = .ok stageFinding.result ∧
      stageFinding.observation.event = .stage zone packet ∧
      stageFinding.result.state.cache = some selected ∧
      selected.source = beforeStage.primary ∧ selected.sourceEpoch = beforeStage.epoch ∧
      selected.record ∈ beforeStage.primary.records ∧
      selected.record.entry.flow.key selected.direction = (zone, packet) := by
  obtain ⟨commitPrior, commitLater, beforeCommit, covered, prefixTrace, accepted, _⟩ :=
    report.trace.prefix finding member
  change step routing beforeCommit finding.observation = .ok finding.result at accepted
  have actual : Netlib.Protocol.StatefulFailover.step beforeCommit (.commit timeout) = .ok finding.result := by
    simpa only [step, event, Event.toModel] using accepted
  obtain ⟨selected, result, cached, committed, reported, _⟩ :=
    Netlib.Protocol.StatefulFailover.step_commit _ _ _ actual
  have same : result = installed := Option.some.inj (reported.symm.trans seen)
  subst result
  have fields := ConntrackReplication.commit_fields _ _ _ _ committed
  rcases trace_cache_source prefixTrace selected cached with seeded | staged
  · simp [Netlib.Protocol.StatefulFailover.State.initial] at seeded
  · obtain ⟨stagePrior, stageFinding, stageLater, beforeStage, zone, packet, stageCovered, stageTrace,
        staged, stageEvent, cache, source, epoch, belongs, attached⟩ := staged
    exact ⟨commitPrior, commitLater, beforeCommit, selected, stagePrior, stageFinding, stageLater,
      beforeStage, zone, packet, covered, prefixTrace, accepted, cached, committed, fields.2.1,
      stageCovered, stageTrace, staged, stageEvent, cache, source, epoch, belongs, attached⟩


theorem Report.observed_output_facts (report : Report routing observations) (compliant : report.compliant = true)
    (finding : Finding) (member : finding ∈ report.findings) (gateway : Gateway) (leg : Leg)
    (config : Config) (zone : Nat) (source : InputPacket) (observed : Check.WireForwarding.PacketObservation)
    (event : finding.observation.event = .packet gateway leg config zone source observed)
    (captured : Check.WireForwarding.WirePacket) (seen : observed.output = some captured) :
    ∃ (prior later : List Finding) (before : ModelState) (call : Netlib.Protocol.StatefulFailover.PacketCall)
      (outcome : Protocol.WireForwarding.Outcome call.input.packet)
      (emission : Protocol.WireForwarding.Emission call.input.packet) (model : ConntrackLifecycle.Outcome),
      report.findings = prior ++ finding :: later ∧
      Replay.Trace (replay routing) Netlib.Protocol.StatefulFailover.State.initial prior before ∧
      step routing before finding.observation = .ok finding.result ∧
      call.gateway = gateway ∧ call.leg = leg ∧ call.pipeline = config.pipeline (routing.table gateway) ∧
      call.input.zone = zone ∧ call.input.packet = source.packet ∧
      gateway = before.owners.get leg ∧ before.isFenced gateway = false ∧
      Protocol.WireForwarding.step call.pipeline (before.table gateway) call.input = .ok outcome ∧
      finding.result.packet = some ⟨call, outcome⟩ ∧ outcome.output = some emission ∧
      captured.value = Check.WireForwarding.emissionValue emission ∧
      captured.checked.packet.datagram.payload = source.packet.datagram.payload ∧
      captured.checked.packet.ip.packet.ttl.toNat = source.packet.ip.packet.ttl.toNat - 1 ∧
      ConntrackLifecycle.step call.pipeline (before.table gateway) call.input.lifecycle = .ok model ∧
      model.output = some emission.target ∧ emission.target = model.attachment.entry.flow.output model.attachment.direction ∧
      StatefulACL.Policy.evaluate call.pipeline.forwardDefault call.pipeline.forward outcome.attachment.classification
        outcome.afterDestination = .permit ∧
      StatefulACL.Policy.evaluate call.pipeline.lateDefault call.pipeline.late outcome.attachment.classification
        emission.target = .permit := by
  obtain ⟨prior, later, before, covered, prefixTrace, computed, _⟩ := report.trace.prefix finding member
  change step routing before finding.observation = .ok finding.result at computed
  let call : Netlib.Protocol.StatefulFailover.PacketCall := ⟨gateway, leg, config.pipeline (routing.table gateway),
    ⟨zone, source.packet, if ((before.table gateway).model.lookup zone source.packet.header).isNone then
      some (config.nat.candidate zone source.packet.header) else none⟩⟩
  have actual : Netlib.Protocol.StatefulFailover.step before (.packet call) = .ok finding.result := by
    simpa only [step, event, Event.toModel, call] using computed
  obtain ⟨owner, unfenced, outcome, forwarded, reported, _⟩ :=
    Netlib.Protocol.StatefulFailover.step_packet _ _ _ actual
  have matched := (Replay.Report.finding_matches report compliant finding member).1
  unfold PacketMatches at matched
  rw [event, reported] at matched
  obtain ⟨_, _, _, _, _, _, outputs⟩ := matched
  cases emitted : outcome.output with
  | none => simp [seen, emitted] at outputs
  | some emission =>
    rw [seen, emitted] at outputs
    have sameValue := Option.some.inj outputs
    obtain ⟨model, modeled, modelOutput, _⟩ := Protocol.WireForwarding.step_output _ _ _ _ forwarded emission emitted
    have binding := ConntrackLifecycle.step_output _ _ _ _ _ modeled modelOutput
    have filters := Protocol.WireForwarding.step_filters _ _ _ _ forwarded emission emitted
    refine ⟨prior, later, before, call, outcome, emission, model, covered, prefixTrace, computed,
      rfl, rfl, rfl, rfl, rfl, owner, unfenced, forwarded, reported, emitted, sameValue, ?_, ?_,
      modeled, modelOutput, binding, filters.2.2.1, filters.2.2.2.1⟩
    · have data := congrArg Prod.snd sameValue
      change captured.checked.packet.datagram = emission.decoded.datagram at data
      rw [data]
      exact emission.payload
    · have header := congrArg Prod.fst sameValue
      change captured.checked.packet.ip.packet = emission.decoded.ip.packet at header
      rw [header]
      exact emission.ttl


end Netlib.Check.StatefulFailover
