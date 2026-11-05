import Netlib.Check.Replay
import Netlib.Check.ReplayOrigin
import Netlib.Protocol.SafeHandoffFacts
import Netlib.Check.StatefulFailover
import Netlib.Protocol.SafeHandoff

/-!
# Replay of route admission, delayed processing, and safe fencing

Early validated bytes allocate a ticket at the route-selected gateway.
Later gateway bytes are observations of that stored source, never replacement input.
Installed configurations evolve independently of tickets and govern their later processing.
-/

namespace Netlib.Check.SafeHandoff

open Packet Protocol
open Protocol.StatefulFailover (Gateway)
abbrev ModelState := Protocol.SafeHandoff.State
abbrev ModelResult := Protocol.SafeHandoff.Result
abbrev Source := Protocol.SafeHandoff.Source
abbrev Config := Check.ConntrackLifecycle.Config
abbrev Routing := Check.StatefulFailover.Routing
abbrev CacheEntry := Check.StatefulFailover.CacheEntry

def configuration (routing : Routing) (gateway : Gateway) (config : Config) : Protocol.SafeHandoff.Configuration :=
  ⟨config.id, config.pipeline (routing.table gateway)⟩

inductive Event where
  | establish (zone : Nat) (source : Source) (observed : Check.WireForwarding.PacketObservation)
  | stage (zone : Nat) (key : Header)
  | commit (timeout : Nat)
  | handoff (leg : Protocol.StatefulFailover.Leg) (gateway : Gateway)
  | fence (gateway : Gateway)
  | forget
  | install (gateway : Gateway) (config : Config)
  | assign (direction : FlowNAT.Direction) (source : Source) (observedID : Option Nat)
  | serve (id : Nat) (observedInput : Source) (observed : Check.WireForwarding.PacketObservation)

def Event.toModel (routing : Routing) (configs : List Config) (before : ModelState) :
    Event → Except String Protocol.SafeHandoff.Event
  | .establish zone source _ => do
    let id := (before.configurations .primary).id
    let some config := configs.find? (·.id == id) | throw s!"Unknown installed primary configuration: {id}."
    let candidate := if (before.gateways.primary.model.lookup zone source.packet.header).isNone then
      some (config.nat.candidate zone source.packet.header) else none
    return .establish ⟨zone, source.packet, candidate⟩
  | .stage zone key => .ok (.stage zone key)
  | .commit timeout => .ok (.commit timeout)
  | .handoff selectedLeg gateway => .ok (.handoff selectedLeg gateway)
  | .fence gateway => .ok (.fence gateway)
  | .forget => .ok .forget
  | .install gateway config => .ok (.install gateway (configuration routing gateway config))
  | .assign direction source _ => .ok (.assign direction source)
  | .serve id _ _ => .ok (.serve id)

structure Observation where
  index : Nat
  event : Event
  primary : Option Import.ConntrackNetlink.Snapshot
  standby : Option Import.ConntrackNetlink.Snapshot
  cache : Option (List CacheEntry)
  raw : Lean.Json

def step (routing : Routing) (configs : List Config) (before : ModelState) (observation : Observation) :
    Except String ModelResult := do
  let event ← observation.event.toModel routing configs before
  Protocol.SafeHandoff.step before event

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
  | some values => decide (Check.StatefulFailover.cacheEntries expected.gateways = values)

private def CacheMatches (observed : Option (List CacheEntry)) (expected : ModelState) : Prop :=
  ∀ values, observed = some values → Check.StatefulFailover.cacheEntries expected.gateways = values

private theorem cacheMatches_correct (observed : Option (List CacheEntry)) (expected : ModelState) :
    cacheMatches observed expected = true ↔ CacheMatches observed expected := by
  cases observed <;> simp [cacheMatches, CacheMatches]

def stateMatches (observation : Observation) (state : ModelState) : Bool :=
  tableMatches observation.primary state.gateways.primary && tableMatches observation.standby state.gateways.standby &&
    cacheMatches observation.cache state

def StateMatches (observation : Observation) (state : ModelState) : Prop :=
  TableMatches observation.primary state.gateways.primary ∧ TableMatches observation.standby state.gateways.standby ∧
    CacheMatches observation.cache state

theorem stateMatches_correct (observation : Observation) (state : ModelState) :
    stateMatches observation state = true ↔ StateMatches observation state := by
  simp [stateMatches, StateMatches, tableMatches_correct, cacheMatches_correct, and_assoc]

private def ticketMatches (observed : Option Nat) (result : ModelResult) : Bool :=
  match observed with
  | none => true
  | some id => result.admitted.any (fun ticket => decide (ticket.id = id))

private def TicketMatches (observed : Option Nat) (result : ModelResult) : Prop :=
  ∀ id, observed = some id → ∃ ticket, result.admitted = some ticket ∧ ticket.id = id

private theorem ticketMatches_correct (observed : Option Nat) (result : ModelResult) :
    ticketMatches observed result = true ↔ TicketMatches observed result := by
  cases observed <;> cases found : result.admitted <;> simp [ticketMatches, TicketMatches, found]

def packetMatches (observation : Observation) (result : ModelResult) : Bool :=
  match observation.event, result.established, result.served with
  | .establish _ _ observed, some packet, none => observed.matches packet.outcome
  | .serve _ seen observed, none, some packet =>
    decide (packet.ticket.value.source.bytes = seen.bytes) && observed.matches packet.outcome
  | .assign _ _ observed, none, none => ticketMatches observed result
  | .establish .., _, _ | .serve .., _, _ | .assign .., _, _ => false
  | _, none, none => true
  | _, _, _ => false

def PacketMatches (observation : Observation) (result : ModelResult) : Prop :=
  match observation.event, result.established, result.served with
  | .establish _ _ observed, some packet, none => observed.Matches packet.outcome
  | .serve _ seen observed, none, some packet =>
    packet.ticket.value.source.bytes = seen.bytes ∧ observed.Matches packet.outcome
  | .assign _ _ observed, none, none => TicketMatches observed result
  | .establish .., _, _ | .serve .., _, _ | .assign .., _, _ => False
  | _, none, none => True
  | _, _, _ => False

theorem packetMatches_correct (observation : Observation) (result : ModelResult) :
    packetMatches observation result = true ↔ PacketMatches observation result := by
  cases observation with
  | mk index event primary standby cache raw =>
    cases result with
    | mk rawResult safe =>
      cases rawResult with
      | mk state admitted served established =>
        cases event <;> cases established <;> cases served <;>
          simp [packetMatches, PacketMatches, ticketMatches_correct,
            Check.WireForwarding.PacketObservation.matches_correct]

def Matches (observation : Observation) (result : ModelResult) : Prop :=
  PacketMatches observation result ∧ StateMatches observation result.state

def replay (routing : Routing) (configs : List Config) : Replay.System ModelState Observation ModelResult where
  step := step routing configs
  state := (·.state)
  passed observation result := packetMatches observation result && stateMatches observation result.state
  Matches := Matches
  correct observation result := by simp [Matches, packetMatches_correct, stateMatches_correct]

abbrev Finding := Replay.Finding Observation ModelResult
abbrev Report (routing : Routing) (configs : List Config) (initial : ModelState) (observations : List Observation) :=
  Replay.Report (replay routing configs) initial observations

def audit (routing : Routing) (configs : List Config) (initial : ModelState) (observations : List Observation) :
    Except String (Report routing configs initial observations) := Replay.audit (replay routing configs) initial observations

theorem prefixes_safe (report : Report routing configs initial observations) (safe : initial.Safe) :
    report.final.Safe ∧ ∀ finding ∈ report.findings, finding.result.state.Safe :=
  report.trace.invariant (·.Safe) (fun _ _ result _ _ => result.safe) safe

structure Input where
  routing : Routing
  configs : List Config
  primary : Config
  standby : Config
  events : List Observation

def Input.initial (input : Input) : ModelState :=
  Protocol.SafeHandoff.State.initial (configuration input.routing .primary input.primary)
    (configuration input.routing .standby input.standby)

theorem Input.initial_safe (input : Input) : input.initial.Safe := Protocol.SafeHandoff.State.initial_safe _ _

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

private def routeLeg (json : Lean.Json) : Except String Protocol.StatefulFailover.Leg := do
  match ← json.getStr? with
  | "client" => return .client
  | "server" => return .server
  | value => throw s!"Unsupported endpoint route: {value}."

private def direction (json : Lean.Json) : Except String FlowNAT.Direction := do
  match ← json.getStr? with
  | "original" => return .original
  | "reply" => return .reply
  | value => throw s!"Unsupported protected flow direction: {value}."

private def zone (json : Lean.Json) : Except String Nat := do
  let value ← json.getNat?
  require (value == 0) "The selected handoff profile requires zone zero."
  return value

private def source (json : Lean.Json) : Except String Source := do
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
  require (values.size ≤ 1) "The selected external cache has at most one protected record."
  values.toList.mapM cacheEntry

private def selectConfig (json : Lean.Json) (configs : List Config) : Except String Config := do
  let id ← json.getStr?
  let some config := configs.find? (·.id == id) | throw s!"Unknown handoff configuration: {id}."
  return config

private def parseObservation (json : Lean.Json) (index : Nat) (configs : List Config) : Except String Observation := do
  let kind ← (← json.getObjVal? "type").getStr?
  let common := ["type", "states", "cache"]
  let event ← match kind with
    | "establish" => do
      Import.PacketFields.fields json (common ++ ["zone", "rawIPv4", "observed"])
      pure (.establish (← zone (← json.getObjVal? "zone")) (← source (← json.getObjVal? "rawIPv4"))
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
      pure (.handoff (← routeLeg (← json.getObjVal? "leg")) (← gateway (← json.getObjVal? "gateway")))
    | "fence" => do
      Import.PacketFields.fields json (common ++ ["gateway"])
      pure (.fence (← gateway (← json.getObjVal? "gateway")))
    | "forget" => do
      Import.PacketFields.fields json common
      pure .forget
    | "install" => do
      Import.PacketFields.fields json (common ++ ["gateway", "config"])
      pure (.install (← gateway (← json.getObjVal? "gateway")) (← selectConfig (← json.getObjVal? "config") configs))
    | "admit" => do
      Import.PacketFields.fields json (common ++ ["direction", "rawIPv4", "observedID"])
      pure (.assign (← direction (← json.getObjVal? "direction")) (← source (← json.getObjVal? "rawIPv4"))
        (← optional Lean.Json.getNat? (← json.getObjVal? "observedID")))
    | "serve" => do
      Import.PacketFields.fields json (common ++ ["id", "rawIPv4", "observed"])
      pure (.serve (← (← json.getObjVal? "id").getNat?) (← source (← json.getObjVal? "rawIPv4"))
        (← Check.WireForwarding.PacketObservation.fromJson (← json.getObjVal? "observed")))
    | _ => throw s!"Unsupported safe handoff event: {kind}."
  let states ← json.getObjVal? "states"
  Import.PacketFields.fields states ["primary", "standby"]
  return ⟨index, event,
    ← optional Import.ConntrackNetlink.Snapshot.fromJson (← states.getObjVal? "primary"),
    ← optional Import.ConntrackNetlink.Snapshot.fromJson (← states.getObjVal? "standby"),
    ← optional parseCache (← json.getObjVal? "cache"), json⟩

def Input.fromJson (json : Lean.Json) : Except String Input := do
  Import.PacketFields.fields json ["schema", "routing", "configs", "initialConfigs", "events"]
  require ((← (← json.getObjVal? "schema").getNat?) == 1) "Use safe handoff schema 1."
  let routes ← json.getObjVal? "routing"
  Import.PacketFields.fields routes ["primary", "standby"]
  let routing : Routing := ⟨← Check.ConntrackLifecycle.routingFromJson (← routes.getObjVal? "primary"),
    ← Check.ConntrackLifecycle.routingFromJson (← routes.getObjVal? "standby")⟩
  let values ← (← json.getObjVal? "configs").getArr?
  let mut configs := []
  for index in [:values.size] do
    let config ← Check.ConntrackLifecycle.Config.fromJson values[index]! index
    require (!(configs.any (·.id == config.id))) "Configuration IDs must be unique."
    configs := configs ++ [config]
  let initial ← json.getObjVal? "initialConfigs"
  Import.PacketFields.fields initial ["primary", "standby"]
  let primary ← selectConfig (← initial.getObjVal? "primary") configs
  let standby ← selectConfig (← initial.getObjVal? "standby") configs
  let values ← (← json.getObjVal? "events").getArr?
  let mut events := []
  for index in [:values.size] do
    events := events ++ [← (parseObservation values[index]! index configs).mapError (s!"/events/{index}: " ++ ·)]
  require (events.any fun observation => match observation.event with | .serve .. => true | _ => false)
    "Supply at least one outstanding-ticket processing event."
  return ⟨routing, configs, primary, standby, events⟩

def Input.parse (text : String) : Except String Input := do
  Input.fromJson (← Import.Json.parse text)

def Input.check (input : Input) : Except String (Report input.routing input.configs input.initial input.events) :=
  audit input.routing input.configs input.initial input.events

private def gatewayText : Gateway → String
  | .primary => "primary"
  | .standby => "standby"

private def directionText : FlowNAT.Direction → String
  | .original => "original"
  | .reply => "reply"

private def ticketJson (item : Theory.Outstanding.Item Protocol.SafeHandoff.Ticket) : Lean.Json := Lean.Json.mkObj [
  ("id", Lean.toJson item.id), ("gateway", Lean.toJson (gatewayText item.value.gateway)),
  ("direction", Lean.toJson (directionText item.value.direction)), ("routeEpoch", Lean.toJson item.value.routeEpoch),
  ("rawIPv4", Lean.toJson (Import.EAPOL.bytesToHex item.value.source.bytes))]

private def stateJson (state : ModelState) : Lean.Json := Lean.Json.mkObj [
  ("primary", Check.ConntrackLifecycle.stateJson state.gateways.primary),
  ("standby", Check.ConntrackLifecycle.stateJson state.gateways.standby),
  ("configurations", Lean.Json.mkObj [("primary", Lean.toJson (state.configurations .primary).id),
    ("standby", Lean.toJson (state.configurations .standby).id)]),
  ("binding", (state.binding.map fun entry => Lean.Json.mkObj [
    ("original", Import.PacketFields.headerJson entry.flow.original),
    ("reply", Import.PacketFields.headerJson entry.flow.reply),
    ("sourceNAT", Lean.toJson entry.sourceNAT), ("destinationNAT", Lean.toJson entry.destinationNAT)]).getD .null),
  ("cacheSourceEpoch", Lean.toJson (state.gateways.cache.map (·.sourceEpoch))),
  ("pending", Lean.toJson (state.work.pending.map ticketJson)),
  ("completedIDs", Lean.toJson (state.work.completed.map (·.id))), ("nextID", Lean.toJson state.work.nextID),
  ("outstanding", Lean.Json.mkObj [("primary", Lean.toJson (state.outstanding .primary)),
    ("standby", Lean.toJson (state.outstanding .standby))]),
  ("owners", Lean.Json.mkObj [("client", Lean.toJson (gatewayText state.gateways.owners.client)),
    ("server", Lean.toJson (gatewayText state.gateways.owners.server))]),
  ("fenced", Lean.toJson (state.gateways.fenced.map gatewayText)), ("epoch", Lean.toJson state.gateways.epoch)]

private def eventText : Event → String
  | .establish .. => "establish"
  | .stage .. => "stage"
  | .commit .. => "commit"
  | .handoff .. => "handoff"
  | .fence .. => "fence"
  | .forget => "forget"
  | .install .. => "install"
  | .assign .. => "admit"
  | .serve .. => "serve"

private def outcomeJson (result : ModelResult) : Lean.Json :=
  match result.served, result.established with
  | some packet, _ => Check.WireForwarding.outcomeToJson packet.outcome
  | none, some packet => Check.WireForwarding.outcomeToJson packet.outcome
  | none, none => .null

def assumptions : List String := [
  "Both gateway tables, the cache, and outstanding work start empty; initial configurations faithfully bind their declared native exports.",
  "Captured native tables and compiled configurations describe the exclusive route, NAT, forward, and late processing stages.",
  "The ordinary UDP tracker accepts modeled attachment without expiry, helpers, reopen, replacement, offload, or clash recovery.",
  "The selected path has sufficient MTU and performs no encapsulation or fragmentation.",
  "Kernel snapshot comparison checks supported tuple, zone, NAT, and seen-reply fields while ignoring IDs, order, and remaining timeout seconds.",
  "Cache observations join actual received FTFW attributes to external cache membership; ACKs and command exit status do not establish installation.",
  "Kernel commitment is successful and collision-free; timeout is metadata without modeled aging or reliable replication.",
  "Route reads, gateway processing, and individual configuration transitions admit the declared event linearization.",
  "Endpoint admission bytes faithfully identify the selected output interface after a route read and before the declared queue.",
  "Admission bytes satisfy the complete UDP checksum codec; NFLOG supplies no checksum-readiness metadata or proof of a partial checksum state.",
  "Assigned gateways and admission bytes remain attached to outstanding tickets across later endpoint route changes.",
  "A serve observation identifies the same ticket at gateway processing; its bytes and output observations never replace stored admission input.",
  "Each ticket uses the gateway configuration installed at processing, with stable hooks during that selected packet's execution.",
  "Ticket completion records a computed gateway outcome, including policy denial; it does not imply network or application delivery.",
  "Fencing requires no outstanding selected ticket to that gateway and neither endpoint route selecting it.",
  "Queue-empty readbacks alone do not establish physical draining; native evidence also joins every selected old admission to its gateway outcome.",
  "The modeled outstanding-work set permits arbitrary completion order; no global FIFO or automatic fair scheduling is assumed.",
  "Physical capture completeness, route-to-ticket correspondence, lifetime stability, and implementation refinement remain external premises."]

def renderJson (report : Report routing configs initial observations) : Lean.Json := Lean.Json.mkObj [
  ("compliant", Lean.toJson report.compliant), ("scope", Lean.toJson "inflight-safe-gateway-handoff"),
  ("assumptions", Lean.toJson assumptions), ("eventCount", Lean.toJson observations.length),
  ("final", stateJson report.final),
  ("findings", Lean.toJson (report.findings.map fun finding => Lean.Json.mkObj [
    ("source", Lean.toJson s!"/events/{finding.observation.index}"),
    ("type", Lean.toJson (eventText finding.observation.event)),
    ("matched", Lean.toJson finding.passed), ("stateMatched", Lean.toJson (stateMatches finding.observation finding.result.state)),
    ("primaryObserved", Lean.toJson finding.observation.primary.isSome),
    ("standbyObserved", Lean.toJson finding.observation.standby.isSome), ("cacheObserved", Lean.toJson finding.observation.cache.isSome),
    ("admitted", (finding.result.admitted.map ticketJson).getD .null),
    ("served", (finding.result.served.map fun packet => Lean.Json.mkObj [
      ("ticket", ticketJson packet.ticket), ("configuration", Lean.toJson packet.configuration.id)]).getD .null),
    ("expected", outcomeJson finding.result), ("expectedState", stateJson finding.result.state)]))]

def render (report : Report routing configs initial observations) : String :=
  (if report.compliant then "SAFE HANDOFF OBSERVATIONS MATCH\n" else "SAFE HANDOFF OBSERVATIONS MISMATCH\n") ++
    (renderJson report).pretty

private theorem core_control_work (before : ModelState) (event : Protocol.StatefulFailover.Event) (raw : Protocol.SafeHandoff.RawResult)
    (accepted : (do
      let result ← Protocol.StatefulFailover.step before.gateways event
      pure (⟨{ before with gateways := result.state }, none, none, result.packet⟩ : Protocol.SafeHandoff.RawResult)) = .ok raw) :
    raw.state.work = before.work := by
  cases computed : Protocol.StatefulFailover.step before.gateways event with
  | error error => simp [computed, bind, Except.bind] at accepted
  | ok result =>
    simp only [computed, bind, Except.bind, pure, Except.pure] at accepted
    cases accepted
    rfl

private theorem core_idle_work (before : ModelState) (event : Protocol.SafeHandoff.Event) (raw : Protocol.SafeHandoff.RawResult)
    (accepted : Protocol.SafeHandoff.core before event = .ok raw)
    (notAdmit : ∀ direction source, event ≠ .assign direction source)
    (notServe : ∀ id, event ≠ .serve id) : raw.state.work = before.work := by
  cases event with
  | establish input =>
    simp only [Protocol.SafeHandoff.core] at accepted
    split at accepted
    · simp [throw, throwThe, bind, Except.bind] at accepted
    · exact core_control_work before _ raw accepted
  | stage zone key =>
    simp only [Protocol.SafeHandoff.core] at accepted
    cases computed : Protocol.StatefulFailover.step before.gateways (.stage zone key) with
    | error error => simp [computed, bind, Except.bind] at accepted
    | ok result =>
      simp only [computed, bind, Except.bind] at accepted
      cases cached : result.state.cache with
      | none => simp [cached, throw] at accepted
      | some selection =>
        simp only [cached] at accepted
        cases binding : before.binding with
        | none => simp only [binding, pure, Except.pure] at accepted; cases accepted; rfl
        | some entry =>
          simp only [binding] at accepted
          split at accepted
          · simp [throw] at accepted
          · simp only [pure, Except.pure] at accepted; cases accepted; rfl
  | commit timeout =>
    simp only [Protocol.SafeHandoff.core] at accepted
    cases binding : before.binding with
    | none => simp [binding, throw] at accepted
    | some entry =>
      simp only [binding] at accepted
      cases cached : before.gateways.cache with
      | none => simp [cached, throw] at accepted
      | some selection =>
        simp only [cached] at accepted
        split at accepted
        · simp [throw, bind, Except.bind] at accepted
        · exact core_control_work before _ raw accepted
  | handoff selectedLeg gateway =>
    simp only [Protocol.SafeHandoff.core] at accepted
    cases binding : before.binding with
    | none => simp [binding, throw] at accepted
    | some entry =>
      simp only [binding] at accepted
      split at accepted
      · simp [throw, bind, Except.bind] at accepted
      · split at accepted
        · simp [throw, bind, Except.bind] at accepted
        · exact core_control_work before _ raw accepted
  | fence gateway =>
    simp only [Protocol.SafeHandoff.core] at accepted
    split at accepted
    · simp [throw, bind, Except.bind] at accepted
    · split at accepted
      · simp [throw, bind, Except.bind] at accepted
      · exact core_control_work before _ raw accepted
  | forget => exact core_control_work before _ raw accepted
  | install gateway config => simp only [Protocol.SafeHandoff.core, Except.ok.injEq] at accepted; cases accepted; rfl
  | assign direction source => exact False.elim (notAdmit direction source rfl)
  | serve id => exact False.elim (notServe id rfl)

theorem step_model (routing : Routing) (configs : List Config) (before : ModelState)
    (observation : Observation) (result : ModelResult)
    (accepted : step routing configs before observation = .ok result) :
    ∃ event, observation.event.toModel routing configs before = .ok event ∧
      Protocol.SafeHandoff.step before event = .ok result := by
  unfold step at accepted
  cases translated : observation.event.toModel routing configs before with
  | error error => simp [translated, bind, Except.bind] at accepted
  | ok event => exact ⟨event, rfl, by simpa only [translated, bind, Except.bind] using accepted⟩

theorem Event.toModel_assign (event : Event) (routing : Routing) (configs : List Config) (before : ModelState)
    (direction : FlowNAT.Direction) (source : Source)
    (selected : event.toModel routing configs before = .ok (.assign direction source)) :
    ∃ observed, event = .assign direction source observed := by
  cases event with
  | establish zone input seen =>
    simp only [Event.toModel] at selected
    cases found : configs.find? (fun config => config.id == (before.configurations .primary).id) with
    | none => simp [found] at selected
    | some config => simp [found, pure, Except.pure] at selected
  | assign dir input seen =>
    simp only [Event.toModel, Except.ok.injEq, Protocol.SafeHandoff.Event.assign.injEq] at selected
    obtain ⟨rfl, rfl⟩ := selected
    exact ⟨seen, rfl⟩
  | stage zone key => simp [Event.toModel] at selected
  | commit timeout => simp [Event.toModel] at selected
  | handoff selectedLeg gateway => simp [Event.toModel] at selected
  | fence gateway => simp [Event.toModel] at selected
  | forget => simp [Event.toModel] at selected
  | install gateway config => simp [Event.toModel] at selected
  | serve id input seen => simp [Event.toModel] at selected

def AdmissionOrigin (before : ModelState) (finding : Finding)
    (item : Theory.Outstanding.Item Protocol.SafeHandoff.Ticket) : Prop :=
  ∃ direction source observedID,
    finding.observation.event = .assign direction source observedID ∧
    finding.result.admitted = some item ∧ before.binding = some item.value.entry ∧
    item.id = before.work.nextID ∧
    item.value.gateway = before.gateways.owners.get (Protocol.SafeHandoff.leg direction) ∧
    item.value.direction = direction ∧ item.value.source = source ∧
    item.value.routeEpoch = before.gateways.epoch

theorem step_pending_origin (before : ModelState) (finding : Finding)
    (accepted : step routing configs before finding.observation = .ok finding.result)
    (item : Theory.Outstanding.Item Protocol.SafeHandoff.Ticket)
    (present : item ∈ finding.result.state.work.pending) :
    item ∈ before.work.pending ∨ AdmissionOrigin before finding item := by
  obtain ⟨event, translated, computed⟩ := step_model routing configs before finding.observation finding.result accepted
  obtain ⟨safe, raw, coreEq, rawEq⟩ := Protocol.SafeHandoff.step_core before event finding.result computed
  have pending : item ∈ raw.state.work.pending := by simpa only [← rawEq] using present
  cases event with
  | assign direction source =>
    obtain ⟨newItem, reported, binding, allocated, assigned, dirEq, sourceEq, epochEq, _, workEq, _⟩ :=
      Protocol.SafeHandoff.core_assign_facts before direction source raw coreEq
    rw [workEq] at pending
    rcases List.mem_append.mp pending with old | created
    · exact .inl old
    · have eq := List.mem_singleton.mp created
      subst newItem
      obtain ⟨observed, observationEq⟩ := Event.toModel_assign finding.observation.event routing configs before direction source translated
      exact .inr ⟨direction, source, observed, observationEq, by simpa only [← rawEq] using reported,
        binding, allocated, assigned, dirEq, sourceEq, epochEq⟩
  | serve id =>
    obtain ⟨completed, _, _, _, _, _, _, _, workEq, _⟩ := Protocol.SafeHandoff.core_serve_facts before id raw coreEq
    rw [workEq] at pending
    exact .inl (completed.pendingPerm.mem_iff.mpr (List.mem_cons_of_mem _ pending))
  | establish input =>
    have same := core_idle_work before _ raw coreEq (by intros; simp) (by intros; simp)
    exact .inl (by simpa only [same] using pending)
  | stage zone key =>
    have same := core_idle_work before _ raw coreEq (by intros; simp) (by intros; simp)
    exact .inl (by simpa only [same] using pending)
  | commit timeout =>
    have same := core_idle_work before _ raw coreEq (by intros; simp) (by intros; simp)
    exact .inl (by simpa only [same] using pending)
  | handoff selectedLeg gateway =>
    have same := core_idle_work before _ raw coreEq (by intros; simp) (by intros; simp)
    exact .inl (by simpa only [same] using pending)
  | fence gateway =>
    have same := core_idle_work before _ raw coreEq (by intros; simp) (by intros; simp)
    exact .inl (by simpa only [same] using pending)
  | forget =>
    have same := core_idle_work before _ raw coreEq (by intros; simp) (by intros; simp)
    exact .inl (by simpa only [same] using pending)
  | install gateway config =>
    have same := core_idle_work before _ raw coreEq (by intros; simp) (by intros; simp)
    exact .inl (by simpa only [same] using pending)

theorem trace_pending_source (trace : Replay.Trace (replay routing configs) initial findings final)
    (item : Theory.Outstanding.Item Protocol.SafeHandoff.Ticket) (pending : item ∈ final.work.pending) :
    item ∈ initial.work.pending ∨ ∃ prior finding later before,
      findings = prior ++ finding :: later ∧ Replay.Trace (replay routing configs) initial prior before ∧
      step routing configs before finding.observation = .ok finding.result ∧ AdmissionOrigin before finding item :=
  trace.origin (fun state item => item ∈ state.work.pending) AdmissionOrigin
    (fun before finding item accepted present => step_pending_origin before finding accepted item present) item pending


theorem Report.served_source (input : Input) (report : Report input.routing input.configs input.initial input.events)
    (finding : Finding) (member : finding ∈ report.findings) (id : Nat) (observedInput : Source)
    (observed : Check.WireForwarding.PacketObservation)
    (event : finding.observation.event = .serve id observedInput observed)
    (served : Protocol.SafeHandoff.PacketResult) (seen : finding.result.served = some served) :
    ∃ servePrior serveLater beforeServe admitPrior admitFinding admitLater beforeAdmit,
      report.findings = servePrior ++ finding :: serveLater ∧
      Replay.Trace (replay input.routing input.configs) input.initial servePrior beforeServe ∧
      step input.routing input.configs beforeServe finding.observation = .ok finding.result ∧
      served.ticket ∈ beforeServe.work.pending ∧ served.ticket.id = id ∧
      served.configuration = beforeServe.configurations served.ticket.value.gateway ∧
      Protocol.WireForwarding.step served.configuration.pipeline
        (beforeServe.gateways.table served.ticket.value.gateway)
        (TrackedFlow.wireInput served.ticket.value.entry served.ticket.value.direction served.ticket.value.source.packet) =
        .ok served.outcome ∧
      servePrior = admitPrior ++ admitFinding :: admitLater ∧
      Replay.Trace (replay input.routing input.configs) input.initial admitPrior beforeAdmit ∧
      step input.routing input.configs beforeAdmit admitFinding.observation = .ok admitFinding.result ∧
      AdmissionOrigin beforeAdmit admitFinding served.ticket := by
  obtain ⟨prior, later, before, covered, prefixTrace, accepted, _⟩ := report.trace.prefix finding member
  have actual : Protocol.SafeHandoff.step before (.serve id) = .ok finding.result := by
    simpa only [replay, step, event, Event.toModel, bind, Except.bind] using accepted
  obtain ⟨_, raw, coreEq, rawEq⟩ := Protocol.SafeHandoff.step_core before (.serve id) finding.result actual
  obtain ⟨completed, outcome, _, reported, _, _, _, computed, _⟩ :=
    Protocol.SafeHandoff.core_serve_facts before id raw coreEq
  have reported' : finding.result.served = some
      (⟨completed.item, before.configurations completed.item.value.gateway, outcome⟩ : Protocol.SafeHandoff.PacketResult) := by
    simpa only [← rawEq] using reported
  have equal := Option.some.inj (seen.symm.trans reported')
  cases equal
  rcases trace_pending_source prefixTrace completed.item completed.member with seeded | origin
  · simp [Input.initial, Protocol.SafeHandoff.State.initial] at seeded
  · obtain ⟨admitPrior, admitFinding, admitLater, beforeAdmit, admissionCovered, admissionTrace, admissionAccepted, origin⟩ := origin
    exact ⟨prior, later, before, admitPrior, admitFinding, admitLater, beforeAdmit,
      covered, prefixTrace, accepted, completed.member, completed.selected, rfl, computed,
      admissionCovered, admissionTrace, admissionAccepted, origin⟩

theorem Report.observed_serve_source (input : Input)
    (report : Report input.routing input.configs input.initial input.events) (compliant : report.compliant = true)
    (finding : Finding) (member : finding ∈ report.findings) (id : Nat) (observedInput : Source)
    (observed : Check.WireForwarding.PacketObservation)
    (event : finding.observation.event = .serve id observedInput observed)
    (served : Protocol.SafeHandoff.PacketResult) (seen : finding.result.served = some served) :
    served.ticket.value.source.bytes = observedInput.bytes ∧
      served.ticket.value.source.packet = observedInput.packet ∧ observed.Matches served.outcome := by
  have matched := (report.finding_matches compliant finding member).1
  change PacketMatches finding.observation finding.result at matched
  unfold PacketMatches at matched
  rw [event, seen] at matched
  cases established : finding.result.established with
  | some packet => simp [established] at matched
  | none =>
    have pair : served.ticket.value.source.bytes = observedInput.bytes ∧ observed.Matches served.outcome := by
      simpa only [PacketMatches, established] using matched
    have decoded := served.ticket.value.source.decoded
    rw [pair.1, observedInput.decoded] at decoded
    exact ⟨pair.1, Except.ok.inj decoded.symm, pair.2⟩


def AdmissionPrefix (routing : Routing) (configs : List Config) (initial : ModelState) (findings : List Finding)
    (item : Theory.Outstanding.Item Protocol.SafeHandoff.Ticket) : Prop :=
  ∃ prior finding later before,
    findings = prior ++ finding :: later ∧ Replay.Trace (replay routing configs) initial prior before ∧
    step routing configs before finding.observation = .ok finding.result ∧ AdmissionOrigin before finding item

theorem Report.observed_output_facts (input : Input)
    (report : Report input.routing input.configs input.initial input.events) (compliant : report.compliant = true)
    (finding : Finding) (member : finding ∈ report.findings) (id : Nat) (observedInput : Source)
    (observed : Check.WireForwarding.PacketObservation)
    (event : finding.observation.event = .serve id observedInput observed)
    (served : Protocol.SafeHandoff.PacketResult) (seen : finding.result.served = some served)
    (captured : Check.WireForwarding.WirePacket) (capturedOutput : observed.output = some captured) :
    ∃ (prior later : List Finding) (before : ModelState)
      (emission : Protocol.WireForwarding.Emission served.ticket.value.source.packet),
      report.findings = prior ++ finding :: later ∧
      Replay.Trace (replay input.routing input.configs) input.initial prior before ∧
      AdmissionPrefix input.routing input.configs input.initial prior served.ticket ∧
      served.configuration = before.configurations served.ticket.value.gateway ∧
      served.ticket.value.source.bytes = observedInput.bytes ∧
      Protocol.WireForwarding.step served.configuration.pipeline
        (before.gateways.table served.ticket.value.gateway)
        (TrackedFlow.wireInput served.ticket.value.entry served.ticket.value.direction served.ticket.value.source.packet) =
        .ok served.outcome ∧
      served.outcome.output = some emission ∧ captured.value = Check.WireForwarding.emissionValue emission ∧
      captured.checked.header = served.ticket.value.entry.flow.output served.ticket.value.direction ∧
      captured.checked.packet.datagram.payload = served.ticket.value.source.packet.datagram.payload ∧
      captured.checked.packet.ip.packet.ttl.toNat = served.ticket.value.source.packet.ip.packet.ttl.toNat - 1 ∧
      StatefulACL.Policy.evaluate served.configuration.pipeline.forwardDefault served.configuration.pipeline.forward
        (TrackedFlow.classification (before.gateways.table served.ticket.value.gateway)
          served.ticket.value.entry served.ticket.value.direction)
        (TrackedFlow.destination served.ticket.value.entry served.ticket.value.direction) = .permit ∧
      StatefulACL.Policy.evaluate served.configuration.pipeline.lateDefault served.configuration.pipeline.late
        (TrackedFlow.classification (before.gateways.table served.ticket.value.gateway)
          served.ticket.value.entry served.ticket.value.direction)
        (served.ticket.value.entry.flow.output served.ticket.value.direction) = .permit := by
  obtain ⟨prior, later, before, admitPrior, admitFinding, admitLater, beforeAdmit,
    covered, prefixTrace, accepted, _, _, configurationEq, computed, admissionCovered,
    admissionTrace, admissionAccepted, origin⟩ :=
    report.served_source input finding member id observedInput observed event served seen
  obtain ⟨bytesEq, _, matched⟩ := report.observed_serve_source input compliant finding member id observedInput observed event served seen
  obtain ⟨_, _, _, _, _, _, outputs⟩ := matched
  cases emitted : served.outcome.output with
  | none => simp [capturedOutput, emitted] at outputs
  | some emission =>
    rw [capturedOutput, emitted] at outputs
    have valueEq := Option.some.inj outputs
    have actual : Protocol.SafeHandoff.step before (.serve id) = .ok finding.result := by
      simpa only [replay, step, event, Event.toModel, bind, Except.bind] using accepted
    obtain ⟨safe, raw, coreEq, rawEq⟩ := Protocol.SafeHandoff.step_core before (.serve id) finding.result actual
    have reported : raw.served = some served := by simpa only [← rawEq] using seen
    obtain ⟨_, _, _, target, payload, ttl, forward, late⟩ :=
      Protocol.SafeHandoff.core_serve_forwarded before id raw safe coreEq served reported emission emitted
    have ipEq := congrArg Prod.fst valueEq
    have dataEq := congrArg Prod.snd valueEq
    change captured.checked.packet.ip.packet = emission.decoded.ip.packet at ipEq
    change captured.checked.packet.datagram = emission.decoded.datagram at dataEq
    refine ⟨prior, later, before, emission, covered, prefixTrace,
      ⟨admitPrior, admitFinding, admitLater, beforeAdmit, admissionCovered, admissionTrace, admissionAccepted, origin⟩,
      configurationEq, bytesEq, computed, rfl, valueEq, ?_, ?_, ?_, forward, ?_⟩
    · change captured.checked.packet.header = _
      simp only [UDP.DecodedIPv4.header, ipEq, dataEq]
      exact emission.header.trans target
    · rw [dataEq]
      exact payload
    · rw [ipEq]
      exact ttl
    · simpa only [target] using late


private theorem core_control_cache (before : ModelState) (event : Protocol.StatefulFailover.Event) (raw : Protocol.SafeHandoff.RawResult)
    (selected : ConntrackReplication.Selection)
    (accepted : (do
      let result ← Protocol.StatefulFailover.step before.gateways event
      pure (⟨{ before with gateways := result.state }, none, none, result.packet⟩ : Protocol.SafeHandoff.RawResult)) = .ok raw)
    (cached : raw.state.gateways.cache = some selected)
    (notStage : ∀ zone key, event ≠ .stage zone key) : before.gateways.cache = some selected := by
  cases computed : Protocol.StatefulFailover.step before.gateways event with
  | error error => simp [computed, bind, Except.bind] at accepted
  | ok result =>
    simp only [computed, bind, Except.bind, pure, Except.pure] at accepted
    cases accepted
    rcases Protocol.StatefulFailover.step_cache_origin before.gateways event result selected computed cached with old | stage
    · exact old
    · obtain ⟨zone, key, same, _⟩ := stage
      exact False.elim (notStage zone key same)

def StageOrigin (before : ModelState) (finding : Finding) (selected : ConntrackReplication.Selection) : Prop :=
  ∃ zone key, finding.observation.event = .stage zone key ∧
    finding.result.state.gateways.cache = some selected ∧
    selected.source = before.gateways.primary ∧ selected.sourceEpoch = before.gateways.epoch ∧
    selected.record ∈ before.gateways.primary.records ∧ selected.record.entry.flow.key selected.direction = (zone, key)

private theorem core_cache_origin (before : ModelState) (event : Protocol.SafeHandoff.Event) (raw : Protocol.SafeHandoff.RawResult)
    (accepted : Protocol.SafeHandoff.core before event = .ok raw) (selected : ConntrackReplication.Selection)
    (cached : raw.state.gateways.cache = some selected) :
    before.gateways.cache = some selected ∨ ∃ zone key,
      event = .stage zone key ∧ selected.source = before.gateways.primary ∧
      selected.sourceEpoch = before.gateways.epoch ∧ selected.record ∈ before.gateways.primary.records ∧
      selected.record.entry.flow.key selected.direction = (zone, key) := by
  cases event with
  | establish input =>
    simp only [Protocol.SafeHandoff.core] at accepted
    split at accepted
    · simp [throw, throwThe, bind, Except.bind] at accepted
    · exact .inl (core_control_cache before _ raw selected accepted cached (by intros; simp))
  | stage zone key =>
    simp only [Protocol.SafeHandoff.core] at accepted
    cases computed : Protocol.StatefulFailover.step before.gateways (.stage zone key) with
    | error error => simp [computed, bind, Except.bind] at accepted
    | ok result =>
      simp only [computed, bind, Except.bind] at accepted
      obtain ⟨selection, _, cacheEq, source, epoch, member, attached, _⟩ :=
        Protocol.StatefulFailover.step_stage before.gateways zone key result computed
      simp only [cacheEq] at accepted
      have fields := And.intro source (And.intro epoch (And.intro member attached))
      have finish : ∀ (raw : Protocol.SafeHandoff.RawResult), raw.state.gateways = result.state →
          raw.state.gateways.cache = some selected →
          selected.source = before.gateways.primary ∧ selected.sourceEpoch = before.gateways.epoch ∧
          selected.record ∈ before.gateways.primary.records ∧ selected.record.entry.flow.key selected.direction = (zone, key) := by
        intro raw stateEq selectedEq
        rw [stateEq, cacheEq] at selectedEq
        have eq := Option.some.inj selectedEq
        simpa only [← eq] using fields
      cases binding : before.binding with
      | none =>
        simp only [binding, pure, Except.pure] at accepted
        cases accepted
        exact .inr ⟨zone, key, rfl, finish _ rfl cached⟩
      | some entry =>
        simp only [binding] at accepted
        split at accepted
        · simp [throw] at accepted
        · simp only [pure, Except.pure] at accepted
          cases accepted
          exact .inr ⟨zone, key, rfl, finish _ rfl cached⟩
  | commit timeout =>
    simp only [Protocol.SafeHandoff.core] at accepted
    cases binding : before.binding with
    | none => simp [binding, throw] at accepted
    | some entry =>
      simp only [binding] at accepted
      cases cacheEq : before.gateways.cache with
      | none => simp [cacheEq, throw] at accepted
      | some selection =>
        simp only [cacheEq] at accepted
        split at accepted
        · simp [throw, bind, Except.bind] at accepted
        · exact .inl (by simpa only [cacheEq] using core_control_cache before _ raw selected accepted cached (by intros; simp))
  | handoff selectedLeg gateway =>
    simp only [Protocol.SafeHandoff.core] at accepted
    cases binding : before.binding with
    | none => simp [binding, throw] at accepted
    | some entry =>
      simp only [binding] at accepted
      split at accepted
      · simp [throw, bind, Except.bind] at accepted
      · split at accepted
        · simp [throw, bind, Except.bind] at accepted
        · exact .inl (core_control_cache before _ raw selected accepted cached (by intros; simp))
  | fence gateway =>
    simp only [Protocol.SafeHandoff.core] at accepted
    split at accepted
    · simp [throw, bind, Except.bind] at accepted
    · split at accepted
      · simp [throw, bind, Except.bind] at accepted
      · exact .inl (core_control_cache before _ raw selected accepted cached (by intros; simp))
  | forget => exact .inl (core_control_cache before _ raw selected accepted cached (by intros; simp))
  | install gateway config =>
    simp only [Protocol.SafeHandoff.core, Except.ok.injEq] at accepted
    cases accepted
    exact .inl cached
  | assign direction source =>
    simp only [Protocol.SafeHandoff.core] at accepted
    cases binding : before.binding with
    | none => simp [binding, throw] at accepted
    | some entry =>
      simp only [binding] at accepted
      split at accepted
      · split at accepted
        · simp [throw, bind, Except.bind] at accepted
        · split at accepted
          · simp [throw, bind, Except.bind] at accepted
          · simp only [pure, Except.pure] at accepted
            cases accepted
            exact .inl cached
      · simp [throw] at accepted
  | serve id =>
    obtain ⟨completed, outcome, completedEq, _, binding, unfenced, ready, computed, _⟩ :=
      Protocol.SafeHandoff.core_serve_facts before id raw accepted
    have checked := (TrackedFlow.ready_correct _ _).mpr ready
    simp only [Protocol.SafeHandoff.core, completedEq, Except.mapError, bind, Except.bind, binding,
      ne_eq, not_true_eq_false, ite_false, unfenced, Bool.false_eq_true, checked, Bool.not_true,
      computed, pure, Except.pure] at accepted
    cases accepted
    change (before.gateways.write completed.item.value.gateway outcome.state).cache = some selected at cached
    cases gatewayEq : completed.item.value.gateway <;>
      exact .inl (by simpa only [gatewayEq, Protocol.StatefulFailover.State.write] using cached)


theorem Event.toModel_stage (event : Event) (routing : Routing) (configs : List Config) (before : ModelState)
    (zone : Nat) (key : Header) (selected : event.toModel routing configs before = .ok (.stage zone key)) :
    event = .stage zone key := by
  cases event with
  | establish zone input seen =>
    simp only [Event.toModel] at selected
    cases found : configs.find? (fun config => config.id == (before.configurations .primary).id) with
    | none => simp [found] at selected
    | some config => simp [found, pure, Except.pure] at selected
  | stage selectedZone selectedKey => simpa only [Event.toModel, Except.ok.injEq, Protocol.SafeHandoff.Event.stage.injEq, Event.stage.injEq] using selected
  | assign direction source seen => simp [Event.toModel] at selected
  | commit timeout => simp [Event.toModel] at selected
  | handoff selectedLeg gateway => simp [Event.toModel] at selected
  | fence gateway => simp [Event.toModel] at selected
  | forget => simp [Event.toModel] at selected
  | install gateway config => simp [Event.toModel] at selected
  | serve id input seen => simp [Event.toModel] at selected

theorem step_cache_origin (before : ModelState) (finding : Finding)
    (accepted : step routing configs before finding.observation = .ok finding.result)
    (selected : ConntrackReplication.Selection) (cached : finding.result.state.gateways.cache = some selected) :
    before.gateways.cache = some selected ∨ StageOrigin before finding selected := by
  obtain ⟨event, translated, computed⟩ := step_model routing configs before finding.observation finding.result accepted
  obtain ⟨_, raw, coreEq, rawEq⟩ := Protocol.SafeHandoff.step_core before event finding.result computed
  have cachedRaw : raw.state.gateways.cache = some selected := by simpa only [← rawEq] using cached
  rcases core_cache_origin before event raw coreEq selected cachedRaw with old | current
  · exact .inl old
  · obtain ⟨zone, key, eventEq, source, epoch, member, attached⟩ := current
    rw [eventEq] at translated
    exact .inr ⟨zone, key, Event.toModel_stage _ _ _ _ _ _ translated, cached, source, epoch, member, attached⟩

theorem trace_cache_source (trace : Replay.Trace (replay routing configs) initial findings final)
    (selected : ConntrackReplication.Selection) (cached : final.gateways.cache = some selected) :
    initial.gateways.cache = some selected ∨ ∃ prior finding later before,
      findings = prior ++ finding :: later ∧ Replay.Trace (replay routing configs) initial prior before ∧
      step routing configs before finding.observation = .ok finding.result ∧ StageOrigin before finding selected :=
  trace.origin (fun state selected => state.gateways.cache = some selected) StageOrigin
    (fun before finding selected accepted cached => step_cache_origin before finding accepted selected cached) selected cached

theorem Report.cache_source (input : Input) (report : Report input.routing input.configs input.initial input.events)
    (selected : ConntrackReplication.Selection) (cached : report.final.gateways.cache = some selected) :
    ∃ prior finding later before,
      report.findings = prior ++ finding :: later ∧ Replay.Trace (replay input.routing input.configs) input.initial prior before ∧
      step input.routing input.configs before finding.observation = .ok finding.result ∧ StageOrigin before finding selected := by
  rcases trace_cache_source report.trace selected cached with seed | source
  · simp [Input.initial, Protocol.SafeHandoff.State.initial, Protocol.StatefulFailover.State.initial] at seed
  · exact source

private theorem core_commit_install (before : ModelState) (timeout : Nat) (raw : Protocol.SafeHandoff.RawResult)
    (accepted : Protocol.SafeHandoff.core before (.commit timeout) = .ok raw) :
    ∃ selected installed,
      before.gateways.cache = some selected ∧
      ConntrackReplication.commit before.gateways.standby selected timeout = .ok installed ∧
      installed.selection = selected ∧ raw.state.gateways.standby = installed.state ∧
      raw.state.gateways.standby.records = before.gateways.standby.records ++ [selected.recordForInstall] := by
  simp only [Protocol.SafeHandoff.core] at accepted
  cases binding : before.binding with
  | none => simp [binding, throw] at accepted
  | some entry =>
    simp only [binding] at accepted
    cases cacheEq : before.gateways.cache with
    | none => simp [cacheEq, throw] at accepted
    | some selected =>
      simp only [cacheEq] at accepted
      split at accepted
      · simp [throw, bind, Except.bind] at accepted
      · change (do
          let result ← Protocol.StatefulFailover.step before.gateways (.commit timeout)
          pure (⟨{ before with gateways := result.state }, none, none, result.packet⟩ : Protocol.SafeHandoff.RawResult)) = .ok raw at accepted
        cases computed : Protocol.StatefulFailover.step before.gateways (.commit timeout) with
        | error error => simp [computed, bind, Except.bind] at accepted
        | ok result =>
          simp only [computed, bind, Except.bind, pure, Except.pure] at accepted
          cases accepted
          obtain ⟨actual, installed, cached, committed, _, installedState, records, _⟩ :=
            Protocol.StatefulFailover.step_commit before.gateways timeout result computed
          have selectionEq := Option.some.inj (cacheEq.symm.trans cached)
          subst actual
          have fields := ConntrackReplication.commit_fields _ _ _ _ committed
          exact ⟨selected, installed, rfl, committed, fields.2.1, installedState, records⟩

theorem Report.commit_source (input : Input) (report : Report input.routing input.configs input.initial input.events)
    (finding : Finding) (member : finding ∈ report.findings) (timeout : Nat)
    (event : finding.observation.event = .commit timeout) :
    ∃ commitPrior commitLater beforeCommit selected installed stagePrior stageFinding stageLater beforeStage,
      report.findings = commitPrior ++ finding :: commitLater ∧
      Replay.Trace (replay input.routing input.configs) input.initial commitPrior beforeCommit ∧
      step input.routing input.configs beforeCommit finding.observation = .ok finding.result ∧
      beforeCommit.gateways.cache = some selected ∧
      ConntrackReplication.commit beforeCommit.gateways.standby selected timeout = .ok installed ∧
      installed.selection = selected ∧ finding.result.state.gateways.standby = installed.state ∧
      finding.result.state.gateways.standby.records = beforeCommit.gateways.standby.records ++ [selected.recordForInstall] ∧
      commitPrior = stagePrior ++ stageFinding :: stageLater ∧
      Replay.Trace (replay input.routing input.configs) input.initial stagePrior beforeStage ∧
      step input.routing input.configs beforeStage stageFinding.observation = .ok stageFinding.result ∧
      StageOrigin beforeStage stageFinding selected := by
  obtain ⟨prior, later, before, covered, prefixTrace, accepted, _⟩ := report.trace.prefix finding member
  have actual : Protocol.SafeHandoff.step before (.commit timeout) = .ok finding.result := by
    simpa only [replay, step, event, Event.toModel, bind, Except.bind] using accepted
  obtain ⟨_, raw, coreEq, rawEq⟩ := Protocol.SafeHandoff.step_core before (.commit timeout) finding.result actual
  obtain ⟨selected, installed, cached, committed, selection, installedState, records⟩ := core_commit_install before timeout raw coreEq
  rcases trace_cache_source prefixTrace selected cached with seed | staged
  · simp [Input.initial, Protocol.SafeHandoff.State.initial, Protocol.StatefulFailover.State.initial] at seed
  · obtain ⟨stagePrior, stageFinding, stageLater, beforeStage, stageCovered, stageTrace, stageAccepted, origin⟩ := staged
    exact ⟨prior, later, before, selected, installed, stagePrior, stageFinding, stageLater, beforeStage,
      covered, prefixTrace, accepted, cached, committed, selection,
      by simpa only [← rawEq] using installedState, by simpa only [← rawEq] using records,
      stageCovered, stageTrace, stageAccepted, origin⟩

theorem Report.served_event (report : Report routing configs initial observations) (compliant : report.compliant = true)
    (finding : Finding) (member : finding ∈ report.findings) (served : Protocol.SafeHandoff.PacketResult)
    (seen : finding.result.served = some served) :
    ∃ id source observed, finding.observation.event = .serve id source observed := by
  have matched := (report.finding_matches compliant finding member).1
  unfold PacketMatches at matched
  rw [seen] at matched
  cases event : finding.observation.event with
  | serve id source observed => exact ⟨id, source, observed, rfl⟩
  | establish zone source observed => cases finding.result.established <;> simp_all
  | stage zone key => cases finding.result.established <;> simp_all
  | commit timeout => cases finding.result.established <;> simp_all
  | handoff selectedLeg gateway => cases finding.result.established <;> simp_all
  | fence gateway => cases finding.result.established <;> simp_all
  | forget => cases finding.result.established <;> simp_all
  | install gateway config => cases finding.result.established <;> simp_all
  | assign direction source observed => cases finding.result.established <;> simp_all

theorem Report.every_served_source (input : Input)
    (report : Report input.routing input.configs input.initial input.events) (compliant : report.compliant = true)
    (finding : Finding) (member : finding ∈ report.findings) (served : Protocol.SafeHandoff.PacketResult)
    (seen : finding.result.served = some served) :
    ∃ id source observed prior later before,
      finding.observation.event = .serve id source observed ∧ report.findings = prior ++ finding :: later ∧
      Replay.Trace (replay input.routing input.configs) input.initial prior before ∧
      AdmissionPrefix input.routing input.configs input.initial prior served.ticket ∧
      served.ticket.value.source.bytes = source.bytes ∧ served.ticket.value.source.packet = source.packet ∧
      served.configuration = before.configurations served.ticket.value.gateway ∧ observed.Matches served.outcome := by
  obtain ⟨id, source, observed, event⟩ := report.served_event compliant finding member served seen
  obtain ⟨prior, later, before, admitPrior, admitFinding, admitLater, beforeAdmit,
    covered, prefixTrace, _, _, _, configurationEq, _, admissionCovered,
    admissionTrace, admissionAccepted, origin⟩ := report.served_source input finding member id source observed event served seen
  obtain ⟨bytesEq, packetEq, matched⟩ := report.observed_serve_source input compliant finding member id source observed event served seen
  exact ⟨id, source, observed, prior, later, before, event, covered, prefixTrace,
    ⟨admitPrior, admitFinding, admitLater, beforeAdmit, admissionCovered, admissionTrace, admissionAccepted, origin⟩,
    bytesEq, packetEq, configurationEq, matched⟩
end Netlib.Check.SafeHandoff
