import Netlib.Check.Replay
import Netlib.Import.EthernetIPv4
import Netlib.Import.PacketFields
import Netlib.Protocol.PMTUFacts
import Netlib.Protocol.RelatedICMP

/-! Byte-derived feedback and drained-error UDP send-capacity observations. -/

namespace Netlib.Check.PMTU

open Packet Protocol

abbrev Cache := Protocol.PMTU.State

structure Environment where
  route : Protocol.PMTU.Route
  policy : Protocol.PMTU.Policy
  socket : Header
  positive : 0 < policy.lifetime

structure State where
  cache : Cache
  lastTime : Nat
  deriving Repr, BEq, DecidableEq

def initial : State := ⟨⟨none⟩, 0⟩

structure CheckedError (bytes : List UInt8) where
  envelope : Import.EthernetIPv4.Envelope
  source : Protocol.RelatedICMP.Source
  ethernet : Import.EthernetIPv4.decode bytes = .ok envelope
  decoded : Protocol.RelatedICMP.decode envelope.payload = .ok source

def checkErrorBytes (bytes : List UInt8) : Except String (CheckedError bytes) := do
  match ethernet : Import.EthernetIPv4.decode bytes with
  | .error error => throw error
  | .ok envelope =>
    match decoded : Protocol.RelatedICMP.decode envelope.payload with
    | .error error => throw error
    | .ok source => return ⟨envelope, source, ethernet, decoded⟩

structure ErrorPacket where
  bytes : List UInt8
  checked : CheckedError bytes

def ErrorPacket.feedback (packet : ErrorPacket) : Protocol.PMTU.Feedback :=
  ⟨packet.checked.source.icmp.message.kind, IPv4QuotePrefix.header packet.checked.source.quote,
    packet.checked.source.ip.packet.source⟩

structure ReceiveResult (environment : Environment) where
  packet : ErrorPacket
  before : Cache
  now : Nat
  outcome : Option Protocol.PMTU.Result
  computed : Protocol.PMTU.feedback environment.policy environment.route environment.socket before now
    packet.feedback = outcome

/-- An accepted update is guarded by the complete quoted socket tuple and ICMP kind. -/
theorem receiveMatchingGuard (receive : ReceiveResult environment) (result : Protocol.PMTU.Result)
    (accepted : receive.outcome = some result) :
    receive.packet.feedback.quoted = environment.socket ∧
      ∃ advertised, receive.packet.feedback.kind = .fragmentationNeeded advertised ∧
        result = Protocol.PMTU.update environment.policy environment.route receive.before receive.now advertised :=
  Protocol.PMTU.feedback_accepted _ _ _ _ _ _ _ (receive.computed.trans accepted)

theorem ReceiveResult.nonincrease (receive : ReceiveResult environment) (result : Protocol.PMTU.Result)
    (accepted : receive.outcome = some result) :
    (result.state.current environment.route receive.now).val ≤
      (receive.before.current environment.route receive.now).val := by
  obtain ⟨_, advertised, _, rfl⟩ := receiveMatchingGuard receive result accepted
  exact Protocol.PMTU.update_nonincrease _ _ _ _ _ environment.positive

inductive Event where
  | receive (now : Nat) (packet : ErrorPacket) (mtu : Option Nat)
  | query (now : Nat) (mtu : Nat)
  | send (now payloadLength : Nat) (df : Bool) (observed : Protocol.PMTU.Send)

def Event.now : Event → Nat
  | .receive now .. | .query now .. | .send now .. => now

structure Observation where
  index : Nat
  event : Event
  raw : Lean.Json

structure Result (environment : Environment) where
  state : State
  valid : state.cache.Valid environment.route
  feedback : Option (ReceiveResult environment) := none
  decision : Option Protocol.PMTU.Send := none

private def cacheValid (environment : Environment) (cache : Cache) : Bool :=
  (cache.exception.map fun entry => decide (entry.mtu.val ≤ environment.route.mtu.val)).getD true

private theorem cacheValid_correct (environment : Environment) (cache : Cache) :
    cacheValid environment cache = true ↔ cache.Valid environment.route := by
  cases found : cache.exception <;> simp [cacheValid, Protocol.PMTU.State.Valid, found]

private theorem feedback_valid (environment : Environment) (before : Cache) (now : Nat)
    (message : Protocol.PMTU.Feedback) (valid : before.Valid environment.route) :
    (((Protocol.PMTU.feedback environment.policy environment.route environment.socket before now message).map
      (·.state)).getD before).Valid environment.route := by
  cases computed : Protocol.PMTU.feedback environment.policy environment.route environment.socket before now message with
  | none => simpa using valid
  | some result =>
    obtain ⟨_, advertised, _, rfl⟩ := Protocol.PMTU.feedback_accepted _ _ _ _ _ _ _ computed
    exact Protocol.PMTU.update_valid _ _ _ _ _ valid

def step (environment : Environment) (before : State) (event : Event) : Except String (Result environment) := do
  if checked : cacheValid environment before.cache = true then
    let valid := (cacheValid_correct environment before.cache).mp checked
    if before.lastTime ≤ event.now then
      match event with
      | .receive now packet _ =>
        let outcome := Protocol.PMTU.feedback environment.policy environment.route environment.socket before.cache now packet.feedback
        return ⟨⟨(outcome.map (·.state)).getD before.cache, now⟩,
          feedback_valid environment before.cache now packet.feedback valid,
          some ⟨packet, before.cache, now, outcome, rfl⟩, none⟩
      | .query now _ => return ⟨⟨before.cache, now⟩, valid, none, none⟩
      | .send now payloadLength df _ => return ⟨⟨before.cache, now⟩, valid, none,
          some (Protocol.PMTU.send environment.route before.cache now df payloadLength)⟩
    else throw "PMTU observation times must be monotonic."
  else throw "The PMTU cache exceeds the configured physical route MTU."

theorem initial_valid (environment : Environment) : initial.cache.Valid environment.route :=
  Protocol.PMTU.State.valid_initial _

theorem step_nonincrease (environment : Environment) (before : State) (event : Event)
    (result : Result environment) (accepted : step environment before event = .ok result) :
    (result.state.cache.current environment.route event.now).val ≤
      (before.cache.current environment.route event.now).val := by
  unfold step at accepted
  split at accepted
  · split at accepted
    · cases event with
      | receive now packet observed =>
        cases computed : Protocol.PMTU.feedback environment.policy environment.route environment.socket
            before.cache now packet.feedback with
        | none =>
          simp only [computed, Option.map_none, Option.getD_none, pure, Except.pure,
            Except.ok.injEq] at accepted
          cases accepted
          exact Nat.le_refl _
        | some outcome =>
          simp only [computed, Option.map_some, Option.getD_some, pure, Except.pure,
            Except.ok.injEq] at accepted
          cases accepted
          obtain ⟨_, advertised, _, rfl⟩ := Protocol.PMTU.feedback_accepted _ _ _ _ _ _ _ computed
          exact Protocol.PMTU.update_nonincrease _ _ _ _ _ environment.positive
      | query now observed =>
        simp only [pure, Except.pure, Except.ok.injEq] at accepted
        cases accepted
        exact Nat.le_refl _
      | send now payloadLength df observed =>
        simp only [pure, Except.pure, Except.ok.injEq] at accepted
        cases accepted
        exact Nat.le_refl _
    · cases accepted
  · cases accepted

theorem step_send (environment : Environment) (before : State) (now payloadLength : Nat) (df : Bool)
    (observed : Protocol.PMTU.Send) (result : Result environment)
    (accepted : step environment before (.send now payloadLength df observed) = .ok result) :
    result.state.cache = before.cache ∧
      result.decision = some (Protocol.PMTU.send environment.route before.cache now df payloadLength) := by
  unfold step at accepted
  split at accepted
  · split at accepted
    · simp only [pure, Except.pure, Except.ok.injEq] at accepted
      cases accepted
      exact ⟨rfl, rfl⟩
    · cases accepted
  · cases accepted

def Matches (environment : Environment) (observation : Observation) (result : Result environment) : Prop :=
  match observation.event with
  | .receive now _ mtu => ∀ observed, mtu = some observed →
      observed = (result.state.cache.current environment.route now).val
  | .query now mtu => mtu = (result.state.cache.current environment.route now).val
  | .send _ _ _ observed => result.decision = some observed

def observationMatches (environment : Environment) (observation : Observation) (result : Result environment) : Bool :=
  match observation.event with
  | .receive now _ mtu => (mtu.map (· == (result.state.cache.current environment.route now).val)).getD true
  | .query now mtu => mtu == (result.state.cache.current environment.route now).val
  | .send _ _ _ observed => decide (result.decision = some observed)

theorem matches_correct (environment : Environment) (observation : Observation) (result : Result environment) :
    observationMatches environment observation result = true ↔ Matches environment observation result := by
  cases observation with
  | mk index event raw =>
    cases event with
    | receive now packet mtu => cases mtu <;> simp [observationMatches, Matches]
    | query now mtu => simp [observationMatches, Matches]
    | send now payloadLength df observed => simp [observationMatches, Matches]

def replay (environment : Environment) : Replay.System State Observation (Result environment) where
  step before observation := step environment before observation.event
  state := Result.state
  passed := observationMatches environment
  Matches := Matches environment
  correct := matches_correct environment

abbrev Finding (environment : Environment) := Replay.Finding Observation (Result environment)
abbrev Agreement (environment : Environment) := Replay.Agreement (replay environment)
abbrev Trace (environment : Environment) := Replay.Trace (replay environment)

structure Report (environment : Environment) (start : State) (observations : List Observation)
    extends Replay.Report (replay environment) start observations

def audit (environment : Environment) (start : State) (observations : List Observation) :
    Except String (Report environment start observations) := do
  return ⟨← Replay.audit (replay environment) start observations⟩

def Report.compliant (report : Report environment start observations) : Bool := report.findings.all (·.passed)

theorem Report.compliant_iff (report : Report environment start observations) :
    report.compliant = true ↔ Agreement environment start observations := report.correct

theorem Report.valid (report : Report environment start observations) (valid : start.cache.Valid environment.route) :
    report.final.cache.Valid environment.route ∧
      ∀ finding ∈ report.findings, finding.result.state.cache.Valid environment.route :=
  report.trace.invariant (fun state => state.cache.Valid environment.route)
    (fun _ _ result _ _ => result.valid) valid

theorem Report.bounds (report : Report environment start observations) (valid : start.cache.Valid environment.route)
    (finding : Finding environment) (member : finding ∈ report.findings) (now : Nat) :
    68 ≤ (finding.result.state.cache.current environment.route now).val ∧
      (finding.result.state.cache.current environment.route now).val ≤ environment.route.mtu.val :=
  ⟨Protocol.PMTU.State.current_lower _ _ _,
    Protocol.PMTU.State.current_le_route _ _ ((report.valid valid).2 finding member) _⟩

theorem Report.nonincrease (report : Report environment start observations)
    (finding : Finding environment) (member : finding ∈ report.findings) :
    ∃ before, step environment before finding.observation.event = .ok finding.result ∧
      (finding.result.state.cache.current environment.route finding.observation.event.now).val ≤
        (before.cache.current environment.route finding.observation.event.now).val := by
  obtain ⟨before, computed⟩ := report.trace.steps finding member
  exact ⟨before, computed, step_nonincrease _ _ _ _ computed⟩

theorem Report.observed_send (report : Report environment start observations)
    (compliant : report.compliant = true) (finding : Finding environment) (member : finding ∈ report.findings)
    (now payloadLength : Nat) (df : Bool) (observed : Protocol.PMTU.Send)
    (event : finding.observation.event = .send now payloadLength df observed) :
    ∃ before, step environment before finding.observation.event = .ok finding.result ∧
      finding.result.state.cache = before.cache ∧
      observed = Protocol.PMTU.send environment.route before.cache now df payloadLength := by
  obtain ⟨before, computed⟩ := report.trace.steps finding member
  have selected := computed
  change step environment before finding.observation.event = .ok finding.result at selected
  rw [event] at selected
  obtain ⟨cache, decision⟩ := step_send _ _ _ _ _ _ _ selected
  have matched := Replay.Report.finding_matches report.toReport compliant finding member
  change Matches environment finding.observation finding.result at matched
  simp only [Matches, event] at matched
  exact ⟨before, computed, cache, (Option.some.inj (matched.symm.trans decision))⟩

structure Input where
  environment : Environment
  events : List Observation

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def mtu (json : Lean.Json) : Except String IPv4Fragmentation.MTU := do
  let value ← json.getNat?
  if bounds : 68 ≤ value ∧ value ≤ 65535 then return ⟨value, by omega⟩
  else throw "An IPv4 MTU must be between 68 and 65535."

private def observedMTU (json : Lean.Json) : Except String (Option Nat) :=
  match json with
  | .null => .ok none
  | value => some <$> value.getNat?

private def errorPacket (json : Lean.Json) : Except String ErrorPacket := do
  let bytes ← Import.EAPOL.bytesFromHex (← json.getStr?)
  return ⟨bytes, ← checkErrorBytes bytes⟩

private def sendDecision (json : Lean.Json) : Except String Protocol.PMTU.Send := do
  match ← json.getStr? with
  | "accepted" => return .accepted
  | "messageSize" => return .messageSize
  | "invalidLength" => return .invalidLength
  | value => throw s!"Unsupported UDP send observation: {value}."

def Input.fromJson (json : Lean.Json) : Except String Input := do
  Import.PacketFields.fields json ["schema", "route", "policy", "socket", "events"]
  require ((← (← json.getObjVal? "schema").getNat?) == 1) "Unsupported host PMTU schema."
  let route ← json.getObjVal? "route"
  Import.PacketFields.fields route ["mtu", "locked"]
  let route : Protocol.PMTU.Route := ⟨← mtu (← route.getObjVal? "mtu"), ← (← route.getObjVal? "locked").getBool?⟩
  let policy ← json.getObjVal? "policy"
  Import.PacketFields.fields policy ["minimum", "lifetime"]
  let minimum ← mtu (← policy.getObjVal? "minimum")
  let lifetime ← (← policy.getObjVal? "lifetime").getNat?
  if positive : 0 < lifetime then
    let policy : Protocol.PMTU.Policy := ⟨minimum, lifetime⟩
    let socket ← Import.PacketFields.header (← json.getObjVal? "socket")
    require (socket.protocol == Packet.Protocol.udp) "The selected connected socket must use UDP."
    let environment : Environment := ⟨route, policy, socket, positive⟩
    let values ← (← json.getObjVal? "events").getArr?
    let mut events := []
    for index in [:values.size] do
      let value := values[index]!
      let kind ← (← value.getObjVal? "type").getStr?
      let now ← (← value.getObjVal? "at").getNat?
      let event ← match kind with
        | "receive" => do
          Import.PacketFields.fields value ["type", "at", "raw", "mtu"]
          pure (.receive now (← errorPacket (← value.getObjVal? "raw")) (← observedMTU (← value.getObjVal? "mtu")))
        | "query" => do
          Import.PacketFields.fields value ["type", "at", "mtu"]
          pure (.query now (← (← value.getObjVal? "mtu").getNat?))
        | "send" => do
          Import.PacketFields.fields value ["type", "at", "payloadLength", "df", "errorsDrained", "observed"]
          require (← (← value.getObjVal? "errorsDrained").getBool?)
            "Send-capacity observations require pending socket errors to have been drained."
          pure (.send now (← (← value.getObjVal? "payloadLength").getNat?)
            (← (← value.getObjVal? "df").getBool?) (← sendDecision (← value.getObjVal? "observed")))
        | _ => throw s!"Unsupported host PMTU event: {kind}."
      events := events ++ [⟨index, event, value⟩]
    require (!events.isEmpty) "Supply now least one host PMTU observation."
    return ⟨environment, events⟩
  else throw "The selected PMTU exception lifetime must be positive."

def Input.parse (text : String) : Except String Input := do Input.fromJson (← Import.Json.parse text)

def Input.check (input : Input) : Except String (Report input.environment initial input.events) :=
  audit input.environment initial input.events

private def dispositionText : Protocol.PMTU.Disposition → String
  | .locked => "locked" | .increase => "increase" | .unchanged => "unchanged" | .updated => "updated"

private def sendText : Protocol.PMTU.Send → String
  | .accepted => "accepted" | .messageSize => "messageSize" | .invalidLength => "invalidLength"

private def kindJson : ICMP.Kind → Lean.Json
  | .timeExceeded => Lean.Json.mkObj [("type", Lean.toJson (11 : Nat)), ("code", Lean.toJson (0 : Nat))]
  | .fragmentationNeeded value => Lean.Json.mkObj [("type", Lean.toJson (3 : Nat)),
      ("code", Lean.toJson (4 : Nat)), ("mtu", Lean.toJson value.val)]

private def cacheJson (environment : Environment) (state : State) : Lean.Json := Lean.Json.mkObj [
  ("currentMTU", Lean.toJson (state.cache.current environment.route state.lastTime).val),
  ("lastTime", Lean.toJson state.lastTime),
  ("exception", ((state.cache.age state.lastTime).exception.map fun entry => Lean.Json.mkObj [
    ("mtu", Lean.toJson entry.mtu.val), ("locked", Lean.toJson entry.locked),
    ("expires", Lean.toJson entry.expires)]).getD .null)]

private def outcomeJson (environment : Environment) (result : Result environment) : Lean.Json :=
  let common := [("mtu", Lean.toJson (result.state.cache.current environment.route result.state.lastTime).val)]
  match result.feedback, result.decision with
  | some received, _ => Lean.Json.mkObj (common ++ [
      ("type", Lean.toJson "receive"), ("kind", kindJson received.packet.feedback.kind),
      ("quoted", Import.PacketFields.headerJson received.packet.feedback.quoted),
      ("reporter", Lean.toJson (Import.PacketFields.addressText received.packet.feedback.reporter)),
      ("acceptedFeedback", Lean.toJson received.outcome.isSome),
      ("disposition", (received.outcome.map (fun outcome => Lean.toJson (dispositionText outcome.disposition))).getD .null)])
  | _, some decision => Lean.Json.mkObj (common ++ [
      ("type", Lean.toJson "send"), ("decision", Lean.toJson (sendText decision))])
  | _, _ => Lean.Json.mkObj (common ++ [("type", Lean.toJson "query")])

def Report.assumptions : List String := [
  "The selected connected UDP socket, physical route MTU, lock and PMTU policy remain stable; the initial exception cache is empty.",
  "Observation times use one monotonic clock; the selected exception lifetime is positive and clock wrap is excluded.",
  "Raw input is complete untagged Ethernet without FCS or checksum-offload intermediates; outer IPv4 and ICMP checksums are verified.",
  "Quoted checksums, flags and declared lengths remain untrusted; updates match the five-field quoted socket tuple and Fragmentation Needed kind.",
  "The ICMP reporter address is unauthenticated, so a forged matching quote can reduce the cached PMTU.",
  "Each send-capacity observation requires the producer to have drained pending socket errors; this is an input premise, not an error-queue protocol theorem.",
  "UDP uses 20-byte IPv4 and 8-byte UDP headers; the decision describes payload length and DF capacity after error draining.",
  "Allocation succeeds; route replacement, concurrency and additional encapsulation are outside this scope.",
  "MTU and send observations are compared with computed state and never replace it; expiry uses the abstract monotonic clock.",
  "These proofs concern the Lean model and supplied observations; native refinement and physical expiry timing remain separate claims."]

def Report.renderJson (report : Report environment start observations) : Lean.Json := Lean.Json.mkObj [
  ("compliant", Lean.toJson report.compliant), ("scope", Lean.toJson "udp-host-pmtu-feedback"),
  ("assumptions", Lean.toJson Report.assumptions), ("eventCount", Lean.toJson observations.length),
  ("final", cacheJson environment report.final),
  ("findings", Lean.toJson (report.findings.map fun finding => Lean.Json.mkObj [
    ("source", Lean.toJson s!"/events/{finding.observation.index}"), ("matched", Lean.toJson finding.passed),
    ("expected", outcomeJson environment finding.result), ("observed", finding.observation.raw),
    ("expectedState", cacheJson environment finding.result.state)]))]

def Report.render (report : Report environment start observations) : String :=
  (if report.compliant then "HOST PMTU OBSERVATIONS MATCH\n" else "HOST PMTU OBSERVATIONS MISMATCH\n") ++ report.renderJson.pretty

end Netlib.Check.PMTU
