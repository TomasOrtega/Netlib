import Netlib.Check.ReassemblyForwarding
import Netlib.Import.NftablesICMPControl
import Netlib.Protocol.IPv4ReassemblyTimeout

/-!
# Expiry controls alongside ingress replay

Expiry and forwarding read the same preceding state. Only forwarding supplies the next state.
Observed errors constrain emissions and never replace queue or conntrack state.
-/

namespace Netlib.Check.ReassemblyTimeout

open Packet Protocol

namespace Core
export Netlib.Check.ReassemblyForwarding (State Environment Event Observation Result Matches
  passed passed_correct step step_queue_valid step_queue_layout)
end Core

namespace Timeout
export Netlib.Protocol.IPv4ReassemblyTimeout (Context Result Finding Emission Disposition
  expire expire_fields expire_output_facts)
end Timeout

structure InputRoute where
  destination : Address
  isLocal : Bool

structure ReturnRoute where
  destination : Address
  path : ICMPForwarding.ReturnPath

structure Context where
  id : String
  inputRoutes : List InputRoute
  returns : List ReturnRoute
  output : Import.NftablesICMPControl.Snapshot
  late : Import.NftablesStateful.Snapshot
  broadcasts : List Address

def Context.model (context : Context) (userBase : Nat) : Timeout.Context where
  inputRouteLocal packet := (context.inputRoutes.find? (·.destination == packet.destination)).map (·.isLocal)
  requiresLocal := fun _ => true
  returnPath packet := (context.returns.find? (·.destination == packet.source)).map (·.path)
  zone queue := if userBase ≤ queue.key.domain.user ∧ queue.key.domain.user - userBase < 65536 then
    queue.key.domain.user - userBase else 65536
  broadcasts := context.broadcasts
  output := context.output.compile .reassemblyTimeout
  outputDefault := context.output.policyDefault
  late := context.late.compile
  lateDefault := context.late.policy

structure Identification where
  key : IPv4Reassembly.Key
  value : InternetChecksum.Word

structure Frame where
  bytes : List UInt8
  envelope : Import.EthernetIPv4.Envelope
  ip : IPv4.Decoded
  icmp : ICMP.Decoded
  quote : IPv4QuotePrefix.Decoded
  ethernet : Import.EthernetIPv4.decode bytes = .ok envelope
  network : IPv4.decode envelope.payload = .ok ip
  protocol : ip.packet.protocol = Packet.Protocol.icmp
  transport : ICMP.decode ip.packet.payload = .ok icmp
  quotation : IPv4QuotePrefix.decode icmp.message.quote = .ok quote

def frame (bytes : List UInt8) : Except String Frame := do
  match ethernet : Import.EthernetIPv4.decode bytes with
  | .error error => throw error
  | .ok envelope =>
    match network : IPv4.decode envelope.payload with
    | .error error => throw error
    | .ok ip =>
      if protocol : ip.packet.protocol = Packet.Protocol.icmp then
        match transport : ICMP.decode ip.packet.payload with
        | .error error => throw error
        | .ok icmp =>
          match quotation : IPv4QuotePrefix.decode icmp.message.quote with
          | .error error => throw error
          | .ok quote => return ⟨bytes, envelope, ip, icmp, quote, ethernet, network, protocol, transport, quotation⟩
      else throw "Require an outer IPv4 ICMP packet."

abbrev Value := IPv4.Packet × ICMP.Kind × List UInt8

def Frame.value (frame : Frame) : Value :=
  ({ frame.ip.packet with payload := [] }, frame.icmp.message.kind, frame.icmp.message.quote)

def emissionValue (emission : Timeout.Emission queue) : Value :=
  ({ emission.packet with payload := [] }, emission.message.kind, emission.message.quote)

structure Observation where
  base : Core.Observation
  context : Context
  identifications : List Identification
  observed : List Frame

def Observation.identification (observation : Observation) (queue : IPv4Reassembly.Queue) : InternetChecksum.Word :=
  ((observation.identifications.find? (fun entry => decide (entry.key = queue.key))).map (·.value)).getD 0

def eventTime : Core.Event → Nat
  | .fragment now .. | .wait now .. | .erase now .. => now

def values (result : Timeout.Result) : List Value :=
  result.findings.filterMap fun finding => finding.control.output.map emissionValue

def sentKeys (result : Timeout.Result) : List IPv4Reassembly.Key :=
  (result.findings.filter (·.control.output.isSome)).map (·.queue.key)

def unsupported (finding : Timeout.Finding) : Bool :=
  match finding.control.disposition with
  | .unsupportedFirst | .unsupportedZone | .unsupportedAssociation => true
  | _ => false

structure Result where
  core : Core.Result
  expiration : Timeout.Result

def Result.state (result : Result) : Core.State := result.core.state

def step (environment : Core.Environment) (before : Core.State) (observation : Observation) : Except String Result := do
  let expiration ← (Timeout.expire (observation.context.model environment.userBase) before.conntrack before.fragments
    (eventTime observation.base.event) observation.identification).mapError (·.describe)
  if expiration.findings.any unsupported then throw "The expired queue needs unsupported first-fragment, zone, or related-association semantics."
  if ¬(observation.identifications.map (·.key)).Perm (sentKeys expiration) then
    throw "Supply exactly one identification binding for each computed timeout emission."
  let core ← Core.step environment before observation.base.event
  return ⟨core, expiration⟩

def Matches (observation : Observation) (result : Result) : Prop :=
  Core.Matches observation.base result.core ∧ (observation.observed.map Frame.value).Perm (values result.expiration)

def passed (observation : Observation) (result : Result) : Bool :=
  Core.passed observation.base result.core && decide ((observation.observed.map Frame.value).Perm (values result.expiration))

theorem passed_correct (observation : Observation) (result : Result) : passed observation result = true ↔ Matches observation result := by
  simp [passed, Matches, Core.passed_correct]

def replay (environment : Core.Environment) : Replay.System Core.State Observation Result where
  step := step environment
  state := Result.state
  passed := passed
  Matches := Matches
  correct := passed_correct

abbrev Finding := Replay.Finding Observation Result
abbrev Agreement (environment : Core.Environment) := Replay.Agreement (replay environment)
abbrev Report (environment : Core.Environment) (initial : Core.State) (observations : List Observation) :=
  Replay.Report (replay environment) initial observations

def audit (environment : Core.Environment) (initial : Core.State) (observations : List Observation) :
    Except String (Report environment initial observations) := Replay.audit (replay environment) initial observations

def Report.compliant (report : Report environment initial observations) : Bool := report.findings.all (·.passed)

theorem Report.compliant_iff (report : Report environment initial observations) :
    report.compliant = true ↔ Agreement environment initial observations := report.correct

theorem Report.finding_matches (report : Report environment initial observations) (compliant : report.compliant = true)
    (finding : Finding) (member : finding ∈ report.findings) : Matches finding.observation finding.result :=
  Replay.Report.finding_matches report compliant finding member

theorem step_fields (environment : Core.Environment) (before : Core.State) (observation : Observation) (result : Result)
    (computed : step environment before observation = .ok result) :
    Timeout.expire (observation.context.model environment.userBase) before.conntrack before.fragments
      (eventTime observation.base.event) observation.identification = .ok result.expiration ∧
      Core.step environment before observation.base.event = .ok result.core := by
  unfold step at computed
  cases expired : Timeout.expire (observation.context.model environment.userBase) before.conntrack before.fragments
      (eventTime observation.base.event) observation.identification with
  | error error => simp [expired, Except.mapError, bind, Except.bind] at computed
  | ok expiration =>
    simp only [expired, Except.mapError, bind, Except.bind] at computed
    split at computed
    · simp [throw] at computed
    · split at computed
      · simp [throw] at computed
      · cases core : Core.step environment before observation.base.event with
        | error error => simp [core] at computed
        | ok actual =>
          simp only [core, pure, Except.pure] at computed
          cases computed
          exact ⟨rfl, rfl⟩

theorem Report.valid (report : Report environment initial observations) (valid : initial.conntrack.Valid) :
    report.final.conntrack.Valid ∧ ∀ finding ∈ report.findings, finding.result.state.conntrack.Valid :=
  report.trace.invariant (fun state => state.conntrack.Valid) (fun _ _ result _ _ => result.core.valid) valid

theorem Report.queue_valid (report : Report environment initial observations) (valid : initial.fragments.Valid) :
    report.final.fragments.Valid ∧ ∀ finding ∈ report.findings, finding.result.state.fragments.Valid :=
  report.trace.invariant (fun state => state.fragments.Valid)
    (fun before observation result valid computed => Core.step_queue_valid environment before observation.base.event result.core valid
      (step_fields _ _ _ _ computed).2) valid

theorem Report.queue_layout (report : Report environment initial observations) (valid : initial.fragments.LayoutValid) :
    report.final.fragments.LayoutValid ∧ ∀ finding ∈ report.findings, finding.result.state.fragments.LayoutValid :=
  report.trace.invariant (fun state => state.fragments.LayoutValid)
    (fun before observation result valid computed => Core.step_queue_layout environment before observation.base.event result.core valid
      (step_fields _ _ _ _ computed).2) valid

theorem Frame.length_eq (frame : Frame) (emission : Timeout.Emission queue)
    (same : frame.value = emissionValue emission) : frame.ip.packet.wireLength = emission.packet.wireLength := by
  have quote := congrArg (fun value : Value => value.2.2) same
  have quoteLength := congrArg List.length quote
  have bodyLength := congrArg List.length (ICMP.decode_fields _ _ frame.transport).2
  simp only [ICMP.bytes_length] at bodyLength
  change frame.ip.packet.payload.length + 20 = (ICMP.encode emission.message).length + 20
  rw [ICMP.encode, ICMP.bytes_length]
  change frame.icmp.message.quote.length = emission.message.quote.length at quoteLength
  omega

theorem Report.observed_output_facts (report : Report environment initial observations)
    (compliant : report.compliant = true) (finding : Finding) (member : finding ∈ report.findings)
    (output : Frame) (observed : output ∈ finding.observation.observed) :
    ∃ (before : Core.State) (selected : Timeout.Finding) (emission : Timeout.Emission selected.queue),
      step environment before finding.observation = .ok finding.result ∧
      Core.step environment before finding.observation.base.event = .ok finding.result.core ∧
      Timeout.expire (finding.observation.context.model environment.userBase) before.conntrack before.fragments
        (eventTime finding.observation.base.event) finding.observation.identification = .ok finding.result.expiration ∧
      selected ∈ finding.result.expiration.findings ∧ selected.control.output = some emission ∧
      output.value = emissionValue emission ∧ selected.queue ∈ before.fragments.queues ∧
      selected.queue ∉ finding.result.expiration.state.queues ∧
      Netlib.Protocol.IPv4ReassemblyTimeout.SentFacts (finding.observation.context.model environment.userBase)
        before.conntrack selected.queue (eventTime finding.observation.base.event) emission ∧
      emission.source.piece ∈ selected.queue.pieces ∧ emission.source.piece.start = 0 ∧
      finding.result.expiration.conntrack = before.conntrack ∧
      output.icmp.message.quote =
        (IPv4Fragment.headerBytes emission.source.piece.fragment.packet emission.source.piece.fragment.checksum ++
          emission.source.piece.data).take emission.length ∧
      output.ip.packet.wireLength ≤ emission.path.mtu.val ∧ output.ip.packet.wireLength ≤ 576 ∧
      finding.observation.context.output.evaluate .reassemblyTimeout .invalid emission.header = .permit := by
  obtain ⟨before, computed⟩ := report.trace.steps finding member
  obtain ⟨expired, core⟩ := step_fields environment before finding.observation finding.result computed
  have permutation := (report.finding_matches compliant finding member).2
  have expected : output.value ∈ values finding.result.expiration :=
    permutation.subset (List.mem_map.mpr ⟨output, observed, rfl⟩)
  obtain ⟨selected, selectedMember, mapped⟩ := List.mem_filterMap.mp expected
  cases emitted : selected.control.output with
  | none => simp [emitted] at mapped
  | some emission =>
    simp only [emitted, Option.map_some, Option.some.injEq] at mapped
    have same : output.value = emissionValue emission := mapped.symm
    obtain ⟨belongs, removed, facts, piece, offset, unchanged⟩ :=
      Timeout.expire_output_facts _ _ _ _ _ _ expired selected selectedMember emission emitted
    have quote := congrArg (fun value : Value => value.2.2) same
    have quotedPrefix : output.icmp.message.quote =
        (IPv4Fragment.headerBytes emission.source.piece.fragment.packet emission.source.piece.fragment.checksum ++
          emission.source.piece.data).take emission.length := quote.trans emission.quote_prefix
    have fits := emission.fits
    rw [← output.length_eq emission same] at fits
    have outputPermit := facts.outputPermit
    change StatefulACL.Policy.evaluate finding.observation.context.output.policyDefault
      (finding.observation.context.output.compile .reassemblyTimeout) .invalid emission.header = .permit at outputPermit
    rw [Import.NftablesICMPControl.Snapshot.compile_evaluate] at outputPermit
    exact ⟨before, selected, emission, computed, core, expired, selectedMember, emitted, same,
      belongs, removed, facts, piece, offset, unchanged, quotedPrefix, fits.1, fits.2, outputPermit⟩

structure Input where
  forwarding : Check.ReassemblyForwarding.Input
  contexts : List Context
  events : List Observation

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def address (json : Lean.Json) : Except String Address := do Import.IPv4.parseAddress (← json.getStr?)

private def word (json : Lean.Json) : Except String InternetChecksum.Word := do
  let value ← json.getNat?
  if bounded : value < 65536 then return ⟨value, bounded⟩
  else throw "An IPv4 identification must fit in 16 bits."

def Context.fromJson (json : Lean.Json) : Except String Context := do
  Import.PacketFields.fields json ["id", "inputRoutes", "returns", "output", "late", "broadcasts"]
  let id ← (← json.getObjVal? "id").getStr?
  require (!id.isEmpty) "A timeout context ID must not be empty."
  let inputs ← (← json.getObjVal? "inputRoutes").getArr?
  let mut inputRoutes : List InputRoute := []
  for value in inputs do
    Import.PacketFields.fields value ["destination", "local"]
    let destination ← address (← value.getObjVal? "destination")
    require (!(inputRoutes.any (·.destination == destination))) "Input-route destination bindings must be unique."
    inputRoutes := inputRoutes ++ [⟨destination, ← (← value.getObjVal? "local").getBool?⟩]
  let routes ← (← json.getObjVal? "returns").getArr?
  let mut returns : List ReturnRoute := []
  for value in routes do
    Import.PacketFields.fields value ["destination", "nextHop", "source", "mtu", "ttl"]
    let destination ← address (← value.getObjVal? "destination")
    let nextHop ← (← value.getObjVal? "nextHop").getStr?
    require (!nextHop.isEmpty) "A timeout return path needs a next-hop label."
    require (!(returns.any (·.destination == destination))) "Return-route destination bindings must be unique."
    let source ← address (← value.getObjVal? "source")
    let size ← (← value.getObjVal? "mtu").getNat?
    let ttl ← (← value.getObjVal? "ttl").getNat?
    if bounded : 68 ≤ size ∧ size < 65536 then
      require (0 < ttl && ttl < 256) "A timeout output TTL must be between one and 255."
      returns := returns ++ [⟨destination, ⟨nextHop, source, ⟨size, bounded⟩, UInt8.ofNat ttl⟩⟩]
    else throw "A timeout return MTU must be between 68 and 65535."
  let output ← Import.NftablesICMPControl.Snapshot.fromJson (← json.getObjVal? "output")
  let late ← Import.NftablesStateful.Snapshot.fromJsonFor (← json.getObjVal? "late") ["postrouting"]
  require (late.priority == 200) "The timeout late chain must use postrouting priority 200."
  let broadcasts ← (← (← json.getObjVal? "broadcasts").getArr?).toList.mapM address
  return ⟨id, inputRoutes, returns, output, late, broadcasts⟩

private def identification (userBase : Nat) (json : Lean.Json) : Except String Identification := do
  Import.PacketFields.fields json ["key", "identification"]
  let key ← json.getObjVal? "key"
  Import.PacketFields.fields key ["zone", "vif", "source", "destination", "protocol", "identification"]
  let zone ← (← key.getObjVal? "zone").getNat?
  let vif ← (← key.getObjVal? "vif").getNat?
  require (zone < 65536 && vif < 4294967296) "A queue allocation key needs a 16-bit zone and 32-bit L3 master."
  let protocol ← (← key.getObjVal? "protocol").getNat?
  if bounded : protocol < 256 then
    let key : IPv4Reassembly.Key := ⟨⟨userBase + zone, vif⟩, ← address (← key.getObjVal? "source"),
      ← address (← key.getObjVal? "destination"), ⟨protocol, bounded⟩, ← word (← key.getObjVal? "identification")⟩
    return ⟨key, ← word (← json.getObjVal? "identification")⟩
  else throw "A queue protocol must fit in eight bits."

def Input.fromJson (json : Lean.Json) : Except String Input := do
  Import.PacketFields.fields json ["schema", "forwarding", "contexts", "controls"]
  require ((← (← json.getObjVal? "schema").getNat?) == 1) "Use timeout replay schema 1."
  let forwarding ← Check.ReassemblyForwarding.Input.fromJson (← json.getObjVal? "forwarding")
  let values ← (← json.getObjVal? "contexts").getArr?
  let mut contexts : List Context := []
  for value in values do
    let context ← Context.fromJson value
    require (!(contexts.any (·.id == context.id))) "Timeout context IDs must be unique."
    contexts := contexts ++ [context]
  let controls ← (← json.getObjVal? "controls").getArr?
  require (controls.size == forwarding.events.length) "Supply one timeout control binding for every forwarding event."
  let mut events := []
  for (base, index) in forwarding.events.zipIdx do
    let value := controls[index]!
    Import.PacketFields.fields value ["event", "context", "identifications", "observed"]
    require ((← (← value.getObjVal? "event").getNat?) == index) "Timeout controls must use consecutive forwarding-event indices."
    let id ← (← value.getObjVal? "context").getStr?
    let some context := contexts.find? (·.id == id) | throw s!"Unknown timeout context: {id}."
    let entries ← (← value.getObjVal? "identifications").getArr?
    let mut identifications : List Identification := []
    for entry in entries do
      let parsed ← identification forwarding.environment.userBase entry
      require (!(identifications.any (fun previous => decide (previous.key = parsed.key)))) "Identification allocation keys must be unique."
      identifications := identifications ++ [parsed]
    let values ← (← value.getObjVal? "observed").getArr?
    let observed ← values.toList.mapM fun value => do frame (← Import.EAPOL.bytesFromHex (← value.getStr?))
    events := events ++ [⟨base, context, identifications, observed⟩]
  return ⟨forwarding, contexts, events⟩

def Input.parse (text : String) : Except String Input := do Input.fromJson (← Import.Json.parse text)

def Input.check (input : Input) : Except String (Report input.forwarding.environment input.forwarding.initial input.events) :=
  audit input.forwarding.environment input.forwarding.initial input.events

private def dispositionText : Timeout.Disposition → String
  | .notExpired => "notExpired" | .noFirst => "noFirst" | .unsupportedFirst => "unsupportedFirst"
  | .noInputRoute => "noInputRoute" | .suppressed => "suppressed" | .noReturnRoute => "noReturnRoute"
  | .unsupportedZone => "unsupportedZone" | .unsupportedAssociation => "unsupportedAssociation"
  | .outputDrop => "outputDrop" | .lateDrop => "lateDrop" | .sent => "sent"

private def findingJson (finding : Timeout.Finding) : Lean.Json := Lean.Json.mkObj [
  ("user", Lean.toJson finding.queue.key.domain.user), ("vif", Lean.toJson finding.queue.key.domain.vif),
  ("source", Lean.toJson finding.queue.key.source.val), ("destination", Lean.toJson finding.queue.key.destination.val),
  ("identification", Lean.toJson finding.queue.key.identification.val), ("expires", Lean.toJson finding.queue.expires),
  ("disposition", .str (dispositionText finding.control.disposition)),
  ("classification", if finding.control.classification.isSome then .str "invalid" else .null),
  ("output", (finding.control.output.map (fun emission => Lean.Json.mkObj [
    ("rawIPv4", Lean.toJson (Import.EAPOL.bytesToHex emission.bytes)),
    ("quoteHex", Lean.toJson (Import.EAPOL.bytesToHex emission.message.quote)),
    ("wireLength", Lean.toJson emission.packet.wireLength), ("returnMTU", Lean.toJson emission.path.mtu.val)])).getD .null)]

def Report.assumptions : List String := Netlib.Check.ReassemblyForwarding.Report.assumptions ++ [
  "Timeout and forwarding processing read the same preceding queue and conntrack state; forwarding alone determines the next state.",
  "Every event binds one captured output-policy context and consumes its complete observed timeout-error family.",
  "Other declared output and postrouting hooks only observe; the selected chains supply the modeled control verdicts.",
  "Input-route locality and return-route/source bindings are supplied premises tied to the stored first fragment before destination NAT.",
  "Missing route bindings mean no selected route; the selected conntrack-input profile requires a local original destination.",
  "Each sent queue has one explicit allocator identification; allocator choice does not determine error existence or update state.",
  "The selected local-output path requires a reverse-quote lookup miss and evaluates output and late filtering as INVALID.",
  "Ingress nftables installs a BOTH-direction zone template before defragmentation; stored heads retain it through ICMP attachment and LOCAL_OUT.",
  "Directional zones, mark-derived templates, and output-zone overrides require separate semantics.",
  "Comparison validates outer IPv4 and ICMP checksums, ignores their zero representations and Ethernet adjacency, and preserves every quoted byte.",
  "Event times and queue timeouts share an abstract monotonic unit; native replay uses nanoseconds.",
  "Complete capture, policy-installation timing, route/source binding, rate-limit admission, and successful allocation remain external premises."]

def Report.renderJson (report : Report environment initial observations) : Lean.Json := Lean.Json.mkObj [
  ("compliant", Lean.toJson report.compliant), ("scope", .str "ipv4-reassembly-timeout-controls"),
  ("assumptions", Lean.toJson Report.assumptions), ("eventCount", Lean.toJson observations.length),
  ("final", Check.ConntrackLifecycle.stateJson report.final.conntrack),
  ("pendingQueues", Lean.toJson report.final.fragments.queues.length),
  ("findings", Lean.toJson (report.findings.map fun finding => Lean.Json.mkObj [
    ("source", .str s!"/controls/{finding.observation.base.index}"), ("matched", Lean.toJson finding.passed),
    ("context", .str finding.observation.context.id),
    ("expired", Lean.toJson (finding.result.expiration.findings.map findingJson)),
    ("expectedState", Check.ConntrackLifecycle.stateJson finding.result.state.conntrack),
    ("pendingQueues", Lean.toJson finding.result.state.fragments.queues.length)]))]

def Report.render (report : Report environment initial observations) : String :=
  (if report.compliant then "REASSEMBLY TIMEOUT OBSERVATIONS MATCH\n" else "REASSEMBLY TIMEOUT OBSERVATIONS MISMATCH\n") ++
    report.renderJson.pretty

end Netlib.Check.ReassemblyTimeout
