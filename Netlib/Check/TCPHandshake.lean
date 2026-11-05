import Netlib.Protocol.TCP.HandshakeExchange
import Netlib.Check.TCPEndpoint

/-!
# Checked ordinary TCP startup replay

The input supplies local configuration and events, without established seeds.
Each successful receipt must match an earlier model output and its selected byte path.
Unsupported processing stops the replay before the next transport decode.
-/

namespace Netlib.Check.TCPHandshake

namespace H
export Netlib.Protocol.TCP.Handshake
  (Local Socket Input SynSent SynReceived ActiveEstablished Failure Reject Unsupported)
end H
namespace X
export Netlib.Protocol.TCP.HandshakeExchange (DeliverySpec Delivery Input Complete)
end X

inductive Path where
  | direct | rewrite
  deriving Repr, BEq, DecidableEq

inductive Event where
  | activeOpen (remote : H.Socket) (policy : Bool)
  | listenSyn (bytes : List UInt8) (path : Path) (policy : Bool)
  | synSentSynAck (bytes : List UInt8) (path : Path) (policy : Bool)
  | synReceivedAck (bytes : List UInt8) (path : Path)

structure Input where
  active : H.Local
  passive : H.Local
  events : List Event

structure Opened (config : H.Local) where
  remote : H.Socket
  policy : Bool
  index : Nat
  pending : H.SynSent
  computed : Protocol.TCP.Handshake.activeOpen config remote policy = .ok pending

structure Answered (active passive : H.Local) where
  opened : Opened active
  policy : Bool
  index : Nat
  spec : X.DeliverySpec
  delivery : X.Delivery opened.pending.output spec
  pending : H.SynReceived
  computed : Protocol.TCP.Handshake.listenSyn passive delivery.input policy = .ok pending

structure Acknowledged (active passive : H.Local) where
  answered : Answered active passive
  policy : Bool
  index : Nat
  spec : X.DeliverySpec
  delivery : X.Delivery answered.pending.output spec
  ready : H.ActiveEstablished answered.opened.pending delivery.input
  computed : Protocol.TCP.Handshake.synSentSynAck answered.opened.pending delivery.input policy = .ok ready

structure Completed (active passive : H.Local) where
  input : X.Input
  certificate : X.Complete input
  activeConfig : input.active = active
  passiveConfig : input.passive = passive

inductive Stage (active passive : H.Local) where
  | idle
  | opened (value : Opened active)
  | answered (value : Answered active passive)
  | acknowledged (value : Acknowledged active passive)
  | complete (value : Completed active passive)

inductive Decision where
  | accepted
  | failed (reason : H.Failure)
  | phase
  deriving Repr, BEq, DecidableEq

structure Link where
  sourceIndex : Nat
  path : Path

structure Effect (active passive : H.Local) where
  state : Stage active passive
  decision : Decision
  decoded : Option H.Input := none
  output : Option H.Input := none
  delivery : Option Link := none

def spec (input : H.Input) (path : Path) : X.DeliverySpec :=
  ⟨input.bytes, match path with
    | .direct => []
    | .rewrite => [⟨input.packet.header, input.packet.ip.packet.ttl⟩]⟩

private def failed (state : Stage active passive) (reason : H.Failure) (decoded : Option H.Input := none) :
    Effect active passive := ⟨state, .failed reason, decoded, none, none⟩

private def finish (active passive : H.Local) (before : Acknowledged active passive)
    (index : Nat) (ack : X.DeliverySpec) : Except String (Completed active passive) := do
  let input : X.Input := {
    active := active, remote := before.answered.opened.remote, passive := passive
    openPolicy := before.answered.opened.policy, synPolicy := before.answered.policy, synAckPolicy := before.policy
    syn := before.answered.spec, synAck := before.spec, ack := ack
    times := ⟨before.answered.opened.index, before.answered.index, before.index, index⟩ }
  let certificate ← input.check
  return ⟨input, certificate, rfl, rfl⟩

def evaluate (active passive : H.Local) (before : Stage active passive) (index : Nat) (event : Event) :
    Except String (Effect active passive) := do
  match before, event with
  | .idle, .activeOpen remote policy =>
    match computed : Protocol.TCP.Handshake.activeOpen active remote policy with
    | .error reason => return failed before reason
    | .ok pending =>
      return ⟨.opened ⟨remote, policy, index, pending, computed⟩, .accepted, none, some pending.output, none⟩
  | .opened opened, .listenSyn bytes path policy =>
    let candidate ← Protocol.TCP.EstablishedReceive.input bytes
    match Protocol.TCP.Handshake.listenSyn passive candidate policy with
    | .error reason => return failed before reason (some candidate)
    | .ok _ =>
      let selected := spec candidate path
      let delivery ← selected.check opened.pending.output
      match computed : Protocol.TCP.Handshake.listenSyn passive delivery.input policy with
      | .error reason => throw reason.message
      | .ok pending =>
        return ⟨.answered ⟨opened, policy, index, selected, delivery, pending, computed⟩,
          .accepted, some delivery.input, some pending.output, some ⟨opened.index, path⟩⟩
  | .answered answered, .synSentSynAck bytes path policy =>
    let candidate ← Protocol.TCP.EstablishedReceive.input bytes
    match Protocol.TCP.Handshake.synSentSynAck answered.opened.pending candidate policy with
    | .error reason => return failed before reason (some candidate)
    | .ok _ =>
      let selected := spec candidate path
      let delivery ← selected.check answered.pending.output
      match computed : Protocol.TCP.Handshake.synSentSynAck answered.opened.pending delivery.input policy with
      | .error reason => throw reason.message
      | .ok ready =>
        return ⟨.acknowledged ⟨answered, policy, index, selected, delivery, ready, computed⟩,
          .accepted, some delivery.input, some ready.output, some ⟨answered.index, path⟩⟩
  | .acknowledged acknowledged, .synReceivedAck bytes path =>
    let candidate ← Protocol.TCP.EstablishedReceive.input bytes
    match Protocol.TCP.Handshake.synReceivedAck acknowledged.answered.pending candidate with
    | .error reason => return failed before reason (some candidate)
    | .ok _ =>
      let selected := spec candidate path
      let _ ← selected.check acknowledged.ready.output
      let complete ← finish active passive acknowledged index selected
      return ⟨.complete complete, .accepted, some complete.certificate.ack.input, none,
        some ⟨acknowledged.index, path⟩⟩
  | _, _ => return ⟨before, .phase, none, none, none⟩

structure Step (active passive : H.Local) where
  before : Stage active passive
  index : Nat
  event : Event
  result : Effect active passive
  computed : evaluate active passive before index event = .ok result

def Step.supported (step : Step active passive) : Bool := match step.result.decision with
  | .phase | .failed (.unsupported _) => false
  | _ => true

inductive Trace (active passive : H.Local) : Nat → Stage active passive → List Event → List (Step active passive) →
    Stage active passive → List Event → Prop where
  | done (index) (state) : Trace active passive index state [] [] state []
  | stop (head : Step active passive) (unsupported : head.supported = false) (tail : List Event) :
      Trace active passive head.index head.before (head.event :: tail) [head] head.result.state tail
  | next (head : Step active passive) (supported : head.supported = true)
      (rest : Trace active passive (head.index + 1) head.result.state tail steps final remaining) :
      Trace active passive head.index head.before (head.event :: tail) (head :: steps) final remaining

structure Report (input : Input) where
  final : Stage input.active input.passive
  steps : List (Step input.active input.passive)
  remaining : List Event
  activeValid : input.active.Valid
  passiveValid : input.passive.Valid
  trace : Trace input.active input.passive 0 .idle input.events steps final remaining

private structure Run (active passive : H.Local) (index : Nat) (before : Stage active passive) (events : List Event) where
  final : Stage active passive
  steps : List (Step active passive)
  remaining : List Event
  trace : Trace active passive index before events steps final remaining

private def run (active passive : H.Local) (before : Stage active passive) (index : Nat) :
    (events : List Event) → Except String (Run active passive index before events)
  | [] => .ok ⟨before, [], [], .done index before⟩
  | event :: events => do
    match computed : evaluate active passive before index event with
    | .error reason => throw reason
    | .ok effect =>
      let head : Step active passive := ⟨before, index, event, effect, computed⟩
      if supported : head.supported = true then
        let rest ← run active passive effect.state (index + 1) events
        return ⟨rest.final, head :: rest.steps, rest.remaining, .next head supported rest.trace⟩
      else
        have unsupported : head.supported = false := by cases result : head.supported <;> simp_all
        return ⟨effect.state, [head], events, .stop head unsupported events⟩

def Input.check (input : Input) : Except String (Report input) := do
  if activeValid : input.active.Valid then
    if passiveValid : input.passive.Valid then
      let result ← run input.active input.passive .idle 0 input.events
      return ⟨result.final, result.steps, result.remaining, activeValid, passiveValid, result.trace⟩
    else throw "The passive local configuration must satisfy its capacity and IP size limits."
  else throw "The active local configuration must satisfy its capacity and IP size limits."

theorem Trace.covered (trace : Trace active passive index initial events steps final remaining) :
    steps.map (·.event) ++ remaining = events := by
  induction trace with
  | done index state => rfl
  | stop head _ _ => rfl
  | next head _ _ ih => simpa only [List.map_cons, List.cons_append, List.cons.injEq, true_and] using ih

theorem Trace.indices (trace : Trace active passive index initial events steps final remaining) :
    steps.map (·.index) = List.range' index steps.length := by
  induction trace with
  | done index state => rfl
  | stop head _ _ => rfl
  | next head _ _ ih => simpa only [List.map_cons, List.length_cons, List.range'_succ] using congrArg (head.index :: ·) ih

theorem Report.indices (report : Report input) :
    report.steps.map (·.index) = List.range' 0 report.steps.length := report.trace.indices

theorem Trace.prefix (trace : Trace active passive index initial events steps final remaining)
    (step : Step active passive) (member : step ∈ steps) :
    ∃ prior later, steps = prior ++ step :: later ∧
      Trace active passive index initial (prior.map (·.event)) prior step.before [] := by
  induction trace with
  | done index state => simp at member
  | stop head unsupported tail =>
    have same : step = head := by simpa using member
    subst step
    exact ⟨[], [], rfl, .done _ _⟩
  | next head supported rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨[], _, rfl, .done _ _⟩
    · obtain ⟨prior, later, same, preceding⟩ := ih member
      exact ⟨head :: prior, later, by simp [same], .next head supported preceding⟩

theorem Report.step_origin (report : Report input) (step : Step input.active input.passive)
    (member : step ∈ report.steps) :
    ∃ prior later, report.steps = prior ++ step :: later ∧
      Trace input.active input.passive 0 .idle (prior.map (·.event)) prior step.before [] ∧
      input.events = prior.map (·.event) ++ step.event :: (later.map (·.event) ++ report.remaining) ∧
      evaluate input.active input.passive step.before step.index step.event = .ok step.result := by
  obtain ⟨prior, later, same, preceding⟩ := report.trace.prefix step member
  refine ⟨prior, later, same, preceding, ?_, step.computed⟩
  rw [← report.trace.covered, same, List.map_append]
  simp

def Report.supported (report : Report input) : Bool := report.steps.all Step.supported

theorem Trace.supported_remaining (trace : Trace active passive index initial events steps final remaining)
    (supported : steps.all Step.supported = true) : remaining = [] := by
  induction trace with
  | done index state => rfl
  | stop head unsupported tail => simp [unsupported] at supported
  | next head supportedHead rest ih => exact ih (by simpa [supportedHead] using supported)

theorem Report.supported_covered (report : Report input) (supported : report.supported = true) :
    report.steps.map (·.event) = input.events ∧ report.remaining = [] := by
  have empty := report.trace.supported_remaining supported
  exact ⟨by simpa [empty] using report.trace.covered, empty⟩

theorem Trace.unsupported_stop (trace : Trace active passive index initial events steps final remaining)
    (unsupported : steps.all Step.supported = false) :
    ∃ prior step, steps = prior ++ [step] ∧ step.supported = false := by
  induction trace with
  | done index state => simp at unsupported
  | stop head blocked tail => exact ⟨[], head, rfl, blocked⟩
  | next head supported rest ih =>
    obtain ⟨prior, step, same, blocked⟩ := ih (by simpa [supported] using unsupported)
    exact ⟨head :: prior, step, by simp [same], blocked⟩

theorem Report.unsupported_stop (report : Report input) (unsupported : report.supported = false) :
    ∃ prior step, report.steps = prior ++ [step] ∧ step.supported = false := report.trace.unsupported_stop unsupported

def Stage.activeSeed : Stage active passive → Option Protocol.TCP.Endpoint.State
  | .acknowledged value => some value.ready.seed
  | .complete value => some value.certificate.activeSeed
  | _ => none

def Stage.passiveSeed : Stage active passive → Option Protocol.TCP.Endpoint.State
  | .complete value => some value.certificate.passiveSeed
  | _ => none

theorem Stage.active_valid (state : Stage active passive) (seed : Protocol.TCP.Endpoint.State)
    (selected : state.activeSeed = some seed) : seed.Valid := by
  cases state <;> simp only [Stage.activeSeed] at selected
  · cases selected
  · cases selected
  · cases selected
  · cases selected; exact Acknowledged.ready _ |>.valid
  · cases selected; exact Completed.certificate _ |>.valid.1

theorem Stage.passive_valid (state : Stage active passive) (seed : Protocol.TCP.Endpoint.State)
    (selected : state.passiveSeed = some seed) : seed.Valid := by
  cases state <;> simp only [Stage.passiveSeed] at selected
  · cases selected
  · cases selected
  · cases selected
  · cases selected
  · cases selected; exact Completed.certificate _ |>.valid.2

def Stage.exchangeComplete : Stage active passive → Bool
  | .complete _ => true
  | _ => false

theorem Stage.complete_history (state : Stage active passive) (complete : state.exchangeComplete = true) :
    ∃ value : Completed active passive, state = .complete value := by
  cases state <;> simp_all [Stage.exchangeComplete]

theorem Stage.passive_seed_before_ack (state : Stage active passive) (pending : state.exchangeComplete = false) :
    state.passiveSeed = none := by
  cases state <;> simp_all [Stage.exchangeComplete, Stage.passiveSeed]

theorem Report.complete_history (report : Report input) (complete : report.final.exchangeComplete = true) :
    ∃ value : Completed input.active input.passive, report.final = .complete value := report.final.complete_history complete

private def sequence (json : Lean.Json) : Except String Protocol.TCP.Seq := do
  let number ← json.getNat?
  if bound : number < 4294967296 then return ⟨⟨number, bound⟩⟩
  else throw "A sequence word must be between 0 and 4294967295."

def socketFromJson (json : Lean.Json) : Except String H.Socket := do
  let value ← Import.PacketFields.endpoint json
  return ⟨value.address, value.port⟩

def localFromJson (json : Lean.Json) : Except String H.Local := do
  Import.PacketFields.fields json ["socket", "iss", "capacity", "pendingLimit", "ipSendLimit"]
  let config : H.Local := ⟨← socketFromJson (← json.getObjVal? "socket"),
    ← sequence (← json.getObjVal? "iss"), ← (← json.getObjVal? "capacity").getNat?,
    ← (← json.getObjVal? "pendingLimit").getNat?, ← (← json.getObjVal? "ipSendLimit").getNat?⟩
  if config.Valid then return config
  else throw "Local capacity and storage cannot exceed 65535. The IP size limit must be between 41 and 65535."

private def pathFromJson (json : Lean.Json) : Except String Path := do
  match ← json.getStr? with
  | "direct" => return .direct
  | "rewrite" => return .rewrite
  | _ => throw "Use direct or rewrite for the startup byte path."

private def eventFromJson (json : Lean.Json) : Except String Event := do
  match ← (← json.getObjVal? "kind").getStr? with
  | "activeOpen" =>
    Import.PacketFields.fields json ["kind", "remote", "policyPermitted"]
    return .activeOpen (← socketFromJson (← json.getObjVal? "remote"))
      (← (← json.getObjVal? "policyPermitted").getBool?)
  | "listenSyn" =>
    Import.PacketFields.fields json ["kind", "rawIPv4Hex", "path", "policyPermitted"]
    return .listenSyn (← Import.EAPOL.bytesFromHex (← (← json.getObjVal? "rawIPv4Hex").getStr?))
      (← pathFromJson (← json.getObjVal? "path")) (← (← json.getObjVal? "policyPermitted").getBool?)
  | "synSentSynAck" =>
    Import.PacketFields.fields json ["kind", "rawIPv4Hex", "path", "policyPermitted"]
    return .synSentSynAck (← Import.EAPOL.bytesFromHex (← (← json.getObjVal? "rawIPv4Hex").getStr?))
      (← pathFromJson (← json.getObjVal? "path")) (← (← json.getObjVal? "policyPermitted").getBool?)
  | "synReceivedAck" =>
    Import.PacketFields.fields json ["kind", "rawIPv4Hex", "path"]
    return .synReceivedAck (← Import.EAPOL.bytesFromHex (← (← json.getObjVal? "rawIPv4Hex").getStr?))
      (← pathFromJson (← json.getObjVal? "path"))
  | _ => throw "Use activeOpen, listenSyn, synSentSynAck, or synReceivedAck as the event kind."

def Input.fromJson (json : Lean.Json) : Except String Input := do
  Import.PacketFields.fields json ["schema", "active", "passive", "events"]
  if (← (← json.getObjVal? "schema").getNat?) != 1 then throw "Use TCP startup schema 1."
  return ⟨← localFromJson (← json.getObjVal? "active"), ← localFromJson (← json.getObjVal? "passive"),
    ← (← (← json.getObjVal? "events").getArr?).toList.mapM eventFromJson⟩

def Input.parse (text : String) : Except String Input := do Input.fromJson (← Import.Json.parse text)

def socketJson (socket : H.Socket) : Lean.Json := Lean.Json.mkObj [
  ("address", Lean.toJson (Import.PacketFields.addressText socket.address)), ("port", Lean.toJson socket.port.val)]

def localJson (config : H.Local) : Lean.Json := Lean.Json.mkObj [
  ("socket", socketJson config.socket), ("iss", Lean.toJson config.iss.val), ("capacity", Lean.toJson config.capacity),
  ("pendingLimit", Lean.toJson config.pendingLimit), ("ipSendLimit", Lean.toJson config.ipSendLimit)]

def Path.name : Path → String | .direct => "direct" | .rewrite => "rewrite"

def Event.json : Event → Lean.Json
  | .activeOpen remote policy => Lean.Json.mkObj [("kind", Lean.toJson "activeOpen"),
      ("remote", socketJson remote), ("policyPermitted", Lean.toJson policy)]
  | .listenSyn bytes path policy => receive "listenSyn" bytes path [("policyPermitted", Lean.toJson policy)]
  | .synSentSynAck bytes path policy => receive "synSentSynAck" bytes path [("policyPermitted", Lean.toJson policy)]
  | .synReceivedAck bytes path => receive "synReceivedAck" bytes path []
where
  receive (kind : String) (bytes : List UInt8) (path : Path) (extra : List (String × Lean.Json)) : Lean.Json :=
    Lean.Json.mkObj ([("kind", Lean.toJson kind), ("rawIPv4Hex", Lean.toJson (Import.EAPOL.bytesToHex bytes)),
      ("path", Lean.toJson path.name)] ++ extra)

private def snapshot (activePhase passivePhase : String) (activeSeed passiveSeed : Option Protocol.TCP.Endpoint.State)
    (activeAt passiveAt : Option Nat) : Lean.Json := Lean.Json.mkObj [
  ("activePhase", Lean.toJson activePhase), ("passivePhase", Lean.toJson passivePhase),
  ("activeSeed", activeSeed.map TCPEndpoint.stateJson |>.getD .null),
  ("passiveSeed", passiveSeed.map TCPEndpoint.stateJson |>.getD .null),
  ("activeEstablishedAt", Lean.toJson activeAt), ("passiveEstablishedAt", Lean.toJson passiveAt)]

def Stage.json : Stage active passive → Lean.Json
  | .idle => snapshot "CLOSED" "LISTEN" none none none none
  | .opened _ => snapshot "SYN-SENT" "LISTEN" none none none none
  | .answered _ => snapshot "SYN-SENT" "SYN-RECEIVED" none none none none
  | .acknowledged value => snapshot "ESTABLISHED" "SYN-RECEIVED" (some value.ready.seed) none (some value.index) none
  | .complete value => snapshot "ESTABLISHED" "ESTABLISHED"
      (some value.certificate.activeSeed) (some value.certificate.passiveSeed)
      (some value.input.times.synAckReceived) (some value.input.times.ackReceived)

def Decision.json : Decision → Lean.Json
  | .accepted => Lean.Json.mkObj [("kind", Lean.toJson "accepted")]
  | .phase => Lean.Json.mkObj [("kind", Lean.toJson "unsupported"), ("reason", Lean.toJson "phase")]
  | .failed reason => match reason with
    | .reject reason => Lean.Json.mkObj [("kind", Lean.toJson "reject"), ("reason", Lean.toJson (match reason with
      | .invalidConfig => "invalidConfig" | .policy => "policy" | .tuple => "tuple" | .encoding => "encoding"))]
    | .unsupported reason => Lean.Json.mkObj [("kind", Lean.toJson "unsupported"), ("reason", Lean.toJson (match reason with
      | .flags => "flags" | .options => "options" | .data => "data" | .acknowledgment => "acknowledgment" | .sequence => "sequence"))]

def Event.kind : Event → String
  | .activeOpen _ _ => "activeOpen" | .listenSyn _ _ _ => "listenSyn"
  | .synSentSynAck _ _ _ => "synSentSynAck" | .synReceivedAck _ _ => "synReceivedAck"

def Step.json (step : Step active passive) : Lean.Json :=
  let decision := match step.result.decision with
    | .accepted => Lean.Json.mkObj [("kind", Lean.toJson "accepted"), ("operation", Lean.toJson step.event.kind)]
    | value => value.json
  Lean.Json.mkObj [
    ("index", Lean.toJson step.index), ("event", step.event.json), ("before", step.before.json),
    ("decision", decision), ("decodedInput", step.result.decoded.map (fun value => TCPReceive.decodedJson value.packet) |>.getD .null),
    ("output", TCPEndpoint.outputJson step.result.output),
    ("delivery", step.result.delivery.map (fun link => Lean.Json.mkObj [
      ("sourceIndex", Lean.toJson link.sourceIndex), ("path", Lean.toJson link.path.name)]) |>.getD .null),
    ("state", step.result.state.json)]

def assumptions : List String := [
  "The caller supplies local sockets, initial sequence choices, storage limits, and IP size evidence.",
  "This profile uses an ordinary exchange with empty startup payloads and no options.",
  "The active window initialization uses the explicit interpretation in RFC 1122, section 4.2.2.20(c).",
  "Successful receipts match earlier checked model outputs through the selected exact byte paths.",
  "Byte equality does not prove physical origin, peer identity, or the current connection instance.",
  "The application theorem needs future delivery history, a quiet startup boundary, and bounded sequence epochs.",
  "The profile does not implement resets, retransmission, timers, congestion control, or native transmission.",
  "An unsupported event stops the replay. Later transport bytes retain only their hex syntax checks."]

def sources : List Standards.Source := [
  ⟨"Transmission Control Protocol", "RFC 9293", "3.4, 3.7.1, and 3.10.7",
    "https://www.rfc-editor.org/rfc/rfc9293.html#section-3.10.7"⟩,
  ⟨"Requirements for Internet Hosts -- Communication Layers", "RFC 1122", "4.2.2.20(c) and (f)",
    "https://www.rfc-editor.org/rfc/rfc1122.html#section-4.2.2.20"⟩]

def Report.renderJson (report : Report input) : Lean.Json := Lean.Json.mkObj [
  ("scope", Lean.toJson "tcp-startup-projection"), ("supported", Lean.toJson report.supported),
  ("inputEvents", Lean.toJson input.events.length), ("evaluatedEvents", Lean.toJson report.steps.length),
  ("active", localJson input.active), ("passive", localJson input.passive),
  ("initial", (Stage.idle : Stage input.active input.passive).json),
  ("steps", Lean.toJson (report.steps.map Step.json)), ("remainingEvents", Lean.toJson (report.remaining.map Event.json)),
  ("final", report.final.json), ("exchangeComplete", Lean.toJson report.final.exchangeComplete),
  ("assumptions", Lean.toJson assumptions), ("sources", Lean.toJson (sources.map fun source => Lean.Json.mkObj [
    ("document", Lean.toJson source.document), ("version", Lean.toJson source.version),
    ("clause", Lean.toJson source.clause), ("url", Lean.toJson source.url)]))]

def Report.render (report : Report input) : String :=
  (if report.supported then "TCP STARTUP PROFILE SUPPORTED\n" else "TCP STARTUP PROFILE UNSUPPORTED\n") ++ report.renderJson.pretty

end Netlib.Check.TCPHandshake
