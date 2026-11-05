import Netlib.Protocol.TCP.ApplicationTrace
import Netlib.Check.TCPReceive

/-!
# Checked TCP application events

Each processed receive event has checked IPv4 and TCP bytes.
An unsupported event stops the replay before the next transport decode.
The report retains application read results and actual model output bytes.
-/

namespace Netlib.Check.TCPEndpoint

namespace E
export Netlib.Protocol.TCP.Endpoint (State Result Decision Reject Accepted)
end E
namespace T
export Netlib.Protocol.TCP.ApplicationTrace (Event Step Chain evaluate)
end T

inductive Event where
  | write (payload : List UInt8)
  | send (count : Nat) (policyPermitted : Bool)
  | read (count : Nat)
  | emitAck (policyPermitted : Bool)
  | receive (bytes : List UInt8)

structure Raw where
  event : Event

def Raw.json (raw : Raw) : Lean.Json := match raw.event with
  | .write payload => Lean.Json.mkObj [("kind", Lean.toJson "write"),
      ("payloadHex", Lean.toJson (Import.EAPOL.bytesToHex payload))]
  | .send count policy => Lean.Json.mkObj [("kind", Lean.toJson "send"),
      ("count", Lean.toJson count), ("policyPermitted", Lean.toJson policy)]
  | .read count => Lean.Json.mkObj [("kind", Lean.toJson "read"), ("count", Lean.toJson count)]
  | .emitAck policy => Lean.Json.mkObj [("kind", Lean.toJson "emitAck"), ("policyPermitted", Lean.toJson policy)]
  | .receive bytes => Lean.Json.mkObj [("kind", Lean.toJson "receive"),
      ("rawIPv4Hex", Lean.toJson (Import.EAPOL.bytesToHex bytes))]

structure Input where
  seed : E.State
  events : List Raw

private def sequence (json : Lean.Json) : Except String Protocol.TCP.Seq := do
  let value ← json.getNat?
  if bound : value < 4294967296 then return ⟨⟨value, bound⟩⟩
  else throw "A sequence word must be between 0 and 4294967295."

private def coreFromJson (json : Lean.Json) : Except String Protocol.TCP.EstablishedReceive.State := do
  Import.PacketFields.fields json ["inbound", "receiveNext", "capacity", "receivedHex", "sendUna", "sendNext", "sentHex"]
  return {
    inbound := ← Import.PacketFields.header (← json.getObjVal? "inbound")
    receiveNext := ← sequence (← json.getObjVal? "receiveNext")
    capacity := ← (← json.getObjVal? "capacity").getNat?
    received := ← Import.EAPOL.bytesFromHex (← (← json.getObjVal? "receivedHex").getStr?)
    sendUna := ← sequence (← json.getObjVal? "sendUna")
    sendNext := ← sequence (← json.getObjVal? "sendNext")
    sent := ← Import.EAPOL.bytesFromHex (← (← json.getObjVal? "sentHex").getStr?) }

private def seedFromJson (json : Lean.Json) : Except String E.State := do
  Import.PacketFields.fields json ["core", "pendingHex", "pendingLimit", "sendWindow", "sendWL1", "sendWL2", "effectiveMSS", "ipSendLimit"]
  let state : E.State := {
    core := ← coreFromJson (← json.getObjVal? "core")
    pending := ← Import.EAPOL.bytesFromHex (← (← json.getObjVal? "pendingHex").getStr?)
    pendingLimit := ← (← json.getObjVal? "pendingLimit").getNat?
    sendWindow := ← (← json.getObjVal? "sendWindow").getNat?
    sendWL1 := ← sequence (← json.getObjVal? "sendWL1")
    sendWL2 := ← sequence (← json.getObjVal? "sendWL2")
    effectiveMSS := ← (← json.getObjVal? "effectiveMSS").getNat?
    ipSendLimit := ← (← json.getObjVal? "ipSendLimit").getNat? }
  if state.Valid then return state
  else throw "The TCP seed must satisfy its buffer, cursor, window, MSS, and IP size limits."

private def eventValueFromJson (json : Lean.Json) : Except String Event := do
  let kind ← (← json.getObjVal? "kind").getStr?
  match kind with
    | "write" => do
      Import.PacketFields.fields json ["kind", "payloadHex"]
      return Event.write (← Import.EAPOL.bytesFromHex (← (← json.getObjVal? "payloadHex").getStr?))
    | "send" => do
      Import.PacketFields.fields json ["kind", "count", "policyPermitted"]
      return Event.send (← (← json.getObjVal? "count").getNat?) (← (← json.getObjVal? "policyPermitted").getBool?)
    | "read" => do
      Import.PacketFields.fields json ["kind", "count"]
      return Event.read (← (← json.getObjVal? "count").getNat?)
    | "emitAck" => do
      Import.PacketFields.fields json ["kind", "policyPermitted"]
      return Event.emitAck (← (← json.getObjVal? "policyPermitted").getBool?)
    | "receive" => do
      Import.PacketFields.fields json ["kind", "rawIPv4Hex"]
      return Event.receive (← Import.EAPOL.bytesFromHex (← (← json.getObjVal? "rawIPv4Hex").getStr?))
    | _ => throw "Use write, send, read, emitAck, or receive as the event kind."

private def eventFromJson (json : Lean.Json) : Except String Raw := do
  return ⟨← eventValueFromJson json⟩

def Input.fromJson (json : Lean.Json) : Except String Input := do
  Import.PacketFields.fields json ["schema", "seed", "events"]
  if (← (← json.getObjVal? "schema").getNat?) != 1 then throw "Use TCP application schema 1."
  return ⟨← seedFromJson (← json.getObjVal? "seed"),
    ← (← (← json.getObjVal? "events").getArr?).toList.mapM eventFromJson⟩

def Input.parse (text : String) : Except String Input := do Input.fromJson (← Import.Json.parse text)

inductive Matches : Event → T.Event → Prop where
  | write (payload) : Matches (.write payload) (.write payload)
  | send (count policy) : Matches (.send count policy) (.send count policy)
  | read (count) : Matches (.read count) (.read count)
  | emitAck (policy) : Matches (.emitAck policy) (.emitAck policy)
  | receive (value : Protocol.TCP.EstablishedReceive.Input) : Matches (.receive value.bytes) (.receive value)

private structure Converted (raw : Raw) where
  event : T.Event
  source : Matches raw.event event

private def convert (raw : Raw) : Except String (Converted raw) :=
  match selected : raw.event with
  | .write payload => .ok ⟨.write payload, selected ▸ .write payload⟩
  | .send count policy => .ok ⟨.send count policy, selected ▸ .send count policy⟩
  | .read count => .ok ⟨.read count, selected ▸ .read count⟩
  | .emitAck policy => .ok ⟨.emitAck policy, selected ▸ .emitAck policy⟩
  | .receive bytes => do
    match decoded : Protocol.TCP.decodeIPv4 bytes with
    | .error reason => throw reason
    | .ok packet =>
      let checked : Protocol.TCP.EstablishedReceive.Input := ⟨bytes, packet, decoded⟩
      return ⟨.receive checked, selected ▸ .receive checked⟩

structure Step where
  raw : Raw
  typed : T.Step
  source : Matches raw.event typed.event

def Step.supported (step : Step) : Bool := step.typed.supported

inductive Trace : E.State → List Raw → List Step → E.State → List Raw → Prop where
  | done (state) : Trace state [] [] state []
  | stop (head : Step) (unsupported : head.supported = false) (tail : List Raw) :
      Trace head.typed.before (head.raw :: tail) [head] head.typed.result.state tail
  | next (head : Step) (supported : head.supported = true)
      (rest : Trace head.typed.result.state tail steps final remaining) :
      Trace head.typed.before (head.raw :: tail) (head :: steps) final remaining

structure Report (input : Input) where
  final : E.State
  steps : List Step
  remaining : List Raw
  seedValid : input.seed.Valid
  trace : Trace input.seed input.events steps final remaining

private structure Run (before : E.State) (events : List Raw) where
  final : E.State
  steps : List Step
  remaining : List Raw
  trace : Trace before events steps final remaining

private def run (before : E.State) (valid : before.Valid) (stamp : Nat) :
    (events : List Raw) → Except String (Run before events)
  | [] => .ok ⟨before, [], [], .done before⟩
  | raw :: events => do
    let converted ← convert raw
    let typed := Netlib.Protocol.TCP.ApplicationTrace.Step.make before valid converted.event stamp
    let head : Step := ⟨raw, typed, converted.source⟩
    if supported : head.supported = true then
      let tail ← run typed.result.state typed.valid (stamp + 1) events
      return ⟨tail.final, head :: tail.steps, tail.remaining, .next head supported tail.trace⟩
    else
      have unsupported : head.supported = false := by cases result : head.supported <;> simp_all
      return ⟨typed.result.state, [head], events, .stop head unsupported events⟩

def Input.check (input : Input) : Except String (Report input) := do
  if valid : input.seed.Valid then
    let result ← run input.seed valid 0 input.events
    return ⟨result.final, result.steps, result.remaining, valid, result.trace⟩
  else throw "The TCP seed must satisfy its buffer, cursor, window, MSS, and IP size limits."

theorem Trace.chain (trace : Trace initial events steps final remaining) :
    T.Chain initial (steps.map (·.typed)) final := by
  induction trace with
  | done state => exact .nil state
  | stop head _ _ => exact .cons head.typed (.nil head.typed.result.state)
  | next head _ _ ih => exact .cons head.typed ih

theorem Trace.covered (trace : Trace initial events steps final remaining) :
    steps.map (·.raw) ++ remaining = events := by
  induction trace with
  | done state => rfl
  | stop head _ _ => rfl
  | next head _ _ ih => simpa only [List.map_cons, List.cons_append, List.cons.injEq, true_and] using ih

theorem Report.final_valid (report : Report input) : report.final.Valid := report.trace.chain.valid report.seedValid

def Report.supported (report : Report input) : Bool := report.steps.all Step.supported

theorem Report.conservation (report : Report input) :
    input.seed.pending ++ (report.steps.map (·.typed)).flatMap Netlib.Protocol.TCP.ApplicationTrace.Step.written =
      (report.steps.map (·.typed)).flatMap Netlib.Protocol.TCP.ApplicationTrace.Step.emitted ++ report.final.pending ∧
    input.seed.core.sent ++ (report.steps.map (·.typed)).flatMap Netlib.Protocol.TCP.ApplicationTrace.Step.emitted =
      (report.steps.map (·.typed)).flatMap Netlib.Protocol.TCP.ApplicationTrace.Step.acknowledged ++ report.final.core.sent ∧
    input.seed.core.received ++ (report.steps.map (·.typed)).flatMap Netlib.Protocol.TCP.ApplicationTrace.Step.acceptedPayload =
      (report.steps.map (·.typed)).flatMap Netlib.Protocol.TCP.ApplicationTrace.Step.readBytes ++ report.final.core.received :=
  ⟨report.trace.chain.pending, report.trace.chain.sent, report.trace.chain.received⟩

theorem Trace.prefix (trace : Trace initial events steps final remaining) (step : Step) (member : step ∈ steps) :
    ∃ prior later, steps = prior ++ step :: later ∧
      T.Chain initial (prior.map (·.typed)) step.typed.before ∧
      T.Chain step.typed.result.state (later.map (·.typed)) final := by
  induction trace with
  | done state => simp at member
  | stop head unsupported tail =>
    have same : step = head := by simpa using member
    subst step
    exact ⟨[], [], rfl, .nil _, .nil _⟩
  | next head supported rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨[], _, rfl, .nil _, rest.chain⟩
    · obtain ⟨prior, later, same, preceding, following⟩ := ih member
      exact ⟨head :: prior, later, by simp [same], .cons head.typed preceding, following⟩

theorem Report.step_origin (report : Report input) (step : Step) (member : step ∈ report.steps) :
    ∃ prior later, report.steps = prior ++ step :: later ∧
      T.Chain input.seed (prior.map (·.typed)) step.typed.before ∧
      input.events = prior.map (·.raw) ++ step.raw :: (later.map (·.raw) ++ report.remaining) ∧
      Matches step.raw.event step.typed.event ∧ step.typed.result = T.evaluate step.typed.before step.typed.event := by
  obtain ⟨prior, later, same, preceding, _⟩ := report.trace.prefix step member
  refine ⟨prior, later, same, preceding, ?_, step.source, step.typed.computed⟩
  rw [← report.trace.covered, same, List.map_append]
  simp

theorem Trace.supported_remaining (trace : Trace initial events steps final remaining)
    (supported : steps.all Step.supported = true) : remaining = [] := by
  induction trace with
  | done state => rfl
  | stop head unsupported tail => simp [unsupported] at supported
  | next head supportedHead rest ih =>
    exact ih (by simpa [supportedHead] using supported)

theorem Report.supported_covered (report : Report input) (supported : report.supported = true) :
    report.steps.map (·.raw) = input.events ∧ report.remaining = [] := by
  have empty := report.trace.supported_remaining supported
  exact ⟨by simpa [empty] using report.trace.covered, empty⟩

theorem Trace.unsupported_stop (trace : Trace initial events steps final remaining)
    (unsupported : steps.all Step.supported = false) :
    ∃ prior step reason, steps = prior ++ [step] ∧ step.typed.result.decision = .unsupported reason := by
  induction trace with
  | done state => simp at unsupported
  | stop head blocked tail =>
    refine ⟨[], head, ?_⟩
    cases selected : head.typed.result.decision with
    | accepted action => simp [Step.supported, Protocol.TCP.ApplicationTrace.Step.supported, selected] at blocked
    | reject reason => simp [Step.supported, Protocol.TCP.ApplicationTrace.Step.supported, selected] at blocked
    | unsupported reason => exact ⟨reason, rfl, rfl⟩
  | next head supported rest ih =>
    obtain ⟨prior, step, reason, same, blocked⟩ := ih (by simpa [supported] using unsupported)
    exact ⟨head :: prior, step, reason, by simp [same], blocked⟩

theorem Report.unsupported_stop (report : Report input) (unsupported : report.supported = false) :
    ∃ prior step reason, report.steps = prior ++ [step] ∧ step.typed.result.decision = .unsupported reason :=
  report.trace.unsupported_stop unsupported

def stateJson (state : E.State) : Lean.Json := Lean.Json.mkObj [
  ("core", TCPReceive.stateJson state.core), ("pendingHex", Lean.toJson (Import.EAPOL.bytesToHex state.pending)),
  ("pendingLimit", Lean.toJson state.pendingLimit), ("sendWindow", Lean.toJson state.sendWindow),
  ("sendWL1", Lean.toJson state.sendWL1.val), ("sendWL2", Lean.toJson state.sendWL2.val),
  ("effectiveMSS", Lean.toJson state.effectiveMSS), ("ipSendLimit", Lean.toJson state.ipSendLimit)]

private def rejectName : E.Reject → String
  | .invalidSeed => "invalidSeed" | .pendingCapacity => "pendingCapacity" | .readBounds => "readBounds"
  | .sendBounds => "sendBounds" | .policy => "policy" | .encoding => "encoding"
  | .input reason => "input." ++ match reason with
    | .invalidSeed => "invalidSeed" | .tuple => "tuple" | .sequence => "sequence"
    | .missingAck => "missingAck" | .acknowledgment => "acknowledgment"

private def acceptedJson : E.Accepted → List (String × Lean.Json)
  | .write count => [("operation", Lean.toJson "write"), ("count", Lean.toJson count)]
  | .send count => [("operation", Lean.toJson "send"), ("count", Lean.toJson count)]
  | .read count => [("operation", Lean.toJson "read"), ("count", Lean.toJson count)]
  | .emitAck => [("operation", Lean.toJson "emitAck")]
  | .receive acknowledged received => [("operation", Lean.toJson "receive"),
      ("acknowledged", Lean.toJson acknowledged), ("received", Lean.toJson received)]

def decisionJson : E.Decision → Lean.Json
  | .accepted value => Lean.Json.mkObj (("kind", Lean.toJson "accepted") :: acceptedJson value)
  | .reject reason => Lean.Json.mkObj [("kind", Lean.toJson "reject"), ("reason", Lean.toJson (rejectName reason))]
  | .unsupported reason => TCPReceive.decisionJson (.blocked (.unsupported reason))

def outputJson : Option Protocol.TCP.EstablishedReceive.Input → Lean.Json
  | none => .null
  | some value => Lean.Json.mkObj [("rawIPv4Hex", Lean.toJson (Import.EAPOL.bytesToHex value.bytes)),
      ("decoded", TCPReceive.decodedJson value.packet)]

def Step.renderJson (step : Step) (index : Nat) : Lean.Json := Lean.Json.mkObj [
  ("index", Lean.toJson index), ("event", step.raw.json), ("before", stateJson step.typed.before),
  ("decodedInput", match step.typed.event with | .receive value => TCPReceive.decodedJson value.packet | _ => .null),
  ("decision", decisionJson step.typed.result.decision), ("output", outputJson step.typed.result.output),
  ("readHex", Lean.toJson (Import.EAPOL.bytesToHex step.typed.result.read)),
  ("ack", TCPReceive.ackJson step.typed.result.ack), ("state", stateJson step.typed.result.state)]

def assumptions : List String := [
  "The caller supplies a pre-established seed. The seed does not prove a handshake or earlier sends.",
  "The caller supplies the effective MSS and IP size limit from startup and lower-layer evidence.",
  "The initial peer window and window-history fields require separate evidence.",
  "The serial window-history comparisons require an age below half the sequence space.",
  "The policy input permits the selected output. It does not prove congestion control or ACK scheduling.",
  "The paired application theorem requires earlier peer sends, certified byte transformations, and a bounded finite epoch.",
  "The output bytes do not prove native transmission, peer delivery, or eventual application delivery.",
  "An unsupported event stops the replay. Later receive byte strings retain only their hex syntax checks."]

def sources : List Standards.Source := TCPReceive.sources ++ [
  ⟨"Transmission Control Protocol", "RFC 9293", "3.10.2 and 3.10.3",
    "https://www.rfc-editor.org/rfc/rfc9293.html#section-3.10.2"⟩,
  ⟨"Transmission Control Protocol", "RFC 9293", "3.7.1 and 3.8.6",
    "https://www.rfc-editor.org/rfc/rfc9293.html#section-3.7.1"⟩,
  ⟨"TCP Congestion Control", "RFC 5681", "2 and 3.1",
    "https://www.rfc-editor.org/rfc/rfc5681.html#section-2"⟩]

def Report.renderJson (report : Report input) : Lean.Json := Lean.Json.mkObj [
  ("scope", Lean.toJson "tcp-application-projection"), ("supported", Lean.toJson report.supported),
  ("inputEvents", Lean.toJson input.events.length), ("evaluatedEvents", Lean.toJson report.steps.length),
  ("seed", stateJson input.seed), ("steps", Lean.toJson (report.steps.zipIdx.map fun (step, index) => step.renderJson index)),
  ("remainingEvents", Lean.toJson (report.remaining.map (·.json))), ("final", stateJson report.final),
  ("finalStateValid", Lean.toJson true), ("assumptions", Lean.toJson assumptions),
  ("sources", Lean.toJson (sources.map fun source => Lean.Json.mkObj [
    ("document", Lean.toJson source.document), ("version", Lean.toJson source.version),
    ("clause", Lean.toJson source.clause), ("url", Lean.toJson source.url)]))]

def Report.render (report : Report input) : String :=
  (if report.supported then "TCP APPLICATION PROFILE SUPPORTED\n" else "TCP APPLICATION PROFILE UNSUPPORTED\n") ++ report.renderJson.pretty

end Netlib.Check.TCPEndpoint
