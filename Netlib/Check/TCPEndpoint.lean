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
  | enableRecovery
  | enableAck
  | dispatchAck (policyPermitted : Bool)
  | advanceClock (millis : Nat)
  | timeout (policyPermitted : Bool)
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
  | .enableRecovery => Lean.Json.mkObj [("kind", Lean.toJson "enableRecovery")]
  | .enableAck => Lean.Json.mkObj [("kind", Lean.toJson "enableAck")]
  | .dispatchAck policy => Lean.Json.mkObj [("kind", Lean.toJson "dispatchAck"), ("policyPermitted", Lean.toJson policy)]
  | .advanceClock millis => Lean.Json.mkObj [("kind", Lean.toJson "advanceClock"), ("millis", Lean.toJson millis)]
  | .timeout policy => Lean.Json.mkObj [("kind", Lean.toJson "timeout"), ("policyPermitted", Lean.toJson policy)]
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
    | "enableRecovery" => do
      Import.PacketFields.fields json ["kind"]
      return .enableRecovery
    | "enableAck" => do
      Import.PacketFields.fields json ["kind"]
      return .enableAck
    | "dispatchAck" => do
      Import.PacketFields.fields json ["kind", "policyPermitted"]
      return .dispatchAck (← (← json.getObjVal? "policyPermitted").getBool?)
    | "advanceClock" => do
      Import.PacketFields.fields json ["kind", "millis"]
      return .advanceClock (← (← json.getObjVal? "millis").getNat?)
    | "timeout" => do
      Import.PacketFields.fields json ["kind", "policyPermitted"]
      return .timeout (← (← json.getObjVal? "policyPermitted").getBool?)
    | "read" => do
      Import.PacketFields.fields json ["kind", "count"]
      return Event.read (← (← json.getObjVal? "count").getNat?)
    | "emitAck" => do
      Import.PacketFields.fields json ["kind", "policyPermitted"]
      return Event.emitAck (← (← json.getObjVal? "policyPermitted").getBool?)
    | "receive" => do
      Import.PacketFields.fields json ["kind", "rawIPv4Hex"]
      return Event.receive (← Import.EAPOL.bytesFromHex (← (← json.getObjVal? "rawIPv4Hex").getStr?))
    | _ => throw "The TCP application event kind is unknown."

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
  | enableRecovery : Matches .enableRecovery .enableRecovery
  | enableAck : Matches .enableAck .enableAck
  | dispatchAck (policy) : Matches (.dispatchAck policy) (.dispatchAck policy)
  | advanceClock (millis) : Matches (.advanceClock millis) (.advanceClock millis)
  | timeout (policy) : Matches (.timeout policy) (.timeout policy)
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
  | .enableRecovery => .ok ⟨.enableRecovery, selected ▸ .enableRecovery⟩
  | .enableAck => .ok ⟨.enableAck, selected ▸ .enableAck⟩
  | .dispatchAck policy => .ok ⟨.dispatchAck policy, selected ▸ .dispatchAck policy⟩
  | .advanceClock millis => .ok ⟨.advanceClock millis, selected ▸ .advanceClock millis⟩
  | .timeout policy => .ok ⟨.timeout policy, selected ▸ .timeout policy⟩
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
    (transportStarted : Bool) → (events : List Raw) → Except String (Run before events)
  | _, [] => .ok ⟨before, [], [], .done before⟩
  | transportStarted, raw :: events => do
    if transportStarted && before.ackReaction.isNone then
      match raw.event with
      | .enableAck => throw "Enable ACK reactions before this endpoint's send or receive operations."
      | _ => pure ()
    let converted ← convert raw
    let typed := Netlib.Protocol.TCP.ApplicationTrace.Step.make before valid converted.event stamp
    let head : Step := ⟨raw, typed, converted.source⟩
    if supported : head.supported = true then
      let transportStarted := transportStarted || match raw.event with | .send .. | .receive .. => true | _ => false
      let tail ← run typed.result.state typed.valid (stamp + 1) transportStarted events
      return ⟨tail.final, head :: tail.steps, tail.remaining, .next head supported tail.trace⟩
    else
      have unsupported : head.supported = false := by cases result : head.supported <;> simp_all
      return ⟨typed.result.state, [head], events, .stop head unsupported events⟩

def Input.check (input : Input) : Except String (Report input) := do
  if valid : input.seed.Valid then
    let result ← run input.seed valid 0 false input.events
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
    ∃ prior step, steps = prior ++ [step] ∧ step.supported = false := by
  induction trace with
  | done state => simp at unsupported
  | stop head blocked tail =>
    exact ⟨[], head, rfl, blocked⟩
  | next head supported rest ih =>
    obtain ⟨prior, step, same, blocked⟩ := ih (by simpa [supported] using unsupported)
    exact ⟨head :: prior, step, by simp [same], blocked⟩

theorem Report.unsupported_stop (report : Report input) (unsupported : report.supported = false) :
    ∃ prior step, report.steps = prior ++ [step] ∧ step.supported = false :=
  report.trace.unsupported_stop unsupported

def rationalJson (value : Rat) : Lean.Json := Lean.Json.mkObj [
  ("num", Lean.toJson value.num), ("den", Lean.toJson value.den)]

def recoveryJson (state : Protocol.TCP.Recovery.State) : Lean.Json := Lean.Json.mkObj [
  ("now", Lean.toJson state.now), ("smss", Lean.toJson state.smss),
  ("outstanding", Lean.toJson (state.outstanding.map fun entry => Lean.Json.mkObj [
    ("id", Lean.toJson entry.id), ("start", Lean.toJson entry.start), ("count", Lean.toJson entry.count),
    ("sentAt", Lean.toJson entry.sentAt), ("lastAt", Lean.toJson entry.lastAt), ("retried", Lean.toJson entry.retried)])),
  ("nextId", Lean.toJson state.nextId), ("frontier", Lean.toJson state.frontier),
  ("estimator", (state.estimator.map fun value => Lean.Json.mkObj [
    ("srtt", rationalJson value.srtt), ("variance", rationalJson value.variance)]).getD .null),
  ("lastSample", (state.lastSample.map fun value => Lean.Json.mkObj [
    ("id", Lean.toJson value.id), ("sentAt", Lean.toJson value.sentAt),
    ("acknowledgedAt", Lean.toJson value.acknowledgedAt)]).getD .null),
  ("rto", Lean.toJson state.rto), ("deadline", Lean.toJson state.deadline),
  ("cwnd", Lean.toJson state.cwnd), ("ssthresh", Lean.toJson state.ssthresh),
  ("lastTimedOut", Lean.toJson state.lastTimedOut), ("timeoutCount", Lean.toJson state.timeoutCount),
  ("duplicateAcks", Lean.toJson state.duplicateAcks), ("flight", Lean.toJson (Protocol.TCP.Recovery.flight state))]

def ownMSSJson : Protocol.TCP.MSS.Offer → Lean.Json
  | .absent => Lean.Json.mkObj [("kind", Lean.toJson "absent")]
  | .present value => Lean.Json.mkObj [("kind", Lean.toJson "present"), ("value", Lean.toJson value.word.val)]

def ackDemandJson (value : Protocol.TCP.AckReaction.Demand) : Lean.Json := Lean.Json.mkObj [
  ("kind", Lean.toJson (match value.kind with | .data => "data" | .sequence => "sequence" | .window => "window")),
  ("cursor", Lean.toJson value.cursor.val), ("position", Lean.toJson value.position),
  ("bytes", Lean.toJson value.bytes), ("minimumEdge", Lean.toJson value.minimumEdge)]

def ackCauseJson (value : Theory.TimedReaction.Cause Unit Protocol.TCP.AckReaction.Demand) : Lean.Json := Lean.Json.mkObj [
  ("id", Lean.toJson value.id), ("issuedAt", Lean.toJson value.issuedAt), ("due", Lean.toJson value.due),
  ("demand", ackDemandJson value.demand)]

def ackOutputJson (value : Protocol.TCP.AckReaction.Acknowledgment) : Lean.Json := Lean.Json.mkObj [
  ("cursor", Lean.toJson value.cursor.val), ("position", Lean.toJson value.position), ("window", Lean.toJson value.window)]

def ackReactionJson (value : Protocol.TCP.AckReaction.State) (capacity free outgoingMSS : Nat) : Lean.Json := Lean.Json.mkObj [
  ("origin", Lean.toJson value.origin.val), ("rmss", Lean.toJson value.rmss),
  ("advertisement", Lean.Json.mkObj [("frontier", Lean.toJson value.advertisement.frontier),
    ("edge", Lean.toJson value.advertisement.edge), ("window", Lean.toJson value.window),
    ("candidate", Lean.toJson (Protocol.TCP.AckReaction.candidate value capacity free outgoingMSS)),
    ("free", Lean.toJson free), ("threshold", Lean.toJson (Protocol.TCP.ReceiveAdvertisement.threshold capacity outgoingMSS))]),
  ("work", Lean.Json.mkObj [("nextID", Lean.toJson value.work.nextID),
    ("nextDischarge", Lean.toJson value.work.nextDischarge), ("pendingDue", Lean.toJson value.due),
    ("credit", Lean.toJson value.credit), ("pending", Lean.toJson (value.work.pending.map ackCauseJson)),
    ("completed", Lean.toJson (value.work.completed.map fun completion => Lean.Json.mkObj [
      ("id", Lean.toJson completion.id), ("time", Lean.toJson completion.time),
      ("output", ackOutputJson completion.output), ("causes", Lean.toJson (completion.causes.map ackCauseJson))]))]),
  ("fullSegments", Lean.toJson value.fullSegments), ("dataBytes", Lean.toJson value.dataBytes)]

def stateJson (state : E.State) : Lean.Json := Lean.Json.mkObj ([
  ("core", TCPReceive.stateJson state.core), ("pendingHex", Lean.toJson (Import.EAPOL.bytesToHex state.pending)),
  ("pendingLimit", Lean.toJson state.pendingLimit), ("sendWindow", Lean.toJson state.sendWindow),
  ("sendWL1", Lean.toJson state.sendWL1.val), ("sendWL2", Lean.toJson state.sendWL2.val),
  ("effectiveMSS", Lean.toJson state.effectiveMSS), ("ipSendLimit", Lean.toJson state.ipSendLimit)] ++
  (match state.recovery with
  | none => []
  | some value => [("recovery", recoveryJson value), ("lastAckWindow", Lean.toJson state.lastAckWindow)]) ++
  match state.ackReaction with
  | none => []
  | some value => [("localReceiveMSS", ownMSSJson state.localReceiveMSS),
    ("ackReaction", ackReactionJson value state.core.capacity state.core.window state.effectiveMSS)])

def ackStopName : Protocol.TCP.AckReaction.Stop → String
  | .disabled => "disabled" | .alreadyEnabled => "alreadyEnabled" | .noCredit => "noCredit"
  | .early => "early" | .ledger => "ledger" | .deadline => "deadline" | .challenge => "challenge"

def recoveryStopName : Protocol.TCP.Recovery.Stop → String
  | .backwardClock => "backwardClock" | .early => "early" | .idle => "idle" | .ledger => "ledger"
  | .fastRecovery => "fastRecovery" | .failureHandling => "failureHandling"
  | .persist => "persist"

private def rejectName : E.Reject → String
  | .invalidSeed => "invalidSeed" | .pendingCapacity => "pendingCapacity" | .readBounds => "readBounds"
  | .sendBounds => "sendBounds" | .policy => "policy" | .encoding => "encoding"
  | .recovery reason => "recovery." ++ recoveryStopName reason
  | .ack reason => "ack." ++ ackStopName reason
  | .input reason => "input." ++ match reason with
    | .invalidSeed => "invalidSeed" | .tuple => "tuple" | .sequence => "sequence"
    | .missingAck => "missingAck" | .acknowledgment => "acknowledgment"

private def acceptedJson : E.Accepted → List (String × Lean.Json)
  | .write count => [("operation", Lean.toJson "write"), ("count", Lean.toJson count)]
  | .send count => [("operation", Lean.toJson "send"), ("count", Lean.toJson count)]
  | .enableRecovery => [("operation", Lean.toJson "enableRecovery")]
  | .enableAck => [("operation", Lean.toJson "enableAck")]
  | .dispatchAck => [("operation", Lean.toJson "dispatchAck")]
  | .advanceClock => [("operation", Lean.toJson "advanceClock")]
  | .retry count => [("operation", Lean.toJson "retry"), ("count", Lean.toJson count)]
  | .read count => [("operation", Lean.toJson "read"), ("count", Lean.toJson count)]
  | .emitAck => [("operation", Lean.toJson "emitAck")]
  | .receive acknowledged received => [("operation", Lean.toJson "receive"),
      ("acknowledged", Lean.toJson acknowledged), ("received", Lean.toJson received)]

def decisionJson : E.Decision → Lean.Json
  | .accepted value => Lean.Json.mkObj (("kind", Lean.toJson "accepted") :: acceptedJson value)
  | .reject reason => Lean.Json.mkObj [("kind", Lean.toJson "reject"), ("reason", Lean.toJson (rejectName reason))]
  | .unsupported reason => TCPReceive.decisionJson (.blocked (.unsupported reason))
  | .recoveryUnsupported reason => Lean.Json.mkObj [
      ("kind", Lean.toJson "unsupported"), ("reason", Lean.toJson ("recovery." ++ recoveryStopName reason))]
  | .ackUnsupported reason => Lean.Json.mkObj [
      ("kind", Lean.toJson "unsupported"), ("reason", Lean.toJson ("ack." ++ ackStopName reason))]

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
  "Recovery initialization requires empty outstanding storage. Its clocks, one-MSS flight bound, and retry limits are explicit.",
  "Fast recovery, persist, control retries, native clocks, and general reliable delivery remain outside this profile.",
  "The output bytes do not prove native transmission, peer delivery, or eventual application delivery.",
  "An unsupported event stops the replay. Later receive byte strings retain only their hex syntax checks."]

def sources : List Standards.Source := TCPReceive.sources ++ [
  ⟨"Computing TCP's Retransmission Timer", "RFC 6298", "2, 3, and 5",
    "https://www.rfc-editor.org/rfc/rfc6298.html#section-5"⟩,
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
