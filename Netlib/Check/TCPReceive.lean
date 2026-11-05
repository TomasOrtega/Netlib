import Netlib.Protocol.TCP.EstablishedReceive
import Netlib.Check.TCP

/-!
# Checked TCP receive prefixes

The caller supplies the initial state and sent-byte buffer.
The caller assumes that the endpoint transmitted these buffer bytes.
Each evaluated input has an IPv4 decode proof and a TCP decode proof.
An unsupported result stops the replay before the next transport decode.
The remaining bytes do not establish later endpoint behavior.
-/

namespace Netlib.Check.TCPReceive

open Protocol
namespace Model
export Netlib.Protocol.TCP.EstablishedReceive
  (State Input Result Decision Block Reject Unsupported AckKind AckRequest receive)
end Model

structure Input where
  seed : Model.State
  packets : List (List UInt8)

private def sequence (json : Lean.Json) : Except String Protocol.TCP.Seq := do
  let value ← json.getNat?
  if bounded : value < 4294967296 then return ⟨⟨value, bounded⟩⟩
  else throw "A sequence word must be between 0 and 4294967295."

private def seedFromJson (json : Lean.Json) : Except String Model.State := do
  Import.PacketFields.fields json ["inbound", "receiveNext", "capacity", "receivedHex", "sendUna", "sendNext", "sentHex"]
  let seed : Model.State := {
    inbound := ← Import.PacketFields.header (← json.getObjVal? "inbound")
    receiveNext := ← sequence (← json.getObjVal? "receiveNext")
    capacity := ← (← json.getObjVal? "capacity").getNat?
    received := ← Import.EAPOL.bytesFromHex (← (← json.getObjVal? "receivedHex").getStr?)
    sendUna := ← sequence (← json.getObjVal? "sendUna")
    sendNext := ← sequence (← json.getObjVal? "sendNext")
    sent := ← Import.EAPOL.bytesFromHex (← (← json.getObjVal? "sentHex").getStr?) }
  if seed.Valid then return seed
  else throw "The TCP seed must satisfy the receive buffer, send span, tuple, and cursor limits."

def Input.fromJson (json : Lean.Json) : Except String Input := do
  Import.PacketFields.fields json ["schema", "seed", "packetsHex"]
  if (← (← json.getObjVal? "schema").getNat?) != 1 then throw "Use TCP receive schema 1."
  let seed ← seedFromJson (← json.getObjVal? "seed")
  let packets ← (← (← json.getObjVal? "packetsHex").getArr?).toList.mapM fun packet => do
    Import.EAPOL.bytesFromHex (← packet.getStr?)
  return ⟨seed, packets⟩

def Input.parse (text : String) : Except String Input := do Input.fromJson (← Import.Json.parse text)

structure Step where
  before : Model.State
  input : Model.Input
  result : Model.Result
  beforeValid : before.Valid
  computed : result = Model.receive before input
  valid : result.state.Valid

def Step.make (before : Model.State) (valid : before.Valid) (input : Model.Input) : Step :=
  ⟨before, input, Model.receive before input, valid, rfl,
    Protocol.TCP.EstablishedReceive.receive_valid before input valid⟩

def Step.supported (step : Step) : Bool :=
  match step.result.decision with
  | .blocked (.unsupported _) => false
  | _ => true

def Step.acceptedPayload (step : Step) : List UInt8 :=
  match step.result.decision with
  | .accepted _ _ => step.input.packet.segment.payload
  | .blocked _ => []

theorem Step.source_valid (step : Step) : Protocol.TCPRewrite.SourceValid step.input.packet := step.input.valid

theorem Step.blocked_preserves (step : Step) (reason : Model.Block)
    (blocked : step.result.decision = .blocked reason) : step.result.state = step.before := by
  rw [step.computed]
  exact Protocol.TCP.EstablishedReceive.receive_blocked_preserves step.before step.input reason
    (by rw [← step.computed]; exact blocked)

theorem Step.accepted_facts (step : Step) (count size : Nat)
    (accepted : step.result.decision = .accepted count size) :
    Protocol.TCP.EstablishedReceive.Ready step.before step.input.packet.header step.input.packet.segment ∧
      count ≤ step.before.sent.length ∧ size = step.input.packet.segment.payload.length ∧
      step.input.packet.segment.payload.length ≤ step.before.window ∧
      step.result.state.received = step.before.received ++ step.input.packet.segment.payload ∧
      step.result.state.receiveNext = step.before.receiveNext.add step.input.packet.segment.payload.length ∧
      step.result.state.sent = step.before.sent.drop count ∧
      step.result.state.sendUna = step.before.sendUna.add count ∧ step.result.state.sendNext = step.before.sendNext := by
  have selected : (Model.receive step.before step.input).decision = .accepted count size := by
    rw [← step.computed]
    exact accepted
  have ready := Protocol.TCP.EstablishedReceive.receive_accepted_ready step.before step.input count size selected
  have effects := Protocol.TCP.EstablishedReceive.receive_accepted step.before step.input count size selected
  have payload := Protocol.TCP.EstablishedReceive.receive_payload step.before step.input count size selected
  have acknowledged := Protocol.TCP.EstablishedReceive.receive_ack_prefix step.before step.input count size selected
  rw [← step.computed] at payload acknowledged
  exact ⟨ready, effects.2.1, effects.2.2.1, effects.2.2.2.1, payload.1, payload.2,
    acknowledged.1, acknowledged.2.1, acknowledged.2.2⟩

inductive Chain : Model.State → List Step → Model.State → Prop where
  | nil (state : Model.State) : Chain state [] state
  | cons (head : Step) (rest : Chain head.result.state tail final) : Chain head.before (head :: tail) final

inductive Trace : Model.State → List (List UInt8) → List Step → Model.State → List (List UInt8) → Prop where
  | done (state : Model.State) : Trace state [] [] state []
  | stop (head : Step) (unsupported : head.supported = false) (tail : List (List UInt8)) :
      Trace head.before (head.input.bytes :: tail) [head] head.result.state tail
  | next (head : Step) (supported : head.supported = true)
      (rest : Trace head.result.state tail steps final remaining) :
      Trace head.before (head.input.bytes :: tail) (head :: steps) final remaining

structure Report (input : Input) where
  final : Model.State
  steps : List Step
  remaining : List (List UInt8)
  seedValid : input.seed.Valid
  trace : Trace input.seed input.packets steps final remaining

private structure Run (before : Model.State) (packets : List (List UInt8)) where
  final : Model.State
  steps : List Step
  remaining : List (List UInt8)
  trace : Trace before packets steps final remaining

private def run (before : Model.State) (valid : before.Valid) :
    (packets : List (List UInt8)) → Except String (Run before packets)
  | [] => .ok ⟨before, [], [], .done before⟩
  | raw :: packets => do
    match decoded : Protocol.TCP.decodeIPv4 raw with
    | .error reason => throw reason
    | .ok packet =>
      let value : Model.Input := ⟨raw, packet, decoded⟩
      let head := Step.make before valid value
      if supported : head.supported = true then
        let tail ← run head.result.state head.valid packets
        return ⟨tail.final, head :: tail.steps, tail.remaining, .next head supported tail.trace⟩
      else
        have unsupported : head.supported = false := by cases result : head.supported <;> simp_all
        return ⟨head.result.state, [head], packets, .stop head unsupported packets⟩

def Input.check (input : Input) : Except String (Report input) := do
  if valid : input.seed.Valid then
    let result ← run input.seed valid input.packets
    return ⟨result.final, result.steps, result.remaining, valid, result.trace⟩
  else throw "The TCP seed must satisfy the receive buffer, send span, tuple, and cursor limits."

def Report.supported (report : Report input) : Bool := report.steps.all Step.supported

theorem Trace.chain (trace : Trace initial packets steps final remaining) : Chain initial steps final := by
  induction trace with
  | done state => exact .nil state
  | stop head unsupported tail => exact .cons head (.nil head.result.state)
  | next head supported rest ih => exact .cons head ih

theorem Trace.covered (trace : Trace initial packets steps final remaining) :
    steps.map (fun step => step.input.bytes) ++ remaining = packets := by
  induction trace with
  | done state => rfl
  | stop head unsupported tail => rfl
  | next head supported rest ih => simpa only [List.map_cons, List.cons_append, List.cons.injEq, true_and] using ih

theorem Chain.valid (chain : Chain initial steps final) (valid : initial.Valid) : final.Valid := by
  induction chain with
  | nil state => exact valid
  | cons head rest ih => exact ih head.valid

theorem Report.final_valid (report : Report input) : report.final.Valid := report.trace.chain.valid report.seedValid

theorem Chain.prefix (chain : Chain initial steps final) (step : Step) (member : step ∈ steps) :
    ∃ prior later, steps = prior ++ step :: later ∧ Chain initial prior step.before ∧
      Chain step.result.state later final := by
  induction chain with
  | nil state => simp at member
  | @cons tail final head rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨[], tail, rfl, .nil step.before, rest⟩
    · obtain ⟨prior, later, same, preceding, following⟩ := ih member
      exact ⟨head :: prior, later, by simp [same], .cons head preceding, following⟩

theorem Report.step_origin (report : Report input) (step : Step) (member : step ∈ report.steps) :
    ∃ prior later,
      report.steps = prior ++ step :: later ∧ Chain input.seed prior step.before ∧
      input.packets = prior.map (fun item => item.input.bytes) ++
        step.input.bytes :: (later.map (fun item => item.input.bytes) ++ report.remaining) ∧
      Protocol.TCP.decodeIPv4 step.input.bytes = .ok step.input.packet ∧
      step.result = Model.receive step.before step.input := by
  obtain ⟨prior, later, same, preceding, following⟩ := report.trace.chain.prefix step member
  refine ⟨prior, later, same, preceding, ?_, step.input.checked, step.computed⟩
  rw [← report.trace.covered, same, List.map_append]
  simp

theorem Step.received (step : Step) :
    step.result.state.received = step.before.received ++ step.acceptedPayload := by
  cases selected : step.result.decision with
  | blocked reason =>
    have blocked := Protocol.TCP.EstablishedReceive.receive_blocked_preserves step.before step.input reason
      (by rw [← step.computed]; exact selected)
    rw [← step.computed] at blocked
    simp [Step.acceptedPayload, selected, blocked]
  | accepted count size =>
    have received := Protocol.TCP.EstablishedReceive.receive_payload step.before step.input count size
      (by rw [← step.computed]; exact selected)
    rw [← step.computed] at received
    simpa only [Step.acceptedPayload, selected] using received.1

theorem Chain.received (chain : Chain initial steps final) :
    final.received = initial.received ++ steps.flatMap Step.acceptedPayload := by
  induction chain with
  | nil state => simp
  | cons head rest ih =>
    rw [ih, head.received]
    simp [List.append_assoc]

theorem Report.received_prefix (report : Report input) :
    report.final.received = input.seed.received ++ report.steps.flatMap Step.acceptedPayload := report.trace.chain.received

theorem Trace.supported_remaining (trace : Trace initial packets steps final remaining)
    (supported : steps.all Step.supported = true) : remaining = [] := by
  induction trace with
  | done state => rfl
  | stop head unsupported tail => simp [unsupported] at supported
  | next head allowed rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at supported
    exact ih supported.2

theorem Report.supported_covered (report : Report input) (supported : report.supported = true) :
    report.remaining = [] ∧ report.steps.map (fun step => step.input.bytes) = input.packets := by
  have empty := report.trace.supported_remaining supported
  exact ⟨empty, by simpa only [empty, List.append_nil] using report.trace.covered⟩

theorem Trace.unsupported_last (trace : Trace initial packets steps final remaining)
    (step : Step) (member : step ∈ steps) (unsupported : step.supported = false) :
    ∃ prior, steps = prior ++ [step] := by
  induction trace with
  | done state => simp at member
  | stop head blocked tail =>
    have same : step = head := by simpa using member
    subst step
    exact ⟨[], rfl⟩
  | next head supported rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · simp [supported] at unsupported
    · obtain ⟨prior, same⟩ := ih member
      exact ⟨head :: prior, by simp [same]⟩

theorem Report.unsupported_last (report : Report input) (step : Step) (member : step ∈ report.steps)
    (unsupported : step.supported = false) : ∃ prior, report.steps = prior ++ [step] :=
  report.trace.unsupported_last step member unsupported

theorem Report.unsupported_stop (report : Report input) (unsupported : report.supported = false) :
    ∃ prior step reason,
      report.steps = prior ++ [step] ∧ step.result.decision = .blocked (.unsupported reason) := by
  obtain ⟨step, member, notSupported⟩ := List.all_eq_false.mp unsupported
  have blocked : step.supported = false := by cases result : step.supported <;> simp_all
  obtain ⟨prior, same⟩ := report.unsupported_last step member blocked
  cases selected : step.result.decision with
  | accepted count size => simp [Step.supported, selected] at blocked
  | blocked reason =>
    cases reason with
    | reject reason => simp [Step.supported, selected] at blocked
    | unsupported reason => exact ⟨prior, step, reason, same, selected⟩

def stateJson (state : Model.State) : Lean.Json := Lean.Json.mkObj [
  ("inbound", Import.PacketFields.headerJson state.inbound),
  ("receiveNext", Lean.toJson state.receiveNext.val), ("capacity", Lean.toJson state.capacity),
  ("receivedHex", Lean.toJson (Import.EAPOL.bytesToHex state.received)), ("window", Lean.toJson state.window),
  ("sendUna", Lean.toJson state.sendUna.val), ("sendNext", Lean.toJson state.sendNext.val),
  ("sentHex", Lean.toJson (Import.EAPOL.bytesToHex state.sent))]

private def rejectName : Model.Reject → String
  | .invalidSeed => "invalidSeed" | .tuple => "tuple" | .sequence => "sequence"
  | .missingAck => "missingAck" | .acknowledgment => "acknowledgment"

private def unsupportedName : Model.Unsupported → String
  | .reset => "reset" | .synchronize => "synchronize" | .finish => "finish" | .urgent => "urgent"
  | .congestion => "congestion" | .options => "options" | .trimming => "trimming" | .outOfOrder => "outOfOrder"

def decisionJson : Model.Decision → Lean.Json
  | .accepted acknowledged received => Lean.Json.mkObj [
      ("kind", Lean.toJson "accepted"), ("acknowledged", Lean.toJson acknowledged), ("received", Lean.toJson received)]
  | .blocked (.reject reason) => Lean.Json.mkObj [("kind", Lean.toJson "reject"), ("reason", Lean.toJson (rejectName reason))]
  | .blocked (.unsupported reason) => Lean.Json.mkObj [
      ("kind", Lean.toJson "unsupported"), ("reason", Lean.toJson (unsupportedName reason))]

private def ackKindName : Model.AckKind → String
  | .sequence => "sequence" | .challenge => "challenge" | .data => "data"

def ackJson : Option Model.AckRequest → Lean.Json
  | none => .null
  | some ack => Lean.Json.mkObj [("kind", Lean.toJson (ackKindName ack.kind)),
      ("sequence", Lean.toJson ack.sequence.val), ("acknowledgment", Lean.toJson ack.acknowledgment.val),
      ("window", Lean.toJson ack.window)]

def decodedJson (packet : Protocol.TCP.DecodedIPv4) : Lean.Json := Lean.Json.mkObj [
  ("header", Import.PacketFields.headerJson packet.header), ("ttl", Lean.toJson packet.ip.packet.ttl.toNat),
  ("tos", Lean.toJson packet.ip.packet.tos.toNat), ("identification", Lean.toJson packet.ip.packet.identification.val),
  ("dontFragment", Lean.toJson packet.ip.packet.dontFragment), ("ipv4Checksum", Lean.toJson packet.ip.checksum.val),
  ("ipv4PaddingHex", Lean.toJson (Import.EAPOL.bytesToHex packet.ip.padding)),
  ("segment", Check.TCP.segmentJson packet.segment)]

def Step.renderJson (step : Step) (index : Nat) : Lean.Json := Lean.Json.mkObj [
  ("index", Lean.toJson index), ("rawIPv4Hex", Lean.toJson (Import.EAPOL.bytesToHex step.input.bytes)),
  ("decoded", decodedJson step.input.packet), ("before", stateJson step.before),
  ("decision", decisionJson step.result.decision), ("ack", ackJson step.result.ack),
  ("state", stateJson step.result.state)]

def assumptions : List String := [
  "The caller supplies the initial state and sent-byte buffer. The caller assumes that the endpoint transmitted these buffer bytes.",
  "The seed does not prove a handshake or earlier packet transmission.",
  "Window scaling, timestamps, and other extensions are not negotiated.",
  "The selected MAX.SND.WND value is 65535.",
  "The peer window does not set the local receive capacity.",
  "PSH has no effect in this receive projection. Send-window updates remain outside the projection.",
  "An ACK request is not a transmitted packet. ACK scheduling and rate limits remain outside the projection.",
  "An Unsupported result stops transport decoding and state transitions before the next input.",
  "The remaining hex strings have valid hex syntax. The checker does not decode the remaining IPv4 and TCP bytes.",
  "The report does not establish conntrack acceptance, native kernel behavior, retransmission, or eventual delivery."]

def sources : List Standards.Source := [
  ⟨"Transmission Control Protocol", "RFC 9293", "3.4 and 3.10.7.4",
    "https://www.rfc-editor.org/rfc/rfc9293.html#section-3.10.7.4"⟩,
  ⟨"Improving TCP's Robustness to Blind In-Window Attacks", "RFC 5961", "5.2",
    "https://www.rfc-editor.org/rfc/rfc5961.html#section-5.2"⟩]

def Report.renderJson (report : Report input) : Lean.Json := Lean.Json.mkObj [
  ("scope", Lean.toJson "tcp-established-receive-projection"), ("supported", Lean.toJson report.supported),
  ("inputPackets", Lean.toJson input.packets.length), ("evaluatedPackets", Lean.toJson report.steps.length),
  ("seed", stateJson input.seed), ("steps", Lean.toJson (report.steps.zipIdx.map fun (step, index) => step.renderJson index)),
  ("remainingPacketsHex", Lean.toJson (report.remaining.map Import.EAPOL.bytesToHex)),
  ("final", stateJson report.final), ("finalStateValid", Lean.toJson true), ("assumptions", Lean.toJson assumptions),
  ("sources", Lean.toJson (sources.map fun source => Lean.Json.mkObj [
    ("document", Lean.toJson source.document), ("version", Lean.toJson source.version),
    ("clause", Lean.toJson source.clause), ("url", Lean.toJson source.url)]))]

def Report.render (report : Report input) : String :=
  (if report.supported then "TCP RECEIVE PROFILE SUPPORTED\n" else "TCP RECEIVE PROFILE UNSUPPORTED\n") ++ report.renderJson.pretty

end Netlib.Check.TCPReceive
