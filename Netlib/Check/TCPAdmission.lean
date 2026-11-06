import Netlib.Check.TCPReceive
import Netlib.Check.TCPAdmissionJSON
import Netlib.Check.ConntrackLifecycle
import Netlib.Protocol.TCP.CheckpointCoverageFacts

/-!
# Raw gateway admission from empty state

Checked packets construct the startup and observation history.
The declared mapping uses fixed permit routes. No endpoint-write or authentication claim follows.
-/

namespace Netlib.Check.TCPAdmission

open Packet Protocol
namespace C
export TCP.Checkpoint (Gateway Transition Error History)
end C

structure Input where
  zone : Nat
  original : Header
  translated : Header
  packets : List (List UInt8)

def Input.entry (input : Input) : NetfilterNAT.Entry :=
  ⟨⟨input.original, input.translated.reverse, input.zone, input.zone, 0⟩, true, true⟩

def Input.pipeline (input : Input) : ConntrackLifecycle.Pipeline := {
  routes := [⟨⟨input.translated.destination, 32⟩, some "server"⟩, ⟨⟨input.original.source, 32⟩, some "client"⟩]
  forward := []
  forwardDefault := .permit }

def Input.request (input : Input) (before : C.Gateway) (packet : TCP.EstablishedReceive.Input) : TCP.Checkpoint.Request :=
  ⟨packet, input.zone,
    if (before.tracker.model.lookup input.zone packet.packet.header).isSome then none else some input.entry⟩

def Input.fromJson (json : Lean.Json) : Except String Input := do
  Import.PacketFields.fields json ["schema", "zone", "original", "translated", "packetsHex"]
  if (← (← json.getObjVal? "schema").getNat?) != 1 then throw "Use TCP gateway admission schema 1."
  let original ← Import.PacketFields.header (← json.getObjVal? "original")
  let translated ← Import.PacketFields.header (← json.getObjVal? "translated")
  if original.protocol != Packet.Protocol.tcp || translated.protocol != Packet.Protocol.tcp then
    throw "Both mapping headers must use TCP."
  let zone ← (← json.getObjVal? "zone").getNat?
  let packets ← (← (← json.getObjVal? "packetsHex").getArr?).toList.mapM fun value => do
    Import.EAPOL.bytesFromHex (← value.getStr?)
  let input : Input := ⟨zone, original, translated, packets⟩
  if input.entry.Compatible then return input
  else throw "The declared TCP mapping must have compatible endpoint fields."

def Input.parse (text : String) : Except String Input := do Input.fromJson (← Import.Json.parse text)

structure Step (input : Input) where
  before : C.Gateway
  packet : TCP.EstablishedReceive.Input
  result : Except C.Error (C.Transition before)
  computed : result = TCP.Checkpoint.run before input.pipeline (input.request before packet)

def Step.make (input : Input) (before : C.Gateway) (packet : TCP.EstablishedReceive.Input) : Step input :=
  ⟨before, packet, TCP.Checkpoint.run before input.pipeline (input.request before packet), rfl⟩

def Step.after (step : Step input) : C.Gateway :=
  match step.result with | .ok transition => transition.after | .error _ => step.before

def Step.supported (step : Step input) : Bool := step.result.isOk

def Step.history (step : Step input) (history : C.History step.before) : C.History step.after := by
  unfold Step.after
  cases found : step.result with
  | ok transition => exact .advance history transition
  | error reason => exact history

inductive Trace (input : Input) : C.Gateway → List (List UInt8) → List (Step input) →
    C.Gateway → List (List UInt8) → Type where
  | done (state : C.Gateway) : Trace input state [] [] state []
  | stop (head : Step input) (stopped : head.supported = false) (tail : List (List UInt8)) :
      Trace input head.before (head.packet.bytes :: tail) [head] head.after tail
  | next (head : Step input) (supported : head.supported = true)
      (tail : Trace input head.after packets steps final remaining) :
      Trace input head.before (head.packet.bytes :: packets) (head :: steps) final remaining

structure Report (input : Input) where
  final : C.Gateway
  steps : List (Step input)
  remaining : List (List UInt8)
  trace : Trace input TCP.Checkpoint.Gateway.initial input.packets steps final remaining

private structure Prefix (input : Input) (before : C.Gateway) (packets : List (List UInt8)) where
  final : C.Gateway
  steps : List (Step input)
  remaining : List (List UInt8)
  trace : Trace input before packets steps final remaining

private def run (input : Input) (before : C.Gateway) :
    (packets : List (List UInt8)) → Except String (Prefix input before packets)
  | [] => .ok ⟨before, [], [], .done before⟩
  | raw :: packets => do
    match decoded : TCP.decodeIPv4 raw with
    | .error reason => throw reason
    | .ok packet =>
      let checked : TCP.EstablishedReceive.Input := ⟨raw, packet, decoded⟩
      let head := Step.make input before checked
      if supported : head.supported = true then
        let tail ← run input head.after packets
        return ⟨tail.final, head :: tail.steps, tail.remaining, .next head supported tail.trace⟩
      else
        have stopped : head.supported = false := by cases found : head.supported <;> simp_all
        return ⟨head.after, [head], packets, .stop head stopped packets⟩

def Input.check (input : Input) : Except String (Report input) := do
  let result ← run input TCP.Checkpoint.Gateway.initial input.packets
  return ⟨result.final, result.steps, result.remaining, result.trace⟩

def Report.supported (report : Report input) : Bool := report.steps.all Step.supported

def Trace.history : Trace input initial packets steps final remaining → C.History initial → C.History final
  | .done _, history => history
  | .stop head _ _, history => head.history history
  | .next head _ tail, history => tail.history (head.history history)

def Report.history (report : Report input) : C.History report.final := report.trace.history .initial

theorem Trace.covered (trace : Trace input initial packets steps final remaining) :
    steps.map (fun step => step.packet.bytes) ++ remaining = packets := by
  induction trace with
  | done state => rfl
  | stop head stopped tail => rfl
  | next head supported tail ih => simpa only [List.map_cons, List.cons_append, List.cons.injEq, true_and] using ih

theorem Report.coverage_sources (report : Report input) : report.final.admission.CoverageSources :=
  report.history.coverage_sources

def stateJson (state : C.Gateway) : Lean.Json := Lean.Json.mkObj [
  ("tracker", Check.ConntrackLifecycle.stateJson state.tracker),
  ("admission", TCPAdmissionJSON.admissionJson state.admission)]

private def unsupportedName : TCP.Admission.Unsupported → String
  | .missingHistory => "missingHistory" | .replacement => "replacement" | .direction => "direction"
  | .flags => "flags" | .options => "options" | .data => "data" | .sequence => "sequence"
  | .acknowledgment => "acknowledgment" | .window => "window" | .epoch => "epoch" | .historyLost => "historyLost"
  | .overlap => "overlap" | .conflict => "conflict"

def Step.decisionJson (step : Step input) : Lean.Json :=
  match step.result with
  | .ok _ => Lean.Json.mkObj [("kind", Lean.toJson "accepted")]
  | .error reason => Lean.Json.mkObj [("kind", Lean.toJson "unsupported"),
      ("reason", Lean.toJson (match reason with
        | .admission (.unsupported stopped) => unsupportedName stopped
        | _ => reason.message))]

def Step.renderJson (step : Step input) (index : Nat) : Lean.Json := Lean.Json.mkObj [
  ("index", Lean.toJson index), ("decoded", TCPReceive.decodedJson step.packet.packet),
  ("before", stateJson step.before), ("decision", step.decisionJson),
  ("outputHex", match step.result with
    | .error _ => .null
    | .ok transition => (transition.outcome.output.map fun output =>
        Lean.toJson (Import.EAPOL.bytesToHex output.bytes)).getD .null),
  ("after", stateJson step.after)]

def assumptions : List String := [
  "Raw packets are supplied inputs. This report does not derive endpoint writes or campus authentication.",
  "The NAT mapping is declared. The checker uses fixed permit routes to the two declared data endpoints.",
  "The checked trace starts with empty tracking and admission state.",
  "The remaining hex strings have valid syntax. Later transport bytes are not decoded after a selected stop.",
  "Gateway observation coverage is distinct from endpoint receive storage.",
  "This selected model does not prove native TCP tracking or eventual delivery."]

def Report.renderJson (report : Report input) : Lean.Json := Lean.Json.mkObj [
  ("scope", Lean.toJson "tcp-gateway-admission"), ("supported", Lean.toJson report.supported),
  ("inputPackets", Lean.toJson input.packets.length), ("evaluatedPackets", Lean.toJson report.steps.length),
  ("initial", stateJson TCP.Checkpoint.Gateway.initial),
  ("steps", Lean.toJson (report.steps.zipIdx.map fun (step, index) => step.renderJson index)),
  ("final", stateJson report.final),
  ("remainingPacketsHex", Lean.toJson (report.remaining.map Import.EAPOL.bytesToHex)),
  ("assumptions", Lean.toJson assumptions)]

def Report.render (report : Report input) : String :=
  (if report.supported then "TCP GATEWAY ADMISSION SUPPORTED\n" else "TCP GATEWAY ADMISSION OUTSIDE PROFILE\n") ++
    report.renderJson.pretty

end Netlib.Check.TCPAdmission
