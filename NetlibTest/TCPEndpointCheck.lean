import Netlib.Check.TCPEndpoint

namespace NetlibTest.TCPEndpointCheck

open Netlib Protocol TCP
open Netlib.Check.TCPEndpoint

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def present : Option α → IO α
  | some value => pure value
  | none => throw (IO.userError "The output packet is missing.")

private def seed : Endpoint.State := {
  core := ⟨⟨3221225985, 3325256706, Packet.Protocol.tcp, 12345, 80⟩,
    Seq.ofNat 100, 8, [], Seq.ofNat 200, Seq.ofNat 200, []⟩
  pending := [], pendingLimit := 8, sendWindow := 8
  sendWL1 := Seq.ofNat 100, sendWL2 := Seq.ofNat 200
  effectiveMSS := 536, ipSendLimit := 576 }

private def raw (event : Event) : Raw := ⟨event⟩

def run : IO Unit := do
  let input : Input := ⟨seed, [raw (.write [1, 2, 3]), raw (.send 2 true), raw (.send 2 true), raw (.emitAck true)]⟩
  let report ← load input.check
  ensure (report.supported && report.steps.length == 4 && report.remaining.isEmpty &&
      report.final.pending == [3] && report.final.core.sent == [1, 2] && report.final.core.sendNext.val == 202)
    "Mixed replay must retain each computed state after a supported send rejection."
  match report.steps[0]? with
  | some step =>
    let displayed ← load ((step.renderJson 0).getObjVal? "event")
    ensure (displayed == Lean.Json.mkObj [("kind", Lean.toJson "write"), ("payloadHex", Lean.toJson "010203")])
      "A programmatic report must display the actual typed event."
  | none => throw (IO.userError "The write step is missing.")
  match report.steps[1]?, report.steps[3]? with
  | some sent, some ack =>
    let sentOutput ← present sent.typed.result.output
    let ackOutput ← present ack.typed.result.output
    ensure (sentOutput.packet.segment.sequence.val == 200 && sentOutput.packet.segment.payload == [1, 2] &&
        ackOutput.packet.segment.sequence.val == 202 && ackOutput.packet.segment.payload.isEmpty)
      "ACK output must use the current cursor after the actual send event."
  | _, _ => throw (IO.userError "The replay steps are missing.")
  let segment := computed seed.core.inbound.source seed.core.inbound.destination {
    sourcePort := 12345, destinationPort := 80, sequence := Seq.ofNat 100,
    acknowledgment := Seq.ofNat 200, reserved := 0, flags := 20,
    window := 0, checksum := 0, urgentPointer := 0, options := [], payload := [] }
  let reset ← load (IPv4.encode ⟨0, 0, true, 64, Packet.Protocol.tcp,
    seed.core.inbound.source, seed.core.inbound.destination, segment.encodeBytes⟩)
  let stopped : Input := ⟨seed, [raw (.write [1]), raw (.receive reset), raw (.send 1 true), raw (.receive [0])]⟩
  let stop ← load stopped.check
  ensure (!stop.supported && stop.steps.length == 2 && stop.remaining.length == 2 &&
      stop.final.pending == [1] && stop.final.core.sent.isEmpty)
    "Unsupported replay must stop before the later send and invalid transport bytes."
  let guide ← load (Input.parse (← IO.FS.readFile "examples/tcp-endpoint/trace.json"))
  let guideReport ← load guide.check
  ensure (guideReport.supported && guideReport.steps.length == guide.events.length && guideReport.final.core.sent == [102])
    "The guide trace must parse and execute all application events."
  IO.println "TCP application replay tests passed."

end NetlibTest.TCPEndpointCheck
