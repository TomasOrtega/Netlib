import Netlib.Protocol.TCP.ApplicationTraceFacts
import Netlib.Protocol.TCP.ControlOutput

namespace NetlibTest.TCPAckEndpoint

open Netlib Packet Protocol TCP

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def client : Endpoint.State := {
  core := ⟨⟨3325256706, 3221225985, Packet.Protocol.tcp, 9000, 41000⟩,
    Seq.ofNat 200, 1600, [], Seq.ofNat 100, Seq.ofNat 100, []⟩
  pending := [], pendingLimit := 3200, sendWindow := 1600,
  sendWL1 := Seq.ofNat 200, sendWL2 := Seq.ofNat 100, effectiveMSS := 800, ipSendLimit := 1500
  localReceiveMSS := .present ⟨⟨1200, by decide⟩, by decide⟩ }

private def server : Endpoint.State := {
  core := ⟨⟨3221225985, 3325256706, Packet.Protocol.tcp, 41000, 9000⟩,
    Seq.ofNat 100, 1600, [], Seq.ofNat 200, Seq.ofNat 200, []⟩
  pending := [], pendingLimit := 3200, sendWindow := 1600,
  sendWL1 := Seq.ofNat 100, sendWL2 := Seq.ofNat 200, effectiveMSS := 1200, ipSendLimit := 1500
  localReceiveMSS := .present ⟨⟨800, by decide⟩, by decide⟩ }

example : (Endpoint.enableAck (Endpoint.enableRecovery server).state).state.ackReaction.map (·.rmss) = some 800 := by
  decide

private def enable (state : Endpoint.State) : IO Endpoint.State := do
  let recovery := Endpoint.enableRecovery state
  ensure (recovery.decision == .accepted .enableRecovery) "Recovery must enable from empty outstanding storage."
  let ack := Endpoint.enableAck recovery.state
  ensure (ack.decision == .accepted .enableAck) "ACK work must start from the existing clock and full receive offer."
  return ack.state

private def packet (result : Endpoint.Result) : IO EstablishedReceive.Input :=
  match result.output with
  | some output => pure output
  | none => throw (IO.userError "The selected operation has no actual checked output.")

private def reaction (state : Endpoint.State) : IO AckReaction.State :=
  match state.ackReaction with
  | some value => pure value
  | none => throw (IO.userError "The selected endpoint has no ACK reaction profile.")

private def partials : IO (Endpoint.State × Endpoint.State × EstablishedReceive.Input) := do
  let source ← enable client
  let target ← enable server
  let written := Endpoint.write source (List.replicate 800 42)
  let first := Endpoint.send written.state 400 true
  ensure (first.decision == .accepted (.send 400)) "The first partial needs an actual new output."
  let firstPacket ← packet first
  let received := Endpoint.receive target firstPacket
  ensure (received.decision == .accepted (.receive 0 400)) "The first partial must enter actual receive storage."
  let firstWork ← reaction received.state
  ensure (firstWork.credit == 1 && firstWork.due == some 499 && firstWork.rmss == 800 &&
      firstWork.window == 1200)
    "ACK RMSS must use the own receive offer and retain the first arrival deadline."
  let later := Endpoint.advanceClock received.state 100
  let second := Endpoint.send first.state 400 true
  let secondPacket ← packet second
  let coalesced := Endpoint.receive later.state secondPacket
  let work ← reaction coalesced.state
  ensure (coalesced.decision == .accepted (.receive 0 400) && work.credit == 2 &&
      work.due == some 499 && work.advertisement.frontier == 800 &&
      work.work.pending.map (·.demand.position) == [400, 800])
    "A second partial must strengthen the cursor without moving the oldest due time."
  return (second.state, coalesced.state, firstPacket)

private def dispatchAndDeadline : IO Unit := do
  let (source, target, _) ← partials
  let early := Endpoint.dispatchAck target true
  ensure (early.decision == .reject (.ack .early) && early.output.isNone && early.state == target)
    "The dispatcher must retain work before it is due."
  let denied := Endpoint.dispatchAck target false
  ensure (denied.decision == .reject .policy && denied.state == target && denied.output.isNone)
    "Local denial must not consume response credit or change the deadline."
  let late := Endpoint.advanceClock target 500
  ensure (late.decision == .ackUnsupported .deadline && late.state == target && late.output.isNone)
    "An outstanding strict deadline must stop a clock jump beyond its due time."
  let atDue := Endpoint.advanceClock target 499
  let dispatched := Endpoint.dispatchAck atDue.state true
  let ack ← packet dispatched
  let done ← reaction dispatched.state
  ensure (dispatched.decision == .accepted .dispatchAck && done.credit == 0 &&
      done.work.completed.length == 1 && done.work.completed[0]?.map (·.time) == some 499 &&
      ack.packet.segment.acknowledgment == Seq.ofNat 900 && ack.packet.segment.window.val == 800 &&
      dispatched.state.recovery == atDue.state.recovery)
    "A due ACK must use actual current fields and preserve the unrelated RTO state."
  let extra := Endpoint.emitAck dispatched.state true
  ensure (extra.decision == .reject (.ack .noCredit) && extra.output.isNone)
    "A completed group must not leave reusable pure-ACK credit."
  let accepted := Endpoint.receive source ack
  let sourceWork ← reaction accepted.state
  ensure (accepted.decision == .accepted (.receive 800 0) && accepted.state.core.sent.isEmpty && sourceWork.credit == 0)
    "Actual ACK receipt must retire sent bytes without creating an ACK loop."

private def piggyback : IO Unit := do
  let (_, target, _) ← partials
  let written := Endpoint.write target [9, 10]
  let sent := Endpoint.send written.state 2 true
  let output ← packet sent
  let work ← reaction sent.state
  ensure (sent.decision == .accepted (.send 2) && work.credit == 0 &&
      output.packet.segment.acknowledgment == Seq.ofNat 900 && output.packet.segment.payload == [9, 10])
    "An actual independent data output must consume its covered ACK group."
  let extra := Endpoint.dispatchAck sent.state true
  ensure (extra.decision == .reject (.ack .noCredit) && extra.output.isNone)
    "Piggyback discharge must prevent an extra pure response."

private def duplicateData : IO Unit := do
  let source ← enable client
  let target ← enable server
  let sent := Endpoint.send (Endpoint.write source [42]).state 1 true
  let input ← packet sent
  let received := Endpoint.receive target input
  let dispatched := Endpoint.emitAck received.state true
  let repeated := Endpoint.receive dispatched.state input
  let work ← reaction repeated.state
  ensure (repeated.decision == .reject (.input .sequence) && repeated.state.core == dispatched.state.core &&
      work.credit == 1 && work.due == some 0)
    "Wholly old data must request immediate cumulative feedback without a second byte delivery."
  let response := Endpoint.dispatchAck repeated.state true
  let output ← packet response
  ensure (response.decision == .accepted .dispatchAck && output.packet.segment.acknowledgment == Seq.ofNat 101 &&
      response.state.core.received == [42])
    "The cumulative response must come from an actual dispatcher output."

private def windowUpdate : IO Unit := do
  let (_, target, _) ← partials
  let responded := Endpoint.emitAck target true
  let small := Endpoint.read responded.state 399
  let work ← reaction small.state
  ensure (small.decision == .accepted (.read 399) && work.credit == 0 &&
      Endpoint.outputWindow small.state == 800 && small.state.core.window == 1199)
    "A small read must free storage without enlarging the offered right edge."
  let noOp := Endpoint.read small.state 0
  let noOpWork ← reaction noOp.state
  ensure (noOpWork.credit == 0) "A zero-byte read must not mint window-update credit."
  let sent := Endpoint.send (Endpoint.write small.state [9]).state 1 true
  let output ← packet sent
  ensure (output.packet.segment.window.val == 800)
    "An unrelated data output must retain the suppressed receive window."
  let opened := Endpoint.read sent.state 401
  let pending ← reaction opened.state
  ensure (pending.credit == 1 && pending.due == some 100 && pending.window == 800 &&
      Endpoint.outputWindow opened.state == 1600)
    "A genuine SWS release must create a read-origin cause before the offered edge changes."
  let dispatched := Endpoint.dispatchAck opened.state true
  let update ← packet dispatched
  let done ← reaction dispatched.state
  ensure (update.packet.segment.window.val == 1600 && done.advertisement.edge == 2400 && done.credit == 0)
    "Only the actual successful window update may commit the larger right edge."

private def fullSegments : IO Unit := do
  let target ← enable server
  let written := Endpoint.write client (List.replicate 1600 42)
  let first := Endpoint.send written.state 800 true
  let firstPacket ← packet first
  let received := Endpoint.receive target firstPacket
  let later := Endpoint.advanceClock received.state 100
  let second := Endpoint.send first.state 800 true
  let secondPacket ← packet second
  let result := Endpoint.receive later.state secondPacket
  let work ← reaction result.state
  ensure (result.decision == .accepted (.receive 0 800) && work.fullSegments == 2 &&
      work.dataBytes == 1600 && work.due == some 100)
    "Two actual RMSS-sized inputs must make their cumulative response immediate."

private def challengeScope : IO Unit := do
  let state ← enable server
  let input ← match ControlOutput.emit state.core.inbound state.core.receiveNext (state.core.sendNext.add 1) 16 1600 with
    | .ok value => pure value
    | .error reason => throw (IO.userError reason)
  let result := Endpoint.receive state input
  ensure (result.decision == .ackUnsupported .challenge && result.state == state && result.output.isNone)
    "Challenge feedback needs its separate throttle and must stop this timed profile."

def run : IO Unit := do
  dispatchAndDeadline
  piggyback
  duplicateData
  windowUpdate
  fullSegments
  challengeScope
  IO.println "Checked TCP ACK endpoint tests passed."

end NetlibTest.TCPAckEndpoint
