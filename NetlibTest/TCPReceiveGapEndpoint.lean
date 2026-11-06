import Netlib.Protocol.TCP.Endpoint

namespace NetlibTest.TCPReceiveGapEndpoint

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

private def payload (start count : Nat) : List UInt8 :=
  (List.range count).map fun offset => UInt8.ofNat ((start + offset) % 251)

private def accepted (result : Endpoint.Result) (expected : Endpoint.Accepted) : IO Endpoint.State := do
  ensure (result.decision == .accepted expected) s!"The actual endpoint operation failed: {repr result.decision}."
  ensure (decide result.state.Valid && decide result.state.StorageValid &&
      decide (Endpoint.RecoveryCoherent result.state) && decide (Endpoint.AckCoherent result.state) &&
      decide (Endpoint.StorageCoherent result.state))
    "The accepted endpoint must retain its buffer, timer, ACK, and reservation bounds."
  return result.state

private def output (result : Endpoint.Result) : IO EstablishedReceive.Input :=
  match result.output with
  | some value => pure value
  | none => throw (IO.userError "The actual endpoint output is missing.")

private def recovery (state : Endpoint.State) : IO Recovery.State :=
  match state.recovery with
  | some value => pure value
  | none => throw (IO.userError "The endpoint recovery state is missing.")

private def reaction (state : Endpoint.State) : IO AckReaction.State :=
  match state.ackReaction with
  | some value => pure value
  | none => throw (IO.userError "The endpoint ACK state is missing.")

private def enable (state : Endpoint.State) : IO Endpoint.State := do
  let timed ← accepted (Endpoint.enableRecovery state) .enableRecovery
  let selected ← accepted (Endpoint.enableAck timed) .enableAck
  accepted (Endpoint.advanceClock selected 100) .advanceClock

private def retryFillsGap : IO Unit := do
  let source ← enable client
  let target ← enable server
  let firstBytes := payload 17 400
  let lastBytes := payload 31 400
  let written ← accepted (Endpoint.write source (firstBytes ++ lastBytes)) (.write 800)
  let first := Endpoint.send written 400 true
  let firstState ← accepted first (.send 400)
  let firstPacket ← output first
  let second := Endpoint.send firstState 400 true
  let secondState ← accepted second (.send 400)
  let secondPacket ← output second
  let flight ← recovery secondState
  ensure (Recovery.flight flight == 800 && flight.outstanding.map (·.count) == [400, 400] &&
      flight.deadline == some 1100 && secondState.core.sendNext == Seq.ofNat 900)
    "Two actual partial sends must fit one MSS and share the earliest timer."
  let held ← accepted (Endpoint.receive target secondPacket) (.receive 0 400)
  let heldWork ← reaction held
  ensure (held.core == target.core && held.receiveStore.heldBytes == 400 &&
      held.physicalFree == 1200 && held.reservationFree == 1600 &&
      Endpoint.offeredWindow held == 1600 && heldWork.window == 1600 &&
      heldWork.credit == 1 && heldWork.due == some 100 && heldWork.work.pending.length == 1 &&
      heldWork.work.pending[0]?.map (·.demand.bytes) == some 400)
    "A held suffix must consume physical space and request immediate feedback without shrinking the offered span."
  let feedback := Endpoint.dispatchAck held true
  let answered ← accepted feedback .dispatchAck
  let feedbackPacket ← output feedback
  ensure (feedbackPacket.packet.segment.acknowledgment == Seq.ofNat 100 &&
      feedbackPacket.packet.segment.window.val == 1600)
    "The actual gap ACK must retain the cumulative cursor and offered right edge."
  let duplicated ← accepted (Endpoint.receive secondState feedbackPacket) (.receive 0 0)
  let duplicateTimer ← recovery duplicated
  ensure (duplicateTimer.duplicateAcks == 1 && Recovery.flight duplicateTimer == 800 &&
      duplicateTimer.deadline == some 1100 && duplicated.core.sent == firstBytes ++ lastBytes)
    "The actual unchanged-window feedback must classify one duplicate ACK without retiring data."
  let due ← accepted (Endpoint.advanceClock duplicated 1100) .advanceClock
  let retry := Endpoint.timeout due true
  let retried ← accepted retry (.retry 400)
  let retryPacket ← output retry
  let retryTimer ← recovery retried
  ensure (retryPacket.packet.segment.sequence == firstPacket.packet.segment.sequence &&
      retryPacket.packet.segment.payload == firstPacket.packet.segment.payload &&
      retried.core.sendNext == secondState.core.sendNext && Recovery.flight retryTimer == 800 &&
      retryTimer.outstanding[0]?.map (·.retried) == some true)
    "The actual timeout must repeat the first outstanding range without adding new stream bytes."
  let receiverDue ← accepted (Endpoint.advanceClock answered 1100) .advanceClock
  let filled ← accepted (Endpoint.receive receiverDue retryPacket) (.receive 0 400)
  let detail := Endpoint.receiveEffect receiverDue retryPacket
  let filledWork ← reaction filled
  ensure (filled.core.received == firstBytes ++ lastBytes && filled.core.receiveNext == Seq.ofNat 900 &&
      filled.receiveStore.held.isEmpty && filled.receiveStore.frontier == 800 &&
      detail.runs.map (·.receipt) == [1, 0] && detail.runs.map (·.metadata.receivedAt) == [1100, 100] &&
      detail.runs.map (·.metadata.segment) == [retryPacket.packet.segment, secondPacket.packet.segment] &&
      detail.stored.map (·.novel) == some 400 && ReceiveStore.size detail.runs == 800)
    "The actual retry must release 800 ordered bytes from two receipts while adding only 400 novel bytes."
  ensure (filledWork.credit == 1 && filledWork.work.pending.length == 1 && filledWork.due == some 1100 &&
      filledWork.dataBytes == 400 && filledWork.work.pending[0]?.map (·.demand.bytes) == some 400 &&
      filledWork.work.pending[0]?.map (·.demand.position) == some 800)
    "One gap-filling packet must create one immediate cause with its own novel-byte count."
  let cumulative := Endpoint.dispatchAck filled true
  let replied ← accepted cumulative .dispatchAck
  let cumulativePacket ← output cumulative
  ensure (cumulativePacket.packet.segment.acknowledgment == Seq.ofNat 900 &&
      cumulativePacket.packet.segment.window.val == 800)
    "One actual cumulative ACK must cover both source ranges."
  let complete ← accepted (Endpoint.receive retried cumulativePacket) (.receive 800 0)
  let completeTimer ← recovery complete
  let completeWork ← reaction complete
  ensure (complete.core.sent.isEmpty && complete.core.sendUna == Seq.ofNat 900 &&
      Recovery.flight completeTimer == 0 && completeTimer.deadline.isNone && completeTimer.estimator.isNone &&
      completeTimer.lastSample.isNone && completeTimer.rto == 2000 && completeWork.credit == 0)
    "The actual cumulative receipt must retire 800 bytes, stop the timer, and retain Karn exclusion."
  let read := Endpoint.read replied 800
  let readState ← accepted read (.read 800)
  ensure (read.read == firstBytes ++ lastBytes && readState.core.received.isEmpty &&
      (Endpoint.read readState 1).decision == .reject .readBounds)
    "The application must read the ordered 800-byte result once."
  let update := Endpoint.dispatchAck readState true
  let _ ← accepted update .dispatchAck
  pure ()

private def deferredReceiptTime : IO Unit := do
  let source ← enable client
  let target ← enable server
  let forward := payload 17 400 ++ payload 31 400
  let reverse := payload 71 600 ++ payload 83 600
  let written ← accepted (Endpoint.write source forward) (.write 800)
  let first := Endpoint.send written 400 true
  let firstState ← accepted first (.send 400)
  let firstPacket ← output first
  let reverseWritten ← accepted (Endpoint.write target reverse) (.write 1200)
  let reverseFirst := Endpoint.send reverseWritten 600 true
  let reverseFirstState ← accepted reverseFirst (.send 600)
  let reverseSecond := Endpoint.send reverseFirstState 600 true
  let reverseSecondState ← accepted reverseSecond (.send 600)
  let sourceLater ← accepted (Endpoint.advanceClock firstState 150) .advanceClock
  let sourceReceived ← accepted (Endpoint.receive sourceLater (← output reverseFirst)) (.receive 0 600)
  let second := Endpoint.send sourceReceived 400 true
  let secondState ← accepted second (.send 400)
  let secondPacket ← output second
  let sourceWork ← reaction secondState
  ensure (firstPacket.packet.segment.acknowledgment == Seq.ofNat 200 &&
      secondPacket.packet.segment.acknowledgment == Seq.ofNat 800 && sourceWork.credit == 0)
    "The later actual data output must piggyback feedback for the first reverse receipt."
  let targetLater ← accepted (Endpoint.advanceClock reverseSecondState 150) .advanceClock
  let held ← accepted (Endpoint.receive targetLater secondPacket) (.receive 0 400)
  let heldTimer ← recovery held
  ensure (Recovery.flight heldTimer == 1200 && heldTimer.lastSample.isNone &&
      heldTimer.deadline == some 1100 && held.core.sendUna == Seq.ofNat 200)
    "The advancing ACK in held data must remain unapplied before the missing prefix arrives."
  let feedback := Endpoint.dispatchAck held true
  let answered ← accepted feedback .dispatchAck
  let _ ← accepted (Endpoint.receive secondState (← output feedback)) (.receive 0 0)
  let processing ← accepted (Endpoint.advanceClock answered 1100) .advanceClock
  let released ← accepted (Endpoint.receive processing firstPacket) (.receive 600 400)
  let detail := Endpoint.receiveEffect processing firstPacket
  let sampled ← recovery released
  ensure (detail.headers.map (·.acknowledged) == [0, 600] &&
      detail.runs.map (·.metadata.receivedAt) == [1100, 150] &&
      sampled.lastSample.map (·.sentAt) == some 100 && sampled.lastSample.map (·.acknowledgedAt) == some 150 &&
      sampled.lastSample.map (·.elapsed) == some 50 && sampled.estimator.isSome && sampled.now == 1100 &&
      Recovery.flight sampled == 600 && sampled.deadline == some 2100 &&
      released.core.sent == payload 83 600 && released.core.sendUna == Seq.ofNat 800 &&
      released.core.received == forward)
    "Queued ACK sampling must use its actual arrival time while the remaining timer uses the current processing clock."
  let work ← reaction released
  ensure (work.credit == 1 && work.due == some 1100 && work.work.pending[0]?.map (·.demand.bytes) == some 400)
    "A delayed gap release must still create one timely local response cause."
  let _ ← accepted (Endpoint.dispatchAck released true) .dispatchAck
  pure ()

def run : IO Unit := do
  retryFillsGap
  deferredReceiptTime
  IO.println "Checked endpoint gap recovery tests passed."

end NetlibTest.TCPReceiveGapEndpoint
