import Netlib.Protocol.TCP.EndpointReceiveEnabled
import Netlib.Protocol.TCP.EndpointAckReceiveEnabled

namespace NetlibTest.TCPReceiveEnabled

open Netlib Packet Protocol TCP

private def ghostTail : Recovery.State := {
  Recovery.sent (Recovery.initial 800) 1 with
  outstanding := [⟨0, 0, 1, 0, 0, false⟩, ⟨1, 1, 0, 0, 0, false⟩]
  nextId := 2 }

example : ghostTail.Valid ∧ ¬ghostTail.Positive ∧
    (Recovery.acknowledgeState ghostTail (Recovery.flight ghostTail)).outstanding ≠ [] := by decide

example (state : Recovery.State) (entry : Recovery.Outstanding) (rest : List Recovery.Outstanding) (deadline : Nat)
    (source : state.outstanding = entry :: rest) (timer : state.deadline = some deadline)
    (positive : 0 < entry.count) (due : deadline ≤ state.now) (elapsed : entry.lastAt + state.rto ≤ state.now)
    (remaining : state.lastTimedOut = some entry.id → state.timeoutCount < 2) :
    Recovery.timeout state = .ok (entry.count, Recovery.timeoutState state entry rest) :=
  Recovery.timeout_of_due state entry rest deadline source timer positive due elapsed remaining

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def verify (property : Prop) [Decidable property] (message : String) : IO { _value : Unit // property } :=
  load (if accepted : property then .ok ⟨(), accepted⟩ else .error message)

private def client (start : Nat) : Endpoint.State := {
  core := ⟨⟨3325256706, 3221225985, Packet.Protocol.tcp, 9000, 41000⟩,
    Seq.ofNat 200, 1600, [], Seq.ofNat start, Seq.ofNat start, []⟩
  pending := [], pendingLimit := 3200, sendWindow := 1600,
  sendWL1 := Seq.ofNat 200, sendWL2 := Seq.ofNat start, effectiveMSS := 800, ipSendLimit := 1500
  localReceiveMSS := .present ⟨⟨1200, by decide⟩, by decide⟩ }

private def server (start : Nat) : Endpoint.State := {
  core := ⟨⟨3221225985, 3325256706, Packet.Protocol.tcp, 41000, 9000⟩,
    Seq.ofNat start, 1600, [], Seq.ofNat 200, Seq.ofNat 200, []⟩
  pending := [], pendingLimit := 3200, sendWindow := 1600,
  sendWL1 := Seq.ofNat start, sendWL2 := Seq.ofNat 200, effectiveMSS := 1200, ipSendLimit := 1500
  localReceiveMSS := .present ⟨⟨800, by decide⟩, by decide⟩ }

private def accepted (result : Endpoint.Result) (expected : Endpoint.Accepted) : IO Endpoint.State := do
  ensure (result.decision == .accepted expected) s!"The actual endpoint action failed: {repr result.decision}."
  return result.state

private def enable (state : Endpoint.State) : IO Endpoint.State := do
  let timed ← accepted (Endpoint.enableRecovery state) .enableRecovery
  let active ← accepted (Endpoint.enableAck timed) .enableAck
  accepted (Endpoint.advanceClock active 100) .advanceClock

private def output (result : Endpoint.Result) : IO EstablishedReceive.Input :=
  match result.output with
  | some packet => pure packet
  | none => throw (IO.userError "The actual output is absent.")

private def proveData (state : Endpoint.State) (packet : EstablishedReceive.Input) : IO Unit := do
  match runtime : state.recovery, enabled : state.ackReaction with
  | some recovery, some reaction =>
    let valid ← verify state.Valid "The old endpoint is invalid."
    let coherent ← verify (Endpoint.RecoveryCoherent state) "The old recovery ledger is incoherent."
    let ready ← verify (Endpoint.AckPrepared state) "The old ACK work is not ready."
    let storage ← verify (Endpoint.StorageCoherent state) "The old receive storage is incoherent."
    let sent ← verify (recovery.SentBy recovery.now) "A timing record lies after the actual clock."
    let empty ← verify (state.receiveStore.held = []) "This first profile excludes existing held runs."
    let tuple ← verify (packet.packet.header = state.core.inbound) "The actual tuple differs."
    let controls ← verify (EstablishedReceive.control packet.packet.segment = none) "The actual controls are unsupported."
    let ack ← verify (Flags.ack packet.packet.segment.flags = true) "The packet has no ACK field."
    let sequence ← verify (packet.packet.segment.sequence = state.core.receiveNext) "The packet is not at the actual cursor."
    let nonempty ← verify (packet.packet.segment.payload ≠ []) "The selected data is empty."
    let fits ← verify (packet.packet.segment.payload.length ≤ Endpoint.offeredWindow state) "The whole range exceeds the offered edge."
    let bounded ← verify (Endpoint.inOrderCount state packet ≤ state.core.sent.length) "The ACK exceeds the actual sent bytes."
    let _ := Endpoint.receive_inOrder_emits_ack state packet recovery reaction valid.property coherent.property ready.property
      storage.property runtime enabled sent.property empty.property tuple.property controls.property ack.property sequence.property
      nonempty.property fits.property bounded.property
    pure ()
  | _, _ => throw (IO.userError "Both runtime components must be active.")

private def proveRetirement (state : Endpoint.State) (packet : EstablishedReceive.Input) : IO Unit := do
  match runtime : state.recovery, enabled : state.ackReaction with
  | some recovery, some reaction =>
    let valid ← verify state.Valid "The old sender is invalid."
    let coherent ← verify (Endpoint.RecoveryCoherent state) "The sender ledger is incoherent."
    let ready ← verify (Endpoint.AckPrepared state) "The sender ACK work is not ready."
    let storage ← verify (Endpoint.StorageCoherent state) "The sender receive storage is incoherent."
    let positive ← verify recovery.Positive "The actual outstanding ranges must be nonempty."
    let flight ← verify (0 < state.core.sent.length) "The sender must have actual outstanding bytes."
    let emptyHeld ← verify (state.receiveStore.held = []) "The sender has unrelated held input."
    let tuple ← verify (packet.packet.header = state.core.inbound) "The reverse tuple differs."
    let controls ← verify (EstablishedReceive.control packet.packet.segment = none) "The reverse controls are unsupported."
    let ack ← verify (Flags.ack packet.packet.segment.flags = true) "The reverse packet has no ACK field."
    let sequence ← verify (packet.packet.segment.sequence = state.core.receiveNext) "The reverse packet is outside the receive cursor."
    let empty ← verify (packet.packet.segment.payload = []) "The reverse packet is not a pure ACK."
    let covers ← verify (Endpoint.inOrderCount state packet = state.core.sent.length) "The ACK does not cover the actual flight."
    let _ := Endpoint.receive_empty_full_ack_coherent state packet recovery reaction valid.property coherent.property ready.property
      storage.property runtime enabled positive.property flight.property emptyHeld.property tuple.property controls.property ack.property
      sequence.property empty.property covers.property
    pure ()
  | _, _ => throw (IO.userError "The sender runtime is disabled.")

private def proveOld (state : Endpoint.State) (packet : EstablishedReceive.Input) : IO Unit := do
  match enabled : state.ackReaction with
  | none => throw (IO.userError "ACK feedback is disabled.")
  | some reaction =>
    let valid ← verify state.Valid "The old receiver is invalid."
    let coherent ← verify (Endpoint.RecoveryCoherent state) "The receiver ledger is incoherent."
    let ready ← verify (Endpoint.AckPrepared state) "The receiver ACK work is not ready."
    let storage ← verify (Endpoint.StorageCoherent state) "The receiver storage is incoherent."
    let tuple ← verify (packet.packet.header = state.core.inbound) "The repeated tuple differs."
    let controls ← verify (EstablishedReceive.control packet.packet.segment = none) "The repeated controls are unsupported."
    let nonempty ← verify (packet.packet.segment.payload ≠ []) "The repeated range is empty."
    let ends ← verify (packet.packet.segment.sequence.add packet.packet.segment.payload.length = state.core.receiveNext)
      "The whole repeated range must end at the current cursor."
    let epoch ← verify (packet.packet.segment.payload.length + Endpoint.offeredWindow state ≤ Seq.modulus)
      "The selected repeated epoch is too long."
    let _ := Endpoint.receive_old_whole_range_emits_ack state packet reaction valid.property coherent.property ready.property
      storage.property enabled tuple.property controls.property nonempty.property ends.property epoch.property
    pure ()

private def round (source target : Endpoint.State) (count : Nat) (byte : UInt8) : IO (Endpoint.State × Endpoint.State) := do
  let bytes := List.replicate count byte
  let written ← accepted (Endpoint.write source bytes) (.write count)
  let sent := Endpoint.send written count true
  let sender ← accepted sent (.send count)
  let packet ← output sent
  proveData target packet
  let receipt := Endpoint.receiveEffect target packet
  let receiver ← accepted receipt.result (.receive 0 count)
  ensure (receipt.runs.length == 1 && (ReceiveStore.bytes receipt.runs) == bytes &&
      receiver.receiveStore.frontier == target.receiveStore.frontier + count &&
      receiver.receiveStore.nextID == target.receiveStore.nextID + 1 &&
      receiver.core.received == target.core.received ++ bytes)
    "One actual receipt must release one range and preserve earlier unread bytes."
  let response := Endpoint.emitAck receiver true
  let answered ← accepted response .emitAck
  let ack ← output response
  ensure (ack.packet.segment.payload.isEmpty && ack.packet.segment.acknowledgment == receiver.core.receiveNext)
    "The actual ACK must cover the released cursor."
  proveRetirement sender ack
  let retired := Endpoint.receiveEffect sender ack
  let ready ← accepted retired.result (.receive count 0)
  ensure (retired.runs.isEmpty && ready.core.sent.isEmpty && ready.core.sendUna == sender.core.sendNext &&
      ready.recovery.any (fun state => state.outstanding.isEmpty && state.deadline.isNone && state.timeoutCount == 0) &&
      decide (Endpoint.RecoveryCoherent ready) && decide (Endpoint.StorageCoherent ready))
    "The actual covering ACK must retire all ranges and cancel the timer."
  return (ready, answered)

private def retryFeedback (start count : Nat) : IO Unit := do
  let source ← enable (client start)
  let target ← enable (server start)
  let bytes := List.replicate count 73
  let written ← accepted (Endpoint.write source bytes) (.write count)
  let original := Endpoint.send written count true
  let sender ← accepted original (.send count)
  let first ← output original
  proveData target first
  let received ← accepted (Endpoint.receiveEffect target first).result (.receive 0 count)
  let response := Endpoint.emitAck received true
  let answered ← accepted response .emitAck
  let _ ← output response
  let some timer := sender.recovery | throw (IO.userError "The actual sender timer is absent.")
  let some due := timer.deadline | throw (IO.userError "The actual sender deadline is absent.")
  let elapsed ← accepted (Endpoint.advanceClock sender due) .advanceClock
  let retry := Endpoint.timeout elapsed true
  let retried ← accepted retry (.retry count)
  let packet ← output retry
  proveOld answered packet
  let receipt := Endpoint.receiveEffect answered packet
  ensure (receipt.result.decision == .reject (.input .sequence) && receipt.runs.isEmpty &&
      receipt.result.state.core == answered.core && receipt.result.state.core.received == bytes &&
      receipt.result.state.ackReaction.any (fun state => state.due == some answered.now && state.credit == 1))
    "An undelivered ACK must permit an old-range retry to create immediate feedback without another release."
  let replacement := Endpoint.dispatchAck receipt.result.state true
  let feedback ← accepted replacement .dispatchAck
  let ack ← output replacement
  proveRetirement retried ack
  let done ← accepted (Endpoint.receiveEffect retried ack).result (.receive count 0)
  ensure (done.core.sent.isEmpty && done.recovery.any (fun state => state.deadline.isNone && state.timeoutCount == 0))
    "The replacement ACK must retire the retried range."
  let read := Endpoint.read feedback count
  let _ ← accepted read (.read count)
  ensure (read.read == bytes) "The final read must contain the original bytes once."

def run : IO Unit := do
  for count in [1, 400, 800] do
    let source ← enable (client 100)
    let target ← enable (server 100)
    let _ ← round source target count 42
    retryFeedback 100 count
  for count in [1, 600, 1200] do
    let source ← enable (server 100)
    let target ← enable (client 100)
    let _ ← round source target count 51
  retryFeedback 4294967200 400
  let source ← enable (client 100)
  let target ← enable (server 100)
  let (source, target) ← round source target 400 61
  let (_, target) ← round source target 400 62
  let reader := Endpoint.read target 800
  let _ ← accepted reader (.read 800)
  ensure (reader.read == List.replicate 400 61 ++ List.replicate 400 62 && target.receiveStore.nextID == 2)
    "A later enabled receive must keep the actual nonzero frontier and earlier unread bytes."
  IO.println "Active TCP receive and covering ACK tests passed."

end NetlibTest.TCPReceiveEnabled
