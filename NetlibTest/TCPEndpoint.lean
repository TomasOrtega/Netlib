import Netlib.Protocol.TCP.Endpoint

namespace NetlibTest.TCPEndpoint

open Netlib Protocol TCP
namespace E
export Netlib.Protocol.TCP.Endpoint (State Result Decision Accepted Reject)
end E

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def tuple : Packet.Header := ⟨3221225986, 3405803778, Packet.Protocol.tcp, 41000, 8080⟩

private def seed : E.State :=
  { core := ⟨tuple, Seq.ofNat 100, 8, [], Seq.ofNat 200, Seq.ofNat 203, [10, 11, 12]⟩
    pending := []
    pendingLimit := 8
    sendWindow := 8
    sendWL1 := Seq.ofNat 100
    sendWL2 := Seq.ofNat 200
    effectiveMSS := 4
    ipSendLimit := 1500 }

private def packet (sequence acknowledgment : Nat) (payload : List UInt8)
    (window : InternetChecksum.Word := 8) (flags : UInt8 := 16)
    (options : List UInt8 := []) : IO EstablishedReceive.Input := do
  let segment := TCP.rechecksum tuple.source tuple.destination {
    sourcePort := tuple.sourcePort, destinationPort := tuple.destinationPort,
    sequence := Seq.ofNat sequence, acknowledgment := Seq.ofNat acknowledgment,
    reserved := 0, flags := flags, window := window, checksum := 0,
    urgentPointer := 0, options := options, payload := payload }
  let ip : IPv4.Packet := ⟨0, 7, true, 64, Packet.Protocol.tcp,
    tuple.source, tuple.destination, segment.encodeBytes⟩
  let bytes ← load (IPv4.encode ip)
  load (EstablishedReceive.input bytes)

private def result (before : E.State) (after : E.Result) (decision : E.Decision) : IO Unit := do
  ensure (after.decision == decision) s!"Unexpected endpoint decision: {repr after.decision}."
  ensure (decide after.state.Valid) "The resulting state must meet the buffer and cursor bounds."
  match decision with
  | .reject _ | .unsupported _ | .recoveryUnsupported _ | .ackUnsupported _ =>
    ensure (after.state == before && after.output.isNone && after.read.isEmpty)
      "A blocked event must keep state and return no output or read bytes."
  | .accepted _ => pure ()

private def applicationOperations : IO Unit := do
  ensure (decide seed.Valid) "The initial state must meet the profile bounds."
  let written := Endpoint.write seed [1, 2, 3, 4, 5]
  result seed written (.accepted (.write 5))
  ensure (written.state.pending == [1, 2, 3, 4, 5] && written.state.core == seed.core)
    "A write must append bytes only to pending storage."
  let rejected := Endpoint.write written.state [6, 7, 8, 9]
  result written.state rejected (.reject .pendingCapacity)
  let full := Endpoint.write written.state [6, 7, 8]
  result written.state full (.accepted (.write 3))
  let sent := Endpoint.send written.state 2 true
  result written.state sent (.accepted (.send 2))
  ensure (sent.state.pending == [3, 4, 5] && sent.state.core.sent == [10, 11, 12, 1, 2] &&
    sent.state.core.sendNext == Seq.ofNat 205 && sent.state.core.sendUna == seed.core.sendUna &&
    sent.state.core.receiveNext == seed.core.receiveNext && sent.state.core.received == seed.core.received)
    "A send must move the exact pending prefix and advance SND.NXT."
  let some output := sent.output | throw (IO.userError "An accepted send must return checked bytes.")
  ensure (output.packet.segment.payload == [1, 2] && output.packet.segment.sequence == Seq.ofNat 203 &&
    output.packet.segment.acknowledgment == Seq.ofNat 100 && output.packet.segment.window == 8 &&
    output.packet.segment.flags == 16 && output.packet.segment.options.isEmpty &&
    output.packet.header == Output.reverse tuple)
    "The output must use current endpoint fields and the selected application bytes."
  let decoded ← load (TCP.decodeIPv4 output.bytes)
  ensure (decoded == output.packet) "The emitted bytes must decode to the certified packet."
  for (count, permit, reason) in [(0, true, Endpoint.Reject.sendBounds), (6, true, .sendBounds),
    (5, true, .sendBounds), (1, false, .policy)] do
    result written.state (Endpoint.send written.state count permit) (.reject reason)
  let maximum := Endpoint.send written.state 4 true
  result written.state maximum (.accepted (.send 4))
  ensure (maximum.state.pending == [5] && maximum.state.core.sent.length == 7)
    "A send can use the exact effective MSS."
  let exhausted := { written.state with sendWindow := 3 }
  result exhausted (Endpoint.send exhausted 1 true) (.reject .sendBounds)
  let buffered := { sent.state with core := { sent.state.core with received := [30, 31, 32, 33] } }
  let read := Endpoint.read buffered 2
  result buffered read (.accepted (.read 2))
  ensure (read.read == [30, 31] && read.state.core.received == [32, 33] &&
    read.state.core.receiveNext == buffered.core.receiveNext && read.state.core.window == buffered.core.window + 2 &&
    read.state.core.sent == buffered.core.sent && read.state.sendWindow == buffered.sendWindow)
    "A read must return the received prefix and increase the local window."
  result buffered (Endpoint.read buffered 5) (.reject .readBounds)
  result buffered (Endpoint.read buffered 0) (.accepted (.read 0))
  let ack := Endpoint.emitAck read.state true
  result read.state ack (.accepted .emitAck)
  let some ackPacket := ack.output | throw (IO.userError "An ACK event must return checked bytes.")
  ensure (ack.state == read.state && ackPacket.packet.segment.payload.isEmpty &&
    ackPacket.packet.segment.window.val == read.state.core.window &&
    ackPacket.packet.segment.sequence == read.state.core.sendNext)
    "An ACK output must read the current state after the application read."
  result read.state (Endpoint.emitAck read.state false) (.reject .policy)
  let invalid := { written.state with effectiveMSS := 0 }
  for after in [Endpoint.write invalid [1], Endpoint.read invalid 0, Endpoint.send invalid 1 true,
    Endpoint.emitAck invalid true] do
    ensure (after.decision == .reject .invalidSeed && after.state == invalid && after.output.isNone && after.read.isEmpty)
      "An invalid initial state must preserve all fields and produce no bytes."

private def windowUpdates : IO Unit := do
  let queued := (Endpoint.write seed [1, 2]).state
  let duplicate ← packet 100 200 [90] 0
  let reduced := Endpoint.receive queued duplicate
  result queued reduced (.accepted (.receive 0 1))
  ensure (reduced.state.sendWindow == 0 && reduced.state.core.sent == queued.core.sent &&
    reduced.state.core.sent.length > reduced.state.sendWindow)
    "A duplicate ACK can reduce the peer window below the outstanding length."
  result reduced.state (Endpoint.send reduced.state 1 true) (.reject .sendBounds)
  let old ← packet 100 199 [91] 0
  let oldResult := Endpoint.receive queued old
  result queued oldResult (.accepted (.receive 0 1))
  ensure (oldResult.state.sendWindow == queued.sendWindow && oldResult.state.sendWL1 == queued.sendWL1 &&
    oldResult.state.sendWL2 == queued.sendWL2)
    "A strictly older ACK can accept data but must preserve peer-window history."
  let forward ← packet 100 201 [] 1
  let advanced := Endpoint.receive queued forward
  result queued advanced (.accepted (.receive 1 0))
  ensure (advanced.state.sendWindow == 1 && advanced.state.core.sent == [11, 12] &&
    advanced.state.sendWL2 == Seq.ofNat 201)
    "A forward ACK must update the window against the state before ACK removal."
  let newerSequence ← packet 101 200 [] 2
  let newer := Endpoint.receive queued newerSequence
  result queued newer (.accepted (.receive 0 0))
  ensure (newer.state.sendWindow == 2 && newer.state.sendWL1 == Seq.ofNat 101)
    "A duplicate ACK with newer sequence history can update the window."
  let olderSequence := { queued with sendWL1 := Seq.ofNat 101 }
  let stale := Endpoint.receive olderSequence duplicate
  result olderSequence stale (.accepted (.receive 0 1))
  ensure (stale.state.sendWindow == olderSequence.sendWindow)
    "Older sequence history must not replace the peer window."
  let newerAckHistory := { queued with sendWL2 := Seq.ofNat 201 }
  let staleAck := Endpoint.receive newerAckHistory duplicate
  result newerAckHistory staleAck (.accepted (.receive 0 1))
  ensure (staleAck.state.sendWindow == newerAckHistory.sendWindow)
    "An older WL2 value must not replace equal WL1 history."
  let laterAck ← packet 100 202 [] 4
  let later := Endpoint.receive newerAckHistory laterAck
  result newerAckHistory later (.accepted (.receive 2 0))
  ensure (later.state.sendWindow == 4 && later.state.sendWL2 == Seq.ofNat 202)
    "A newer ACK can replace equal WL1 history."
  let opposite := { queued with sendWL1 := (Seq.ofNat 100).add Seq.halfSpace }
  let half := Endpoint.receive opposite duplicate
  result opposite half (.accepted (.receive 0 1))
  ensure (half.state.sendWindow == opposite.sendWindow)
    "An exact half-space comparison must not pass the freshness test."
  let geometry ← packet 101 201 [1] 0
  let held := Endpoint.receive queued geometry
  result queued held (.accepted (.receive 0 1))
  ensure (held.state.receiveStore.heldBytes == 1 && held.state.receiveStore.nextID == 1 &&
    held.state.core == queued.core && held.state.sendWindow == queued.sendWindow &&
    held.state.sendWL1 == queued.sendWL1 && held.state.sendWL2 == queued.sendWL2 &&
    held.output.isNone && (Endpoint.receivedBytes queued geometry).isEmpty)
    "Future data must retain storage and defer its ACK and window effects."
  let reset ← packet 100 200 [1] 0 20
  let zero := { queued with core := { queued.core with capacity := 0 } }
  result zero (Endpoint.receive zero reset) (.unsupported .reset)

private def wraparound : IO Unit := do
  let wrapped := { seed with
    core := { seed.core with
      receiveNext := Seq.ofNat 4294967295
      sendUna := Seq.ofNat 4294967295
      sendNext := Seq.ofNat 2 }
    sendWL1 := Seq.ofNat 4294967294
    sendWL2 := Seq.ofNat 4294967295 }
  let value ← packet 4294967295 0 [7, 8] 5
  let after := Endpoint.receive wrapped value
  result wrapped after (.accepted (.receive 1 2))
  ensure (after.state.core.receiveNext == Seq.ofNat 1 && after.state.core.sendUna == Seq.ofNat 0 &&
    after.state.sendWindow == 5 && after.state.sendWL2 == Seq.ofNat 0)
    "Receive cursors and window history must use modulo sequence arithmetic."
  let queued := (Endpoint.write wrapped [1, 2]).state
  let sent := Endpoint.send queued 2 true
  result queued sent (.accepted (.send 2))
  ensure (sent.state.core.sendNext == Seq.ofNat 4)
    "A new send must advance from the wrapped SND.NXT."
  let crossing := { seed with core := { seed.core with
    sendUna := Seq.ofNat 4294967292
    sendNext := Seq.ofNat 4294967295 } }
  let crossingQueued := (Endpoint.write crossing [1, 2]).state
  let crossed := Endpoint.send crossingQueued 2 true
  result crossingQueued crossed (.accepted (.send 2))
  let some output := crossed.output | throw (IO.userError "The wrapped send must return checked bytes.")
  ensure (crossed.state.core.sendNext == Seq.ofNat 1 && output.packet.segment.sequence == Seq.ofNat 4294967295 &&
    output.packet.segment.payload == [1, 2])
    "A send across sequence zero must keep the exact output range."

private def rewrite : IO Unit := do
  let value ← packet 100 201 [1] 0
  let target : Packet.Header := ⟨3405803777, 3325256706, Packet.Protocol.tcp, 40000, 9000⟩
  let before := Endpoint.receive seed value
  let changed := value.rewrite target 63 rfl
  let after := Endpoint.receive (seed.rebind target) changed
  ensure (after.state == before.state.rebind target && after.decision == before.decision && after.ack == before.ack)
    "A certified tuple rewrite must preserve receive and peer-window effects."
  ensure ((Endpoint.receive seed changed).decision == .reject (.input .tuple))
    "The endpoint must use the checked tuple."

def run : IO Unit := do
  applicationOperations
  windowUpdates
  wraparound
  rewrite

end NetlibTest.TCPEndpoint
