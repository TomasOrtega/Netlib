import Netlib.Protocol.TCP.ReceiveReassembly
import Netlib.Protocol.TCP.Endpoint

namespace NetlibTest.TCPReceiveReassembly

open Netlib Packet Protocol TCP

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def client : Endpoint.State := {
  core := ⟨⟨3325256706, 3221225985, Packet.Protocol.tcp, 9000, 41000⟩,
    Seq.ofNat 200, 1600, [], Seq.ofNat 100, Seq.ofNat 100, []⟩
  pending := [], pendingLimit := 3200, sendWindow := 1600,
  sendWL1 := Seq.ofNat 200, sendWL2 := Seq.ofNat 100, effectiveMSS := 800, ipSendLimit := 1500 }

private def server : Endpoint.State := {
  core := ⟨⟨3221225985, 3325256706, Packet.Protocol.tcp, 41000, 9000⟩,
    Seq.ofNat 100, 1600, [], Seq.ofNat 200, Seq.ofNat 200, []⟩
  pending := [], pendingLimit := 3200, sendWindow := 1600,
  sendWL1 := Seq.ofNat 100, sendWL2 := Seq.ofNat 200, effectiveMSS := 1200, ipSendLimit := 1500 }

private def payload (start count : Nat) : List UInt8 :=
  (List.range count).map fun offset => UInt8.ofNat ((start + offset) % 251)

private def output (result : Endpoint.Result) : IO EstablishedReceive.Input :=
  match result.output with
  | some value => pure value
  | none => throw (IO.userError s!"The actual endpoint output is missing: {repr result.decision}.")

private def data (plan : ReceiveReassembly.Plan) : IO (ReceiveStore.Result ReceiveReassembly.Receipt) :=
  match plan with
  | .data stored => pure stored
  | _ => throw (IO.userError s!"The selected packet did not produce a data plan: {repr plan}.")

private def applied : Except ReceiveReassembly.HeaderFailure ReceiveReassembly.Applied → IO ReceiveReassembly.Applied
  | .ok value => pure value
  | .error reason => throw (IO.userError s!"The released header batch failed: {repr reason}.")

private def alter (input : EstablishedReceive.Input) (change : Segment → Segment) : IO EstablishedReceive.Input := do
  let tuple := input.packet.header
  let segment := TCP.rechecksum tuple.source tuple.destination (change input.packet.segment)
  let packet := { input.packet.ip.packet with payload := segment.encodeBytes }
  let encoded ← load (IPv4.encode packet)
  load (EstablishedReceive.input encoded)

private def pair : IO (EstablishedReceive.Input × EstablishedReceive.Input) := do
  let written := Endpoint.write client (payload 17 400 ++ payload 31 400)
  let first := Endpoint.send written.state 400 true
  let second := Endpoint.send first.state 400 true
  return (← output first, ← output second)

private def retainAndRelease : IO Unit := do
  let (first, second) ← pair
  let initial : ReceiveReassembly.Store := ReceiveStore.initial
  let held ← data (ReceiveReassembly.prepare server.core initial second 1600 100)
  ensure (held.released.isEmpty && held.novel == 400 && held.state.frontier == 0 &&
      held.state.heldBytes == 400 && held.state.physicalFree 1600 == 1200 &&
      held.state.held.map (·.metadata.receivedAt) == [100])
    "A future packet must retain its actual bytes and arrival time without filling the gap."
  let unchanged ← applied (ReceiveReassembly.applyRuns server.core held.released)
  ensure (unchanged.state == server.core && unchanged.acknowledged == 0 && unchanged.headers.isEmpty)
    "Held data must not apply its ACK or change the ordered receive buffer."
  let closed ← data (ReceiveReassembly.prepare unchanged.state held.state first 1600 1000)
  ensure (ReceiveStore.bytes closed.released == payload 17 400 ++ payload 31 400 &&
      closed.released.map (·.receipt) == [1, 0] &&
      closed.released.map (·.metadata.receivedAt) == [1000, 100] && closed.state.held.isEmpty)
    "A gap fill must release the actual current and earlier receipts in sequence order."
  let result ← applied (ReceiveReassembly.applyRuns server.core closed.released)
  ensure (result.state.received == payload 17 400 ++ payload 31 400 &&
      result.state.receiveNext == Seq.ofNat 900 && result.acknowledged == 0 &&
      result.headers.map (·.run.metadata.segment) == [first.packet.segment, second.packet.segment] &&
      result.headers.map (·.run.metadata.header) == [first.packet.header, second.packet.header])
    "The released batch must process the exact original headers and append each payload once."

private def evolvedAcknowledgments : IO Unit := do
  let offered := Endpoint.write server (payload 71 400 ++ payload 83 400)
  let firstReply := Endpoint.send offered.state 400 true
  let secondReply := Endpoint.send firstReply.state 400 true
  let firstReceived := Endpoint.receive client (← output firstReply)
  ensure (firstReceived.decision == .accepted (.receive 0 400)) "The first actual reverse data receipt must succeed."
  let written := Endpoint.write firstReceived.state (payload 17 400 ++ payload 31 400)
  let first := Endpoint.send written.state 400 true
  let laterReceived := Endpoint.receive first.state (← output secondReply)
  ensure (laterReceived.decision == .accepted (.receive 0 400)) "The second actual reverse data receipt must succeed."
  let second := Endpoint.send laterReceived.state 400 true
  let firstPacket ← output first
  let secondPacket ← output second
  ensure (firstPacket.packet.segment.acknowledgment == Seq.ofNat 600 &&
      secondPacket.packet.segment.acknowledgment == Seq.ofNat 1000)
    "Actual peer receipts must supply both distinct cumulative ACKs."
  let target := secondReply.state.core
  ensure (EstablishedReceive.acknowledgedCount target secondPacket.packet.segment.acknowledgment == some 800)
    "The held ACK must cover the actual 800-byte receipt-time send range."
  let held ← data (ReceiveReassembly.prepare target ReceiveStore.initial secondPacket 1600 100)
  let unchanged ← applied (ReceiveReassembly.applyRuns target held.released)
  ensure (unchanged.state.sendUna == Seq.ofNat 200 && unchanged.state.sent.length == 800 &&
      unchanged.acknowledged == 0)
    "The higher sequence packet must defer its otherwise valid advancing ACK."
  let closed ← data (ReceiveReassembly.prepare target held.state firstPacket 1600 1000)
  let result ← applied (ReceiveReassembly.applyRuns target closed.released)
  ensure (result.headers.map (·.acknowledged) == [400, 400] &&
      result.headers.map (·.before.sendUna) == [Seq.ofNat 200, Seq.ofNat 600] &&
      result.headers.map (·.run.metadata.receivedAt) == [1000, 100] &&
      result.acknowledged == 800 && result.state.sendUna == Seq.ofNat 1000 &&
      result.state.sent.isEmpty && result.state.received.length == 800)
    "Each queued ACK must be rechecked against the prior released header's actual state."

private def deferredFailures : IO Unit := do
  let (first, second) ← pair
  let missing ← alter second (fun segment => { segment with flags := 0 })
  let heldMissing ← data (ReceiveReassembly.prepare server.core ReceiveStore.initial missing 1600 100)
  ensure (heldMissing.released.isEmpty && heldMissing.state.held.map (·.metadata.segment.flags) == [0])
    "An above-gap data receipt must defer its missing-ACK check with the original header."
  let missingBatch ← data (ReceiveReassembly.prepare server.core heldMissing.state first 1600 1000)
  match ReceiveReassembly.applyRuns server.core missingBatch.released with
  | .error failure =>
    ensure (failure.reason == .reject .missingAck && failure.run.receipt == 0 &&
        failure.run.metadata.segment == missing.packet.segment && failure.run.metadata.header == missing.packet.header &&
        failure.run.metadata.receivedAt == 100 && failure.before.receiveNext == Seq.ofNat 500 &&
        failure.before.received == payload 17 400)
      "A queued missing ACK must identify its actual earlier receipt and processing state."
  | _ => throw (IO.userError "The queued missing ACK must fail the whole batch without a final state.")
  let outside ← alter second (fun segment => { segment with acknowledgment := Seq.ofNat 500000 })
  let heldOutside ← data (ReceiveReassembly.prepare server.core ReceiveStore.initial outside 1600 100)
  ensure (heldOutside.released.isEmpty) "An above-gap ACK range check must wait for sequence-order release."
  let outsideBatch ← data (ReceiveReassembly.prepare server.core heldOutside.state first 1600 1000)
  match ReceiveReassembly.applyRuns server.core outsideBatch.released with
  | .error failure =>
    ensure (failure.reason == .reject .acknowledgment && failure.run.receipt == 0 &&
        failure.run.metadata.segment == outside.packet.segment && failure.run.metadata.header == outside.packet.header &&
        failure.run.metadata.receivedAt == 100 && failure.before.receiveNext == Seq.ofNat 500)
      "A queued ACK range failure must identify the retained header rather than the fresh gap receipt."
  | _ => throw (IO.userError "The queued invalid ACK must fail the complete batch.")

private def pureAcknowledgments : IO Unit := do
  let packet ← output (Endpoint.emitAck client true)
  match ReceiveReassembly.prepare server.core ReceiveStore.initial packet 1600 100 with
  | .acknowledgment 0 => pure ()
  | _ => throw (IO.userError "A pure ACK must keep the existing immediate header path.")
  let missing ← alter packet (fun segment => { segment with flags := 0 })
  match ReceiveReassembly.prepare server.core ReceiveStore.initial missing 1600 100 with
  | .blocked (.reject .missingAck) none => pure ()
  | _ => throw (IO.userError "A pure packet with no ACK flag must be rejected immediately.")
  let outside ← alter packet (fun segment => { segment with acknowledgment := Seq.ofNat 500000 })
  match ReceiveReassembly.prepare server.core ReceiveStore.initial outside 1600 100 with
  | .blocked (.reject .acknowledgment) (some ack) =>
    ensure (ack.kind == .challenge) "An immediate pure-ACK range rejection must retain its challenge request."
  | _ => throw (IO.userError "A pure ACK must retain its existing immediate range check.")

def run : IO Unit := do
  retainAndRelease
  evolvedAcknowledgments
  deferredFailures
  pureAcknowledgments
  IO.println "Checked receive-reassembly tests passed."

end NetlibTest.TCPReceiveReassembly
