import Netlib.Protocol.TCP.HandshakeTimer
import Netlib.Protocol.TCP.HandshakeDuplicate
import Netlib.Protocol.TCP.EndpointStartupRecovery

namespace NetlibTest.TCPHandshakeRecovery

open Netlib Protocol TCP

namespace T
export HandshakeTimer (Kind State Status Flight Stop initial arm advance expire acknowledge handoff)
end T

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def timer : Except T.Stop α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError s!"Unexpected startup timer rejection: {repr reason}.")

private def transition : Except Handshake.Failure α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason.message)

private def flight (state : T.State) : IO T.Flight :=
  match state.status with
  | .pending value => pure value
  | _ => throw (IO.userError "The current SYN timer must still be pending.")

private def reject (result : Except T.Stop α) (expected : T.Stop) : IO Unit :=
  match result with
  | .error reason => ensure (reason == expected) "The startup timer rejection is incorrect."
  | .ok _ => throw (IO.userError "The startup timer operation must reject.")

private def backoff (kind : T.Kind) (count : Nat) : IO Unit := do
  let source := 83
  let first := 47
  let mut state ← timer (T.arm (T.initial 1000 first) kind source)
  ensure (state.now == first && state.rto == 1000 && state.estimator.isNone && decide state.Valid)
    "A SYN timer must start from the actual current clock without an RTT sample."
  reject (T.arm state kind (source + 1)) .alreadyStarted
  reject (T.advance state (first - 1)) .backwardClock
  for generation in List.range count do
    let old ← flight state
    let early ← timer (T.advance state (old.deadline - 1))
    reject (T.expire early generation) .early
    let due ← timer (T.advance early old.deadline)
    let next ← timer (T.expire due generation)
    let current ← flight next
    ensure (next.rto == 2 * state.rto && next.now == old.deadline &&
        next.estimator == state.estimator && next.shortSynTimeout &&
        current.kind == kind && current.source == source && current.firstAt == first &&
        current.lastAt == next.now && current.retries == generation + 1 &&
        current.deadline == next.now + next.rto && decide next.Valid)
      "Expiry must retain the selected control and clock, double RTO, and restart one timer."
    reject (T.expire next generation) .obsolete
    let future ← timer (T.advance next current.deadline)
    reject (T.expire future generation) .obsolete
    state := next
  let pending ← flight state
  let received ← timer (T.advance state (state.now + 37))
  let closed ← timer (T.acknowledge received)
  let some data := T.handoff closed
    | throw (IO.userError "The acknowledged SYN must permit a timer handoff.")
  let expectedRTO := if count == 0 then 1000 else max 3000 (1000 * 2 ^ count)
  ensure (data.now == received.now && data.rto == expectedRTO &&
      data.synRetransmitted == (count != 0) && decide closed.Valid &&
      closed.status == .acknowledged pending received.now &&
      (if count == 0 then data.estimator == some (RTO.first 37) else data.estimator.isNone))
    "Data recovery must retain the clock, Karn eligibility, backoff, and the SYN timeout floor."
  reject (T.expire closed count) .idle
  reject (T.arm closed kind source) .alreadyStarted

private def races : IO Unit := do
  let opened ← timer (T.arm (T.initial 1000 19) .syn 101)
  let due ← timer (T.advance opened 1019)
  let acknowledgedFirst ← timer (T.acknowledge due)
  reject (T.expire acknowledgedFirst 0) .idle
  ensure (acknowledgedFirst.estimator == some (RTO.first 1000) && !acknowledgedFirst.shortSynTimeout)
    "An ACK before expiry at the same clock must cancel the timer and retain its eligible sample."
  let expiredFirst ← timer (T.expire due 0)
  let acknowledgedLast ← timer (T.acknowledge expiredFirst)
  ensure (acknowledgedLast.estimator.isNone && acknowledgedLast.rto == 2000 &&
      HandshakeTimer.dataRTO acknowledgedLast == 3000)
    "Expiry before the ACK at the same clock must suppress sampling and retain the data RTO floor."
  let idle := T.initial
  ensure ((T.handoff idle).isNone && (T.handoff opened).isNone)
    "An idle or unacknowledged SYN must not supply a data handoff."
  reject (T.expire idle 0) .idle
  reject (T.acknowledge idle) .idle
  let conservative ← timer (T.arm (T.initial 5000 23) .synAck 109)
  let expired ← timer (T.expire (← timer (T.advance conservative 5023)) 0)
  let closed ← timer (T.acknowledge expired)
  ensure (!closed.shortSynTimeout && HandshakeTimer.dataRTO closed == 10000)
    "An initial RTO above three seconds must retain its larger backoff."

private def config (address : Packet.Address) (port : Packet.Port) (iss capacity : Nat) : Handshake.Local :=
  ⟨⟨address, port⟩, Seq.ofNat iss, capacity, 8, 1500, none⟩

private def endpointHandoff (seed : Endpoint.State) : IO Unit := do
  let started ← timer (T.arm (T.initial 1000 61) .syn 307)
  let expired ← timer (T.expire (← timer (T.advance started 1061)) 0)
  let acknowledged ← timer (T.acknowledge expired)
  let some data := T.handoff acknowledged
    | throw (IO.userError "The completed startup timer must supply data recovery parameters.")
  let result := Endpoint.enableStartupRecovery seed data
  let some recovery := result.state.recovery
    | throw (IO.userError "The accepted startup handoff must create the data recovery ledger.")
  ensure (result.decision == .accepted .enableRecovery && result.output.isNone && result.read.isEmpty &&
      recovery.now == 1061 && recovery.rto == 3000 && recovery.estimator.isNone && recovery.lastSample.isNone &&
      recovery.cwnd == seed.effectiveMSS && recovery.outstanding.isEmpty && recovery.deadline.isNone &&
      result.state.core == seed.core && result.state.pending == seed.pending &&
      result.state.sendWL1 == seed.sendWL1 && result.state.sendWL2 == seed.sendWL2 &&
      result.state.ackReaction == seed.ackReaction && result.state.receiveStore == seed.receiveStore &&
      decide result.state.Valid && decide (Endpoint.RecoveryCoherent result.state))
    "The actual data enable operation must retain the startup clock and RTO without replacing endpoint state."
  let repeated := Endpoint.enableStartupRecovery result.state data
  ensure (repeated.decision == .reject (.recovery .ledger) && repeated.state == result.state)
    "A second enable must reject without clearing the existing data recovery state."
  let invalid := Endpoint.enableStartupRecovery seed { data with rto := 999 }
  ensure (invalid.decision == .reject (.recovery .ledger) && invalid.state == seed)
    "A handoff below the selected RTO floor must reject without changing the endpoint."
  let defaultData : HandshakeTimer.Data := ⟨0, 1000, none, false⟩
  let ordinary := Endpoint.enableRecovery seed
  let legacy := Endpoint.enableStartupRecovery seed defaultData
  ensure (ordinary.state == legacy.state && ordinary.decision == legacy.decision)
    "Default startup parameters must retain the legacy enable behavior."

private def duplicates (iss capacity : Nat) : IO Unit := do
  let active := config 3221225985 41000 iss capacity
  let passive := config 3325256706 8080 (iss + 13) capacity
  let sent ← transition (Handshake.activeOpen active passive.socket true)
  let received ← transition (Handshake.listenSyn passive sent.output true)
  let established ← transition (Handshake.synSentSynAck sent received.output true)
  let finished ← transition (Handshake.synReceivedAck received established.output)
  let passiveAck := HandshakeDuplicate.syn_received_ack received
  let activeAck := HandshakeDuplicate.active_established_ack sent received.output established
  let finalAck := HandshakeDuplicate.passive_established_ack received established.output finished
  ensure (!(ReceiveWindow.acceptsSegment (active.iss.add 1) capacity sent.output.packet.segment) &&
      !(ReceiveWindow.acceptsSegment (passive.iss.add 1) capacity received.output.packet.segment))
    "A consumed SYN position must fail the first sequence test, including zero windows and sequence wrap."
  for (packet, sendNext, receiveNext) in
      [(passiveAck.output, passive.iss.add 1, active.iss.add 1),
        (activeAck.output, active.iss.add 1, passive.iss.add 1),
        (finalAck.output, passive.iss.add 1, active.iss.add 1)] do
    ensure (packet.packet.segment.flags == 16 && packet.packet.segment.payload.isEmpty &&
        packet.packet.segment.options.isEmpty && packet.packet.segment.sequence == sendNext &&
        packet.packet.segment.acknowledgment == receiveNext && packet.packet.segment.window.val == capacity &&
        packet.bytes.length == 40 && packet.packet.ip.packet.ttl.toNat == 64 &&
        ReceiveWindow.segmentLength packet.packet.segment == 0 &&
        checksumAccepts packet.packet.ip.packet.source packet.packet.ip.packet.destination packet.packet.segment)
      "Duplicate startup controls must produce a bare ACK at current cursors without new SYN sequence space."
  ensure (passiveAck.output.packet.header == Output.reverse received.input.packet.header &&
      activeAck.output.packet.header == Output.reverse established.seed.core.inbound &&
      finalAck.output.packet.header == Output.reverse finished.seed.core.inbound)
    "Each duplicate ACK must use its actual endpoint tuple."
  endpointHandoff established.seed
  endpointHandoff finished.seed

def run : IO Unit := do
  for kind in ([.syn, .synAck] : List T.Kind) do
    for count in List.range 4 do backoff kind count
  races
  for iss in [99, Seq.modulus - 1, Seq.modulus - 14] do
    for capacity in [0, 4, 65535] do duplicates iss capacity
  IO.println "TCP startup timer and duplicate-response tests passed."

end NetlibTest.TCPHandshakeRecovery
