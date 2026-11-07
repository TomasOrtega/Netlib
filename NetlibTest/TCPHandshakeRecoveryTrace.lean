import Netlib.Check.TCPHandshakeRecoveryFacts
import Netlib.Protocol.TCP.EndpointStartupRecovery

namespace NetlibTest.TCPHandshakeRecoveryTrace

open Netlib Protocol TCP
namespace C
export Check.TCPHandshakeRecovery (State Step Event Effect Emission Phase Side Cause)
end C

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def active : Handshake.Local := ⟨⟨3221225985, 41000⟩, Seq.ofNat 4294967295, 8, 32, 1500, none⟩
private def passive : Handshake.Local := ⟨⟨3325256706, 8080⟩, Seq.ofNat 199, 8, 32, 1500, none⟩

private structure Run where
  state : C.State active passive
  next : Nat
  events : List C.Event
  steps : List (C.Step active passive)
  trace : Check.TCPHandshakeRecovery.Trace .initial events steps state

private def initial : Run := ⟨.initial, 17, [], [], .done _⟩

private def append (before : Run) (event : C.Event) : IO (Run × C.Effect active passive) := do
  match computed : Check.TCPHandshakeRecovery.evaluate before.state before.next event with
  | .error reason => throw (IO.userError reason)
  | .ok effect =>
    let actual : C.Step active passive := ⟨before.state, before.next, event, effect, computed⟩
    return (⟨effect.state, before.next + 1, before.events ++ [event], before.steps ++ [actual], Check.TCPHandshakeRecovery.Trace.snoc (actual := actual) before.trace⟩, effect)

private def output (effect : C.Effect active passive) : IO C.Emission := do
  let some value := effect.output | throw (IO.userError "The startup event must emit a control occurrence.")
  return value

private def openConnection : IO (Run × C.Emission) := do
  let (run, effect) ← append initial (.activeOpen passive.socket true)
  return (run, ← output effect)

private def deliver (run : Run) (source : C.Emission) : IO (Run × C.Effect active passive) :=
  append run (.receive source.index source.packet.bytes .direct true)

private def timeout (run : Run) (side : C.Side) : IO (Run × C.Emission) := do
  let (clocked, _) ← append run (.advanceClock side 1000)
  let (retried, effect) ← append clocked (.timeout side 0 true)
  let packet ← output effect
  ensure (packet.index == clocked.next && packet.actor == side &&
      retried.state.emissions.length == run.state.emissions.length + 1)
    "A timer retry must create a fresh event-indexed occurrence without removing its original."
  return (retried, packet)

private def completed (run : Run) (activeRetries passiveRetries : Nat) : IO Unit := do
  match run.state.phase with
  | .complete complete client server =>
    ensure (complete.input.times.Valid && client.current.core.sendNext == active.iss.add 1 &&
        client.current.core.receiveNext == passive.iss.add 1 &&
        server.current.core.sendNext == passive.iss.add 1 && server.current.core.receiveNext == active.iss.add 1 &&
        client.current.pending.isEmpty && client.current.core.sent.isEmpty && client.current.core.received.isEmpty &&
        server.current.pending.isEmpty && server.current.core.sent.isEmpty && server.current.core.received.isEmpty)
      "Completion must retain the actual advancing witnesses and complementary empty endpoint cursors."
    let some activeData := HandshakeTimer.handoff run.state.activeTimer
      | throw (IO.userError "The active SYN must be acknowledged before data handoff.")
    let some passiveData := HandshakeTimer.handoff run.state.passiveTimer
      | throw (IO.userError "The passive SYN must be acknowledged before data handoff.")
    ensure (activeData.synRetransmitted == (activeRetries != 0) &&
        passiveData.synRetransmitted == (passiveRetries != 0) &&
        (if activeRetries == 0 then activeData.estimator.isSome else activeData.estimator.isNone) &&
        (if passiveRetries == 0 then passiveData.estimator.isSome else passiveData.estimator.isNone) &&
        (if activeRetries == 0 then activeData.rto == 1000 else activeData.rto == max 3000 (1000 * 2 ^ activeRetries)) &&
        (if passiveRetries == 0 then passiveData.rto == 1000 else passiveData.rto == max 3000 (1000 * 2 ^ passiveRetries)))
      "Each endpoint must retain its own retransmission and RTT history at the data handoff."
    let clientReady := Endpoint.enableStartupRecovery client.current activeData
    let serverReady := Endpoint.enableStartupRecovery server.current passiveData
    ensure (clientReady.decision == .accepted .enableRecovery && serverReady.decision == .accepted .enableRecovery &&
        clientReady.state.core == client.current.core && serverReady.state.core == server.current.core &&
        clientReady.state.sendWL1 == client.current.sendWL1 && serverReady.state.sendWL1 == server.current.sendWL1)
      "Enabling data recovery must retain the current endpoint buffers and window metadata."
  | _ => throw (IO.userError "The actual startup trace must complete.")
  let indices := run.state.emissions.map (·.index)
  ensure (indices.eraseDups == indices && indices.all (fun index => index < run.next) &&
      run.state.receipts.all (fun receipt => receipt.source.index < receipt.index &&
        indices.contains receipt.source.index && run.steps.any (fun actual =>
          actual.index == receipt.index && match actual.event with
          | .receive source bytes .direct true => source == receipt.source.index && bytes == receipt.spec.bytes
          | _ => false)))
    "All stored sources and receipts must belong to their actual ordered startup events."

private def ordinary : IO Unit := do
  let (opened, syn) ← openConnection
  let (answered, response) ← deliver opened syn
  let synAck ← output response
  let (acknowledged, response) ← deliver answered synAck
  let ack ← output response
  let (done, _) ← deliver acknowledged ack
  completed done 0 0

private def absentSyn : IO Unit := do
  let (opened, original) ← openConnection
  let (retried, syn) ← timeout opened .active
  ensure (syn.index != original.index && syn.packet.bytes == original.packet.bytes)
    "Equal retry bytes must retain distinct original and retransmission identities."
  let (answered, response) ← deliver retried syn
  let synAck ← output response
  let (acknowledged, response) ← deliver answered synAck
  let ack ← output response
  let (done, _) ← deliver acknowledged ack
  ensure (done.state.receipts.head?.map (·.source.index) == some syn.index &&
      !done.state.receipts.any (fun receipt => receipt.source.index == original.index))
    "The selected retry receipt must identify the actual retry rather than its equal-byte original."
  completed done 1 0

private def absentSynAck : IO Unit := do
  let (opened, syn) ← openConnection
  let (answered, response) ← deliver opened syn
  let original ← output response
  let (retried, repeatedSyn) ← timeout answered .active
  let (responded, response) ← deliver retried repeatedSyn
  let bareAck ← output response
  let (discarded, effect) ← deliver responded bareAck
  ensure (effect.decision == .discarded && effect.output.isNone && bareAck.packet.packet.segment.flags == 16 &&
      discarded.state.activeTimer.rto == 2000 && discarded.state.passiveTimer.rto == 1000)
    "A passive bare ACK must not establish the active endpoint or cancel either pending SYN timer."
  let (serverRetried, synAck) ← timeout discarded .passive
  let (acknowledged, response) ← deliver serverRetried synAck
  let ack ← output response
  let (done, _) ← deliver acknowledged ack
  ensure (!done.state.receipts.any (fun receipt => receipt.source.index == original.index) &&
      (done.state.emissions.filter (fun emission => match emission.cause with | .timeout .. => true | _ => false)).length == 2)
    "One missing SYN,ACK receipt can cause two actual endpoint timer retries."
  completed done 1 1

private def delayedFinalAck : IO Unit := do
  let (opened, syn) ← openConnection
  let (answered, response) ← deliver opened syn
  let synAck ← output response
  let (acknowledged, response) ← deliver answered synAck
  let originalAck ← output response
  let (retried, repeatedSynAck) ← timeout acknowledged .passive
  let (responded, response) ← deliver retried repeatedSynAck
  let repeatedAck ← output response
  let (done, _) ← deliver responded originalAck
  let (drained, effect) ← deliver done repeatedAck
  ensure (repeatedAck.index != originalAck.index && repeatedAck.packet.bytes == originalAck.packet.bytes &&
      effect.application.isSome && effect.output.isNone &&
      drained.state.receipts.any (fun receipt => receipt.source.index == originalAck.index) &&
      drained.state.receipts.any (fun receipt => receipt.source.index == repeatedAck.index))
    "A delayed original ACK and its later duplicate must retain separate receipt identities and endpoint operations."
  completed drained 0 1

private def delayedOriginalSyn : IO Unit := do
  let (opened, original) ← openConnection
  let (retried, syn) ← timeout opened .active
  let (answered, response) ← deliver retried syn
  let synAck ← output response
  let (acknowledged, response) ← deliver answered synAck
  let ack ← output response
  let (responded, response) ← deliver acknowledged original
  let bareAck ← output response
  let (received, effect) ← deliver responded bareAck
  ensure (effect.application.isSome && effect.output.isNone)
    "A bare ACK after active establishment must execute an actual endpoint receive."
  let (done, _) ← deliver received ack
  match done.state.phase with
  | .complete _ client _ =>
    ensure (client.steps.length == 1 && client.current.sendWL1 == passive.iss.add 1 &&
        client.steps.head?.map (·.stamp) == some responded.next)
      "Completion must retain the early ACK operation and its changed window marker."
  | _ => throw (IO.userError "The delayed-original case must complete.")
  completed done 1 0

private def repeatedExpiry : IO Unit := do
  let (opened, original) ← openConnection
  let (retried, _) ← timeout opened .active
  let (clocked, _) ← append retried (.advanceClock .active 3000)
  let (obsolete, ignored) ← append clocked (.timeout .active 0 true)
  ensure (ignored.decision == .obsolete && ignored.output.isNone &&
      obsolete.state.emissions.length == retried.state.emissions.length && obsolete.state.activeTimer.rto == 2000)
    "An obsolete queued expiry must not emit even after the next deadline."
  let (retriedAgain, effect) ← append obsolete (.timeout .active 1 true)
  let repeatedSyn ← output effect
  ensure (repeatedSyn.cause == .timeout original.index 1 && repeatedSyn.packet.bytes == original.packet.bytes &&
      repeatedSyn.index != original.index && retriedAgain.state.activeTimer.rto == 4000)
    "The current generation must emit its own occurrence and retain the larger backoff."
  let (answered, response) ← deliver retriedAgain original
  let synAck ← output response
  let (acknowledged, response) ← deliver answered synAck
  let ack ← output response
  let (done, _) ← deliver acknowledged ack
  completed done 2 0

private def rejected : Except ε α → Bool
  | .error _ => true
  | .ok _ => false

private def guards : IO Unit := do
  let (opened, syn) ← openConnection
  ensure (rejected (Check.TCPHandshakeRecovery.evaluate opened.state opened.next (.timeout .active 0 true)) &&
      rejected (Check.TCPHandshakeRecovery.evaluate opened.state opened.next (.receive (syn.index + 1) syn.packet.bytes .direct true)) &&
      rejected (Check.TCPHandshakeRecovery.evaluate opened.state opened.next (.receive syn.index syn.packet.bytes .direct false)) &&
      rejected (Check.TCPHandshakeRecovery.evaluate opened.state syn.index (.advanceClock .active 1)))
    "Early expiry, missing sources, denied receipts, and reused event indices must reject."

def run : IO Unit := do
  ordinary
  absentSyn
  absentSynAck
  delayedFinalAck
  delayedOriginalSyn
  repeatedExpiry
  guards
  IO.println "Actual TCP startup recovery traces passed."

end NetlibTest.TCPHandshakeRecoveryTrace
