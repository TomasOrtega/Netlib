import Netlib.Protocol.TCP.EndpointClockEnabled

namespace NetlibTest.TCPEndpointClockEnabled

open Netlib Packet Protocol TCP

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def verify (property : Prop) [Decidable property] (message : String) : Except String { _value : Unit // property } :=
  if accepted : property then .ok ⟨(), accepted⟩ else .error message

private def client : Endpoint.State := {
  core := ⟨⟨3325256706, 3221225985, Packet.Protocol.tcp, 9000, 41000⟩,
    Seq.ofNat 200, 1600, [], Seq.ofNat 100, Seq.ofNat 100, []⟩
  pending := [], pendingLimit := 3200, sendWindow := 1600,
  sendWL1 := Seq.ofNat 200, sendWL2 := Seq.ofNat 100, effectiveMSS := 800, ipSendLimit := 1500 }

private def server : Endpoint.State := {
  core := ⟨⟨3221225985, 3325256706, Packet.Protocol.tcp, 41000, 9000⟩,
    Seq.ofNat 100, 1600, [], Seq.ofNat 200, Seq.ofNat 200, []⟩
  pending := [], pendingLimit := 3200, sendWindow := 1600,
  sendWL1 := Seq.ofNat 100, sendWL2 := Seq.ofNat 200, effectiveMSS := 800, ipSendLimit := 1500 }

private def enabled (state : Endpoint.State) : Endpoint.State :=
  (Endpoint.enableAck (Endpoint.enableRecovery state).state).state

private def tick (state : Endpoint.State) (millis : Nat) : IO Endpoint.State := do
  let valid ← load (verify state.Valid "The preceding clock state must be valid.")
  let coherent ← load (verify (Endpoint.RecoveryCoherent state) "The preceding recovery ledger must be coherent.")
  let prepared ← load (verify (Endpoint.AckPrepared state) "The preceding ACK ledger must be prepared.")
  let storage ← load (verify (Endpoint.StorageCoherent state) "The preceding receive store must be coherent.")
  match runtime : state.recovery with
  | none => throw (IO.userError "The clock test requires the actual recovery runtime.")
  | some recovery =>
    let monotone ← load (verify (recovery.now ≤ millis) "The selected clock target must be monotone.")
    let timely ← load (verify (Endpoint.AckTimeReady state millis) "The old ACK causes must permit the clock target.")
    let clocked ← load (verify recovery.Clocked "The old transmission times must precede the current clock.")
    let positive ← load (verify recovery.Positive "The old outstanding ranges must be positive.")
    have computed := Endpoint.advanceClock_of_monotone state millis valid.property coherent.property
      runtime monotone.property timely.property
    have frame : Endpoint.ClockFrame state (Endpoint.advanceClock state millis).state := by
      rw [computed]
      exact Endpoint.clockState_frame state millis runtime monotone.property
    let _ := frame.storage_coherent storage.property
    let _ := frame.recovery_coherent coherent.property
    let _ := frame.ack_prepared prepared.property (by
      simpa only [computed, Endpoint.clockState_now state millis runtime] using timely.property)
    let _ := frame.clocked runtime clocked.property
    let _ := frame.positive runtime positive.property
    let result := Endpoint.advanceClock state millis
    ensure (result.decision == .accepted .advanceClock && result.output.isNone && result.read.isEmpty &&
        result.state.now == millis && result.state.recovery == some { recovery with now := millis })
      "An accepted tick must retain the actual recovery ledger and change only its clock."
    return result.state

def run : IO Unit := do
  let sent := Endpoint.send (Endpoint.write (enabled client) [37, 38]).state 2 true
  ensure (sent.decision == .accepted (.send 2)) "The clock test must start with an actual data output."
  let first ← tick sent.state 10
  let second ← tick first 20
  ensure (second.core == sent.state.core && second.pending == sent.state.pending &&
      second.receiveStore == sent.state.receiveStore && second.ackReaction == sent.state.ackReaction &&
      second.sendWindow == sent.state.sendWindow && second.sendWL1 == sent.state.sendWL1 && second.sendWL2 == sent.state.sendWL2 &&
      second.effectiveMSS == sent.state.effectiveMSS && second.lastAckWindow == sent.state.lastAckWindow)
    "Positive ticks must retain bytes, ACK causes, window history, and negotiated limits."
  let backward := Endpoint.advanceClock second 19
  ensure (backward.decision == .reject (.recovery .backwardClock) && backward.state == second)
    "A backward clock must fail and retain the current endpoint."
  let some packet := sent.output
    | throw (IO.userError "The actual send must retain its packet.")
  let received := Endpoint.receive (enabled server) packet
  ensure (received.decision == .accepted (.receive 0 2)) "The first actual receipt must release the selected bytes."
  let responded := Endpoint.emitAck received.state true
  let repeated := Endpoint.receive responded.state packet
  ensure (repeated.decision == .reject (.input .sequence) &&
      decide (Endpoint.AckTimeReady repeated.state repeated.state.now) &&
      !decide (Endpoint.AckTimeReady repeated.state (repeated.state.now + 1)))
    "An actual whole-old receipt must block a positive tick through its immediate ACK deadline."
  let overdue := Endpoint.advanceClock repeated.state (repeated.state.now + 1)
  ensure (overdue.decision == .ackUnsupported .deadline && overdue.state == repeated.state)
    "A clock advance beyond an immediate ACK deadline must fail without changing the endpoint."
  IO.println "Endpoint advancing-clock tests passed."

end NetlibTest.TCPEndpointClockEnabled
