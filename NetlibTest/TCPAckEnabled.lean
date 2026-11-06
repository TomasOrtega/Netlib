import Netlib.Protocol.TCP.EndpointAckEnabled

namespace NetlibTest.TCPAckEnabled

open Netlib Packet Protocol TCP

example (state : Endpoint.State) (dueOnly : Bool) (valid : state.Valid)
    (prepared : Endpoint.AckPrepared state) (available : Endpoint.ResponseAvailable state dueOnly) :
    ∃ output, Endpoint.pureAck state true dueOnly =
        ⟨Endpoint.outputState state, .accepted (if dueOnly then .dispatchAck else .emitAck), some output, [], none⟩ ∧
      output.packet.segment.payload = [] ∧ output.packet.segment.acknowledgment = state.core.receiveNext ∧
      output.packet.segment.window.val = Endpoint.outputWindow state := by
  obtain ⟨output, accepted, encoded⟩ := Endpoint.pureAck_success_enabled state dueOnly valid prepared available
  have fields := Endpoint.emit_transport state [] output encoded
  exact ⟨output, accepted, Endpoint.emit_payload state [] output encoded, fields.2.2.1, fields.2.2.2.1⟩

example (state : AckReaction.State) (now : Nat) (cursor : Seq) (novel released : Nat) (immediate : Bool)
    (capacity free outgoingMSS : Nat) (covered : state.Covered capacity free outgoingMSS)
    (valid : state.advertisement.Valid free) (fits : released ≤ state.window)
    (timely : state.WithinTime now) :
    AckReaction.outputReady (AckReaction.receiveRelease state now cursor novel released immediate)
      now cursor capacity (free - released) outgoingMSS = .ok () :=
  AckReaction.outputReady_of_covered _ _ _ _ _ _
    (AckReaction.receiveRelease_within _ _ _ _ _ _ timely)
    (AckReaction.receiveRelease_covered _ _ _ _ _ _ _ _ _ covered valid fits)

example (state : Endpoint.State) (valid : state.Valid) (coherent : Endpoint.RecoveryCoherent state)
    (disabled : state.ackReaction = none) (recovery : state.recovery.isSome = true)
    (received : state.core.received = []) (sent : state.core.sent = [])
    (initial : state.receiveStore = ReceiveStore.initial) : Endpoint.AckPrepared (Endpoint.enableAck state).state := by
  have initialized := Endpoint.enableAck_success_prepared state valid coherent disabled recovery received sent initial
  rw [initialized.1]
  exact initialized.2

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
  sendWL1 := Seq.ofNat 200, sendWL2 := Seq.ofNat 100, effectiveMSS := 800, ipSendLimit := 1500
  localReceiveMSS := .present ⟨⟨1200, by decide⟩, by decide⟩ }

private def server : Endpoint.State := {
  core := ⟨⟨3221225985, 3325256706, Packet.Protocol.tcp, 41000, 9000⟩,
    Seq.ofNat 100, 1600, [], Seq.ofNat 200, Seq.ofNat 200, []⟩
  pending := [], pendingLimit := 3200, sendWindow := 1600,
  sendWL1 := Seq.ofNat 100, sendWL2 := Seq.ofNat 200, effectiveMSS := 1200, ipSendLimit := 1500
  localReceiveMSS := .present ⟨⟨800, by decide⟩, by decide⟩ }

private def enabled (state : Endpoint.State) : Endpoint.State :=
  (Endpoint.enableAck (Endpoint.enableRecovery state).state).state

private def uncoveredPromise : Endpoint.State :=
  let state := enabled server
  { state with ackReaction := state.ackReaction.map (fun reaction =>
    { reaction with work := (Theory.TimedReaction.issue reaction.work state.now
      ⟨.window, state.core.receiveNext, reaction.advertisement.frontier, 0, 1601⟩ 0) }) }

example : Endpoint.AckCoherent uncoveredPromise ∧ ¬Endpoint.AckPrepared uncoveredPromise := by decide

private def packet (result : Endpoint.Result) : IO EstablishedReceive.Input :=
  match result.output with
  | some value => pure value
  | none => throw (IO.userError "The actual operation has no packet output.")

private def prepared (state : Endpoint.State) : IO Unit := do
  let evidence ← load (verify (Endpoint.AckPrepared state) "The actual endpoint violates ACK predecessor guards.")
  let _ := Endpoint.ackReady_of_prepared state evidence.property
  pure ()

private def acknowledge (state : Endpoint.State) (dueOnly : Bool) : IO Endpoint.Result := do
  let valid ← load (verify state.Valid "The actual endpoint is invalid.")
  let ready ← load (verify (Endpoint.AckPrepared state) "ACK time or coverage is invalid.")
  let credit ← load (verify (Endpoint.ResponseAvailable state dueOnly) "The actual ACK cause is absent or early.")
  let _ := Endpoint.pureAck_success_enabled state dueOnly valid.property ready.property credit.property
  let retained := Endpoint.outputState_ackPrepared state ready.property
  let result := Endpoint.pureAck state true dueOnly
  let output ← packet result
  ensure (result.decision == .accepted (if dueOnly then .dispatchAck else .emitAck) &&
      output.packet.segment.payload.isEmpty && output.packet.segment.acknowledgment == state.core.receiveNext &&
      output.packet.segment.window.val == Endpoint.outputWindow state)
    "The derived output must acknowledge the actual cursor and current offered window."
  let _ := retained
  prepared result.state
  return result

private def arrival (count : Nat) : IO (Endpoint.State × Endpoint.State × EstablishedReceive.Input) := do
  let source := enabled client
  let target := enabled server
  let sent := Endpoint.send (Endpoint.write source (List.replicate count 42)).state count true
  let input ← packet sent
  let actual := Endpoint.receive target input
  ensure (actual.decision == .accepted (.receive 0 count)) "The actual active receive must release this in-order range."
  prepared actual.state
  return (sent.state, actual.state, input)

private def delayedAndDenied : IO Unit := do
  let (_, target, _) ← arrival 1
  ensure (!decide (Endpoint.ResponseAvailable target true) && decide (Endpoint.ResponseAvailable target false))
    "Delayed work permits an early explicit ACK, but not early due-only dispatch."
  let early := Endpoint.dispatchAck target true
  let denied := Endpoint.emitAck target false
  ensure (early.decision == .reject (.ack .early) && early.state == target && early.output.isNone &&
      denied.decision == .reject .policy && denied.state == target && denied.output.isNone)
    "An early or denied output must retain the actual ACK work."
  let past := Endpoint.advanceClock target 500
  ensure (past.decision == .ackUnsupported .deadline && past.state == target)
    "A clock jump beyond the actual pending deadline is not enabled."
  let atDue := Endpoint.advanceClock target 499
  let output ← acknowledge atDue.state true
  ensure (!decide (Endpoint.ResponseAvailable output.state false))
    "A consumed ACK group must provide no further response credit."

private def piggyback : IO Unit := do
  let (_, target, _) ← arrival 400
  let written := (Endpoint.write target [9, 10]).state
  let valid ← load (verify written.Valid "The written actual state is invalid.")
  let ready ← load (verify (Endpoint.SendReady written 2) "The new data prefix is not sendable.")
  let ack ← load (verify (Endpoint.AckPrepared written) "The piggyback ACK guards are invalid.")
  let _ := Endpoint.send_success_enabled written 2 valid.property ready.property ack.property
  let sent := Endpoint.send written 2 true
  let output ← packet sent
  ensure (sent.decision == .accepted (.send 2) && output.packet.segment.payload == [9, 10] &&
      output.packet.segment.acknowledgment == Seq.ofNat 500 &&
      (sent.state.ackReaction.map (·.credit)) == some 0)
    "New data must discharge the actual pending ACK group with its covering cursor."
  prepared sent.state

private def readPromise : IO Unit := do
  let (_, target, _) ← arrival 800
  let responded ← acknowledge target false
  let small := Endpoint.read responded.state 399
  prepared small.state
  ensure ((small.state.ackReaction.map (·.credit)) == some 0 && Endpoint.outputWindow small.state == 800)
    "A suppressed read must not create a larger output promise."
  let opened := Endpoint.read small.state 401
  prepared opened.state
  ensure ((opened.state.ackReaction.map (·.credit)) == some 1 && Endpoint.outputWindow opened.state == 1600)
    "A larger read must retain the actual proposed edge before output."
  let completed ← acknowledge opened.state true
  ensure ((completed.state.ackReaction.map (·.advertisement.edge)) == some 2400)
    "Successful output must commit the actual window-update promise."

private def oldRange : IO Unit := do
  let (_, target, input) ← arrival 1
  let responded ← acknowledge target false
  let repeated := Endpoint.receive responded.state input
  ensure (repeated.decision == .reject (.input .sequence) &&
      repeated.state.core.received == [42] && repeated.state.core.receiveNext == Seq.ofNat 101 &&
      (repeated.state.ackReaction.map (·.due)) == some (some 0))
    "An old whole range must create immediate feedback without releasing a second byte."
  prepared repeated.state
  let _ ← acknowledge repeated.state true
  pure ()

private def insufficientCoherence : IO Unit := do
  ensure (decide (Endpoint.AckCoherent uncoveredPromise) && !decide (Endpoint.AckPrepared uncoveredPromise) &&
      (Endpoint.emitAck uncoveredPromise true).decision == .reject (.ack .ledger))
    "Cursor coherence alone must not certify an uncovered read-edge promise."

def run : IO Unit := do
  insufficientCoherence
  delayedAndDenied
  piggyback
  readPromise
  oldRange
  IO.println "Active ACK enabledness tests passed."

end NetlibTest.TCPAckEnabled
