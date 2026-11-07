import Netlib.Check.CampusTCPTwoTransferState
import Netlib.Check.CampusTCPTwoProgressRetry

namespace Netlib.Check.CampusTCPTwoTransferLocatedTimeout

open Packet Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart (TwoWriteInitial)
open CampusTCPTwoTransferState (LiveAt)
open CampusTCPTwoProgressRetry (HeadRange)

namespace S
export CampusTCPTwoProgressSender (Part Original Stage Flight)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage Facts)
end R
namespace W
export CampusTCPTwoProgressWire (DataFields)
end W
namespace V
export CampusTCPTwoProgressSenderWindow (Reserved)
end V

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {stage : S.Stage initial} {part : S.Part} {head : Recovery.Outstanding} {rest : List Recovery.Outstanding}
variable {timeouts deadline : Nat} {received : R.Stage} {actual : Step input}

structure Retry (_live : LiveAt initial current location stage timeouts received) (part : S.Part)
    (head : Recovery.Outstanding) (rest : List Recovery.Outstanding) (actual : Step input)
    extends CampusTCPGapTimeout.TimeoutMove current sender _live.senderFlight.recovery head rest actual where
  selection : HeadRange stage part head rest
  next : LiveAt initial move.after location (stage.retry _live.senderFlight.recovery.now) (timeouts + 1) received
  reserve : V.Reserved initial (endpoint move.after.endpoints sender) (stage.retry _live.senderFlight.recovery.now)
  encoded : Endpoint.emitAt (endpoint current.endpoints sender) (endpoint current.endpoints sender).core.sendUna
    (part.bytes lower upper) = .ok facts.packet
  fields : W.DataFields initial (part.offset lower) (part.bytes lower upper) facts.produced
  source : move.after.report.final.outputs[current.report.final.outputs.length]? = some facts.produced
  pending : IngressPending move.after.report.final current.report.final.outputs.length
  minted : ∃ item ∈ move.after.report.final.custody.pending,
    item.value.parent = none ∧ item.value.payload = .ingress current.report.final.outputs.length facts.produced
  packetID : Nat
  custody : move.after.report.final.custody.pendingID (Transit.ingressAt current.report.final.outputs.length) = some packetID
  serviceFrame : ∀ selected, beforeService input move.after.report.final selected = beforeService input current.report.final selected
  environment : CampusTCPRoundEnvironment.environment current.report.final =
    CampusTCPRoundEnvironment.environment move.after.report.final
  history : next.history.operations = _live.history.operations

private theorem retry_fields (live : LiveAt initial current location stage timeouts received)
    (selected : HeadRange stage part head rest)
    (value : CampusTCPGapTimeout.TimeoutMove current sender live.senderFlight.recovery head rest actual) :
    W.DataFields initial (part.offset lower) (part.bytes lower upper) value.facts.produced := by
  have fields := value.facts.source_fields
  refine ⟨?_, ?_, ?_, ?_, fields.2.2.2.2.1, ?_, ?_⟩
  · rw [fields.1, live.senderFlight.inbound]
    exact initial.input_tuple sender
  · exact fields.2.1.trans (selected.sequence live.senderFlight)
  · exact fields.2.2.1.trans live.senderFlight.receiveNext
  · exact fields.2.2.2.1.trans (selected.payload live.senderFlight)
  · rw [fields.2.2.2.2.2]
    decide
  · rw [value.facts.production]
    change CampusTCPTwoProgressReceiver.advertisedFloor initial ≤ value.facts.packet.packet.segment.window.val
    rw [value.facts.window]
    exact Nat.le_trans live.senderFlight.advertised
      (Endpoint.offeredWindow_le_outputWindow _ live.senderFlight.prepared.1)

theorem retry_at (live : LiveAt initial current location stage timeouts received)
    (space : V.Reserved initial (endpoint current.endpoints sender) stage)
    (selected : HeadRange stage part head rest) (credit : timeouts < 2)
    (timer : live.senderFlight.recovery.deadline = some deadline) (due : deadline ≤ live.senderFlight.recovery.now)
    (elapsed : head.lastAt + live.senderFlight.recovery.rto ≤ live.senderFlight.recovery.now) :
    ∃ actual : Step input, Nonempty (Retry live part head rest actual) := by
  let ready := live.senderFlight.timeout_ready head rest selected.ledger credit timer due elapsed
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPGapTimeout.timeout_at current sender live.senderFlight.recovery head rest deadline
    ready live.senderFlight.storage
  have flight : S.Flight initial (endpoint value.move.after.endpoints sender)
      (stage.retry live.senderFlight.recovery.now) (timeouts + 1) := by
    rw [value.selected]
    exact live.senderFlight.retry head rest selected.ledger selected.preparing credit timer due elapsed
  have receiver : R.Facts initial (endpoint value.move.after.endpoints sender.other) received := by
    rw [value.peer]
    exact live.receiverFacts
  have serviceFrame : ∀ chosen, beforeService input value.move.after.report.final chosen =
      beforeService input current.report.final chosen := by
    intro chosen
    rw [value.move.final, CampusTCPRoundLocal.step_service_nonservice actual (by rw [value.facts.event]; trivial), value.facts.beforeEq]
  have environment : CampusTCPRoundEnvironment.environment current.report.final =
      CampusTCPRoundEnvironment.environment value.move.after.report.final := by
    rw [value.move.final]
    exact value.facts.environment
  let next : LiveAt initial value.move.after location (stage.retry live.senderFlight.recovery.now) (timeouts + 1) received := {
    anchor := ⟨⟨live.anchor.retained.trans value.move.retained, fun selected => (live.anchor.policy selected).trans
      (congrArg CampusTCPService.Before.environment (serviceFrame selected)).symm⟩,
      CampusTCPTwoProgressState.endpoint_guards flight receiver⟩
    senderFlight := flight, receiverFacts := receiver
    gatewayState := live.gatewayState.reframe (serviceFrame location), gatewayWindow := live.gatewayWindow
    history := live.history.same value.peerSteps }
  have reserve : V.Reserved initial (endpoint value.move.after.endpoints sender) (stage.retry live.senderFlight.recovery.now) := by
    apply CampusTCPTwoProgressSenderWindow.congr space
    · rw [value.selected]
      rfl
    · exact Nat.le_of_eq (selected.retired live.senderFlight.recovery.now)
  have encoded : Endpoint.emitAt (endpoint current.endpoints sender) (endpoint current.endpoints sender).core.sendUna
      (part.bytes lower upper) = .ok value.facts.packet := by
    simpa only [selected.payload live.senderFlight] using value.facts.encoded
  obtain ⟨id, custody⟩ := CampusTCPRoundMonitorFacts.output_pending actual value.facts.produced value.facts.output
  refine ⟨actual, ⟨{
    toTimeoutMove := value, selection := selected, next, reserve, encoded
    fields := retry_fields live selected value, source := ?_, pending := ?_, minted := ?_
    packetID := id, custody := ?_, serviceFrame, environment, history := rfl }⟩⟩
  · rw [value.move.final]
    exact value.facts.source
  · rw [value.move.final]
    exact value.facts.pending
  · rw [value.move.final]
    exact value.facts.minted
  · rw [value.move.final, ← value.facts.beforeEq]
    exact custody

def Retry.attempt {live : LiveAt initial current location stage timeouts received} (value : Retry live part head rest actual) :
    ApplicationTrace.OutputAt (applicationSteps value.move.after.endpoints sender) :=
  ⟨applicationSteps current.endpoints sender, value.facts.localStep, [], value.toTimeoutMove.selectedSteps,
    value.facts.packet, value.facts.origin⟩

theorem Retry.local_member {live : LiveAt initial current location stage timeouts received} (value : Retry live part head rest actual) :
    value.facts.localStep ∈ applicationSteps value.move.after.endpoints sender := value.attempt.member

theorem Retry.head_identity {live : LiveAt initial current location stage timeouts received} (value : Retry live part head rest actual) :
    head.id = initial.senderState.idle.recovery.nextId + part.index := value.selection.identity live.senderFlight

theorem Retry.head_count {live : LiveAt initial current location stage timeouts received} (value : Retry live part head rest actual) :
    head.count = (part.bytes lower upper).length := value.selection.count live.senderFlight

theorem Retry.payload {live : LiveAt initial current location stage timeouts received} (value : Retry live part head rest actual) :
    value.facts.packet.packet.segment.payload = part.bytes lower upper :=
  value.facts.payload.trans (value.selection.payload live.senderFlight)

theorem Step.timeout (actual : Step input) (live : LiveAt initial current location stage timeouts received)
    (space : V.Reserved initial (endpoint current.endpoints sender) stage)
    (selected : HeadRange stage part head rest) (credit : timeouts < 2)
    (timer : live.senderFlight.recovery.deadline = some deadline) (due : deadline ≤ live.senderFlight.recovery.now)
    (elapsed : head.lastAt + live.senderFlight.recovery.rto ≤ live.senderFlight.recovery.now)
    (before : actual.before = current.report.final) (event : actual.event = .timeout sender true) :
    Nonempty (Retry live part head rest actual) := by
  obtain ⟨enabled, ⟨value⟩⟩ := retry_at live space selected credit timer due elapsed
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (value.move.beforeEq.trans before.symm) (value.facts.event.trans event.symm)
  exact ⟨same ▸ value⟩

end Netlib.Check.CampusTCPTwoTransferLocatedTimeout
