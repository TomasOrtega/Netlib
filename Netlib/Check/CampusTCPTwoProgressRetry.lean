import Netlib.Check.CampusTCPTwoProgressState
import Netlib.Check.CampusTCPTwoProgressSenderWindow
import Netlib.Check.CampusTCPTwoProgressWire
import Netlib.Check.CampusTCPGapTimeout
import Netlib.Check.CampusTCPRoundMonitorFacts

/-!
# Actual current-head retries for two TCP records

The timeout retains the old head and emits its actual range.
The joint report stores the same local retry operation and output.
-/

namespace Netlib.Check.CampusTCPTwoProgressRetry

open Packet Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart (TwoWriteInitial)
open CampusTCPTwoProgressState (Live)

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
  {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
  {initial : TwoWriteInitial cut sender gateway lower upper}

inductive HeadRange : S.Stage initial → S.Part → Recovery.Outstanding → List Recovery.Outstanding → Prop
  | lower (first : S.Original initial .lower) (second : S.Original initial .upper) (head : Recovery.Outstanding) :
      HeadRange (.both first second head) .lower head [second.entry]
  | upper (first : S.Original initial .lower) (second : S.Original initial .upper) (head : Recovery.Outstanding) :
      HeadRange (.tail first second head) .upper head []

variable {stage : S.Stage initial} {part : S.Part} {head : Recovery.Outstanding} {rest : List Recovery.Outstanding}
  {timeouts : Nat} {received : R.Stage} {actual : Step input}

theorem HeadRange.ledger (selected : HeadRange stage part head rest) : stage.ledger = head :: rest := by
  cases selected <;> rfl

theorem HeadRange.preparing (selected : HeadRange stage part head rest) : stage.preparing = false := by
  cases selected <;> rfl

theorem HeadRange.count (selected : HeadRange stage part head rest)
    (flight : S.Flight initial state stage timeouts) : head.count = (part.bytes lower upper).length := by
  cases selected <;> exact congrArg Recovery.Outstanding.count flight.headFixed

theorem HeadRange.identity (selected : HeadRange stage part head rest)
    (flight : S.Flight initial state stage timeouts) : head.id = initial.senderState.idle.recovery.nextId + part.index := by
  cases selected <;> exact congrArg Recovery.Outstanding.id flight.headFixed

theorem HeadRange.payload (selected : HeadRange stage part head rest)
    (flight : S.Flight initial state stage timeouts) : state.core.sent.take head.count = part.bytes lower upper := by
  have count := selected.count flight
  rw [flight.sent, count]
  cases selected
  · exact List.take_left
  · exact List.take_length

theorem HeadRange.sequence (selected : HeadRange stage part head rest)
    (flight : S.Flight initial state stage timeouts) :
    state.core.sendUna = (endpoint cut.endpoints sender).core.sendNext.add (part.offset lower) := by
  rw [flight.sendUna, CampusTCPTwoProgressSender.source, initial.senderState.idle.cursor]
  cases selected <;> rfl

theorem HeadRange.retired (selected : HeadRange stage part head rest) (now : Nat) :
    stage.retiredBytes = (stage.retry now).retiredBytes := by cases selected <;> rfl

structure Retry (_live : Live initial current stage timeouts received) (part : S.Part)
    (head : Recovery.Outstanding) (rest : List Recovery.Outstanding) (actual : Step input)
    extends CampusTCPGapTimeout.TimeoutMove current sender _live.senderFlight.recovery head rest actual where
  selection : HeadRange stage part head rest
  next : Live initial move.after (stage.retry _live.senderFlight.recovery.now) (timeouts + 1) received
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

private theorem retry_fields (live : Live initial current stage timeouts received)
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

private theorem retry_at (live : Live initial current stage timeouts received)
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
  let next : Live initial value.move.after (stage.retry live.senderFlight.recovery.now) (timeouts + 1) received := {
    anchor := ⟨CampusTCPTwoProgressState.endpoint_guards flight receiver, live.anchor.retained.trans value.move.retained,
      live.anchor.environment.trans environment⟩
    senderFlight := flight, receiverFacts := receiver
    gatewayState := live.gatewayState.reframe (serviceFrame gateway), gatewayWindow := live.gatewayWindow
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

theorem lower_at (live : Live initial current (.both first second head) timeouts received)
    (space : V.Reserved initial (endpoint current.endpoints sender) (.both first second head))
    (credit : timeouts < 2) (timer : live.senderFlight.recovery.deadline = some deadline)
    (due : deadline ≤ live.senderFlight.recovery.now) (elapsed : head.lastAt + live.senderFlight.recovery.rto ≤ live.senderFlight.recovery.now) :
    ∃ actual : Step input, Nonempty (Retry live .lower head [second.entry] actual) :=
  retry_at live space (.lower first second head) credit timer due elapsed

theorem upper_at (live : Live initial current (.tail first second head) timeouts received)
    (space : V.Reserved initial (endpoint current.endpoints sender) (.tail first second head))
    (credit : timeouts < 2) (timer : live.senderFlight.recovery.deadline = some deadline)
    (due : deadline ≤ live.senderFlight.recovery.now) (elapsed : head.lastAt + live.senderFlight.recovery.rto ≤ live.senderFlight.recovery.now) :
    ∃ actual : Step input, Nonempty (Retry live .upper head [] actual) :=
  retry_at live space (.upper first second head) credit timer due elapsed

def Retry.attempt {live : Live initial current stage timeouts received} (value : Retry live part head rest actual) :
    ApplicationTrace.OutputAt (applicationSteps value.move.after.endpoints sender) :=
  ⟨applicationSteps current.endpoints sender, value.facts.localStep, [], value.toTimeoutMove.selectedSteps,
    value.facts.packet, value.facts.origin⟩

theorem Retry.local_member {live : Live initial current stage timeouts received} (value : Retry live part head rest actual) :
    value.facts.localStep ∈ applicationSteps value.move.after.endpoints sender := value.attempt.member

theorem Retry.head_identity {live : Live initial current stage timeouts received} (value : Retry live part head rest actual) :
    head.id = initial.senderState.idle.recovery.nextId + part.index := value.selection.identity live.senderFlight

theorem Retry.head_count {live : Live initial current stage timeouts received} (value : Retry live part head rest actual) :
    head.count = (part.bytes lower upper).length := value.selection.count live.senderFlight

theorem Retry.payload {live : Live initial current stage timeouts received} (value : Retry live part head rest actual) :
    value.facts.packet.packet.segment.payload = part.bytes lower upper :=
  value.facts.payload.trans (value.selection.payload live.senderFlight)

theorem Step.lower_retry (actual : Step input) (live : Live initial current (.both first second head) timeouts received)
    (space : V.Reserved initial (endpoint current.endpoints sender) (.both first second head))
    (credit : timeouts < 2) (timer : live.senderFlight.recovery.deadline = some deadline)
    (due : deadline ≤ live.senderFlight.recovery.now) (elapsed : head.lastAt + live.senderFlight.recovery.rto ≤ live.senderFlight.recovery.now)
    (before : actual.before = current.report.final) (event : actual.event = .timeout sender true) :
    Nonempty (Retry live .lower head [second.entry] actual) := by
  obtain ⟨enabled, ⟨value⟩⟩ := lower_at live space credit timer due elapsed
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (value.move.beforeEq.trans before.symm) (value.facts.event.trans event.symm)
  exact ⟨same ▸ value⟩

theorem Step.upper_retry (actual : Step input) (live : Live initial current (.tail first second head) timeouts received)
    (space : V.Reserved initial (endpoint current.endpoints sender) (.tail first second head))
    (credit : timeouts < 2) (timer : live.senderFlight.recovery.deadline = some deadline)
    (due : deadline ≤ live.senderFlight.recovery.now) (elapsed : head.lastAt + live.senderFlight.recovery.rto ≤ live.senderFlight.recovery.now)
    (before : actual.before = current.report.final) (event : actual.event = .timeout sender true) :
    Nonempty (Retry live .upper head [] actual) := by
  obtain ⟨enabled, ⟨value⟩⟩ := upper_at live space credit timer due elapsed
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (value.move.beforeEq.trans before.symm) (value.facts.event.trans event.symm)
  exact ⟨same ▸ value⟩

end Netlib.Check.CampusTCPTwoProgressRetry
