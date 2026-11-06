import Netlib.Check.CampusTCPTwoProgressSenderWindow
import Netlib.Check.CampusTCPTwoProgressWire

/-!
# Actual ACK output from current two-record state

The current pending work supplies the ACK cause.
The output and both endpoint histories belong to the same report.
-/

namespace Netlib.Check.CampusTCPTwoProgressAckOutput

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart CampusTCPTwoProgressState

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {sent : CampusTCPTwoProgressSender.Stage initial} {timeouts : Nat} {received : CampusTCPTwoProgressReceiver.Stage}

private theorem application_read (before : State input) (actor : Actor) (event : T.Event)
    (effect : Effect input) (operation : T.Step) (computed : applyApplication input before actor event = .ok effect)
    (recorded : effect.application = some (actor, operation)) : effect.read = operation.result.read := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; simp_all only [Option.some.injEq, Prod.mk.injEq])
    | (cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)
  simp only [unsupported] at recorded
  cases recorded

def ackMove (current : Cut input complete) (actual : Step input)
    (facts : CampusTCPRoundAck.AckFacts current.report.final complete current.endpoints sender.other actual) : Move current actual :=
  let report := CampusTCPSchedule.Report.appendStep current.report current.supported current.finished actual facts.beforeEq facts.supported
  let next : Cut input complete := ⟨_, report, CampusTCPSchedule.Report.appendStep_supported _ _ _ _ _ _,
    rfl, facts.after, facts.connection⟩
  ⟨next, facts.beforeEq, facts.supported, facts.passed, rfl, rfl⟩

structure Acked (live : Live initial current sent timeouts received) (actual : Step input) where
  facts : CampusTCPRoundAck.AckFacts current.report.final complete current.endpoints sender.other actual
  move : Move current actual
  next : Live initial move.after sent timeouts received
  reserve : CampusTCPTwoProgressSenderWindow.Reserved initial (endpoint move.after.endpoints sender) sent
  fields : CampusTCPTwoProgressWire.AckFields initial (received.bytes lower upper).length facts.produced
  selected : endpoint move.after.endpoints sender.other = Endpoint.outputState (endpoint current.endpoints sender.other)
  peer : endpoint move.after.endpoints sender = endpoint current.endpoints sender
  localRelease : facts.localStep.releasedPayload = []
  localRead : facts.localStep.readBytes = []
  read : actual.result.read = []

theorem ack_at (live : Live initial current sent timeouts received)
    (space : CampusTCPTwoProgressSenderWindow.Reserved initial (endpoint current.endpoints sender) sent)
    (pending : live.receiverFacts.reaction.work.pending ≠ []) :
    ∃ actual : Step input, Nonempty (Acked live actual) := by
  have available := Endpoint.responseAvailable_of_pending _ live.receiverFacts.reaction live.receiverFacts.ackRuntime pending
  obtain ⟨actual, ⟨facts⟩⟩ := CampusTCPRoundAck.Report.emitAck_enabled current.report complete current.endpoints current.connection
    sender.other live.receiverFacts.prepared available
  let move := ackMove current actual facts
  have selected : endpoint move.after.endpoints sender.other = Endpoint.outputState (endpoint current.endpoints sender.other) := by
    change endpoint facts.after sender.other = _
    exact facts.selected
  have peer : endpoint move.after.endpoints sender = endpoint current.endpoints sender := by
    change endpoint facts.after sender = _
    have twice : sender.other.other = sender := by cases sender <;> rfl
    simpa only [twice] using facts.peer
  obtain ⟨wire, emitted, encoded, _, _, _, _, _, _⟩ := live.receiverFacts.emit_ack pending
  have packet : wire = facts.packet := Except.ok.inj (encoded.symm.trans facts.encoded)
  rw [packet] at emitted
  have receiver : CampusTCPTwoProgressReceiver.Facts initial (endpoint move.after.endpoints sender.other) received := by
    rw [selected]
    exact live.receiverFacts.output facts.packet emitted
  have flight : CampusTCPTwoProgressSender.Flight initial (endpoint move.after.endpoints sender) sent timeouts := by
    rw [peer]
    exact live.senderFlight
  have release : facts.localStep.releasedPayload = [] := by
    simp only [ApplicationTrace.Step.releasedPayload, ApplicationTrace.releasedPayload, facts.localEvent]
  have localRead : facts.localStep.readBytes = [] := by
    simp only [ApplicationTrace.Step.readBytes, facts.localStep.computed, facts.localEvent,
      ApplicationTrace.evaluate, facts.localBefore, emitted]
  have read : actual.result.read = [] := by
    obtain ⟨core, custody, computed, final⟩ := actual.processed
    have applied : applyApplication input actual.before sender.other (.emitAck true) = .ok core := by
      simpa only [facts.event, processCore] using computed
    have recorded : core.application = some (sender.other, facts.localStep) := by
      simpa only [final] using facts.application
    have same := application_read actual.before sender.other (.emitAck true) core facts.localStep applied recorded
    exact (show actual.result.read = facts.localStep.readBytes by
      simpa only [final, ApplicationTrace.Step.readBytes] using same).trans localRead
  have environment : CampusTCPRoundEnvironment.environment current.report.final =
      CampusTCPRoundEnvironment.environment move.after.report.final := by rw [move.final]; exact facts.environment
  have gatewayFrame (selected : Gateway) : beforeService input move.after.report.final selected = beforeService input current.report.final selected := by
    rw [move.final, ← facts.beforeEq]
    exact CampusTCPRoundLocal.step_service_nonservice actual (by rw [facts.event]; trivial) selected
  have steps : applicationSteps move.after.endpoints sender.other = applicationSteps current.endpoints sender.other ++ [facts.localStep] := by
    change applicationSteps facts.after sender.other = _
    exact facts.selectedSteps
  let history := live.history.quiet facts.localStep steps release localRead
  let next : Live initial move.after sent timeouts received :=
    ⟨⟨endpoint_guards flight receiver, live.anchor.retained.trans move.retained,
      live.anchor.environment.trans environment⟩, flight, receiver,
      live.gatewayState.reframe (gatewayFrame gateway), live.gatewayWindow, history⟩
  have fields : CampusTCPTwoProgressWire.AckFields initial (received.bytes lower upper).length facts.produced := by
    rw [facts.production]
    apply CampusTCPTwoProgressWire.ack_fields initial facts.localStep facts.packet facts.origin
    · rw [facts.localBefore]
      exact live.receiverFacts
    · rw [facts.localBefore]
      exact facts.encoded
  exact ⟨actual, ⟨⟨facts, move, next, by rw [peer]; exact space, fields, selected, peer, release, localRead, read⟩⟩⟩

theorem Step.emit_ack (actual : Step input) (live : Live initial current sent timeouts received)
    (space : CampusTCPTwoProgressSenderWindow.Reserved initial (endpoint current.endpoints sender) sent)
    (before : actual.before = current.report.final) (event : actual.event = .emitAck sender.other true)
    (pending : live.receiverFacts.reaction.work.pending ≠ []) : Nonempty (Acked live actual) := by
  obtain ⟨enabled, ⟨result⟩⟩ := ack_at live space pending
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (result.move.beforeEq.trans before.symm) (result.facts.event.trans event.symm)
  subst enabled
  exact ⟨result⟩

end Netlib.Check.CampusTCPTwoProgressAckOutput
