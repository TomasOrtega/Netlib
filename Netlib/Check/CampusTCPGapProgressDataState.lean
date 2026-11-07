import Netlib.Check.CampusTCPGapProgressState
import Netlib.Check.CampusTCPGapDelivery
import Netlib.Check.CampusTCPGapOldData

namespace Netlib.Check.CampusTCPGapProgressDataState

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPGapProgressStart
open CampusTCPRound (Cut)
open CampusTCPGapProgressPhaseBase (Move)
open CampusTCPGapProgressState (Live)

namespace R
export CampusTCPGapProgressReceiver (Facts source)
end R
namespace D
export CampusTCPRoundDelivery (Delivery)
end D

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {lower upper : List UInt8}
variable {initial : GapInitial cut sender lower upper} {retries : Nat} {released : Bool}
variable {index : Nat} {served : Served input} {emission : WireForwarding.Emission served.ticket.value.source.packet}
variable {emitted : served.evidence.output = some emission}

private def deliveryMove (current : Cut input complete)
    (delivery : D.Delivery current.report complete current.endpoints index served emission emitted) : Move current delivery.step :=
  let next : Cut input complete := ⟨_, delivery.append current.supported current.finished,
    delivery.append_supported _ _, rfl, delivery.updated, delivery.connection⟩
  ⟨next, delivery.beforeEq, delivery.supported, delivery.passed, rfl, rfl⟩

private theorem delivery_gateway
    (delivery : D.Delivery current.report complete current.endpoints index served emission emitted) (gateway : Gateway) :
    beforeService input (deliveryMove current delivery).after.report.final gateway = beforeService input current.report.final gateway := by
  rw [(deliveryMove current delivery).final, ← delivery.beforeEq]
  exact CampusTCPRoundLocal.step_service_nonservice delivery.step (by rw [delivery.event]; trivial) gateway

private theorem delivery_environment
    (delivery : D.Delivery current.report complete current.endpoints index served emission emitted) :
    CampusTCPRoundEnvironment.environment current.report.final =
      CampusTCPRoundEnvironment.environment (deliveryMove current delivery).after.report.final := by
  rw [(deliveryMove current delivery).final]
  exact delivery.environment

private theorem delivery_read
    (delivery : D.Delivery current.report complete current.endpoints index served emission emitted) :
    delivery.localStep.readBytes = [] := by
  simp only [ApplicationTrace.Step.readBytes, delivery.localStep.computed, delivery.localEvent, ApplicationTrace.evaluate]
  exact (Endpoint.receiveEffect_effects delivery.localStep.before emission.asInput).read

private theorem selected_receiver
    (delivery : D.Delivery current.report complete current.endpoints index served emission emitted)
    (actor : served.ticket.value.produced.actor = sender) :
    endpoint (deliveryMove current delivery).after.endpoints sender.other = delivery.after := by
  change endpoint delivery.updated sender.other = delivery.after
  simpa only [actor] using delivery.selected

private theorem sender_peer
    (delivery : D.Delivery current.report complete current.endpoints index served emission emitted)
    (actor : served.ticket.value.produced.actor = sender) :
    endpoint (deliveryMove current delivery).after.endpoints sender = endpoint current.endpoints sender := by
  change endpoint delivery.updated sender = endpoint current.endpoints sender
  have twice : sender.other.other = sender := by cases sender <;> rfl
  simpa only [actor, twice] using delivery.peer

private theorem pending_work (facts : R.Facts initial state true) (available : Endpoint.ResponseAvailable state false) :
    facts.reaction.work.pending ≠ [] := by
  simpa only [Endpoint.ResponseAvailable, facts.ackRuntime, Bool.false_eq_true, false_implies, and_true] using available

private def receipt_live (live : Live initial current retries released)
    (delivery : D.Delivery current.report complete current.endpoints index served emission emitted)
    (actor : served.ticket.value.produced.actor = sender) (receiver : R.Facts initial delivery.after true)
    (release : delivery.localStep.releasedPayload = if released then [] else lower ++ upper) :
    Live initial (deliveryMove current delivery).after retries true := by
  let move := deliveryMove current delivery
  have receiverAt : R.Facts initial (endpoint move.after.endpoints sender.other) true := by
    rw [selected_receiver delivery actor]
    exact receiver
  have flight : CampusTCPGapProgressSender.Flight initial.flight (endpoint move.after.endpoints sender) retries := by
    rw [sender_peer delivery actor]
    exact live.senderFlight
  have history : CampusTCPGapProgressHistory.History cut move.after sender.other (lower ++ upper) true := by
    have steps : applicationSteps move.after.endpoints sender.other = applicationSteps current.endpoints sender.other ++ [delivery.localStep] := by
      change applicationSteps delivery.updated sender.other = _
      simpa only [actor] using delivery.selectedSteps
    cases released with
    | false =>
      exact live.history.first delivery.localStep steps
        (by
          intro empty
          have count := congrArg List.length empty
          have positive := List.length_pos_iff.mpr initial.lowerNonempty
          simp only [List.length_append, List.length_nil] at count
          omega) release (delivery_read delivery)
    | true => exact live.history.quiet delivery.localStep steps release (delivery_read delivery)
  exact ⟨⟨CampusTCPGapProgressState.endpoint_guards flight receiverAt, live.anchor.retained.trans move.retained,
    live.anchor.environment.trans (delivery_environment delivery)⟩,
    flight, receiverAt, CampusTCPGapProgressState.gateway_reframe live.gateway (delivery_gateway delivery .standby), history⟩

structure Received (live : Live initial current retries released) (index : Nat) (served : Served input)
    (emission : WireForwarding.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission) where
  actor : served.ticket.value.produced.actor = sender
  delivery : D.Delivery current.report complete current.endpoints index served emission emitted
  move : Move current delivery.step
  next : Live initial move.after retries true
  selected : endpoint move.after.endpoints sender.other = delivery.after
  localRelease : delivery.localStep.releasedPayload = if released then [] else lower ++ upper
  releasedBytes : Endpoint.receivedBytes (endpoint current.endpoints sender.other) emission.asInput =
    if released then [] else lower ++ upper
  read : delivery.step.result.read = []
  available : Endpoint.ResponseAvailable (endpoint move.after.endpoints sender.other) false
  pending : next.receiverFacts.reaction.work.pending ≠ []
  gap : released = false → ∃ actual : CampusTCPGapDelivery.GapDelivered current.report complete current.endpoints index served emission emitted
    initial.receiver.run live.receiverFacts.recovery live.receiverFacts.reaction, actual.toDelivery = delivery
  old : released = true → ∃ actual : CampusTCPTimedOldData.OldDataDelivered current.report complete current.endpoints index served emission emitted
    live.receiverFacts.reaction, actual.toDelivery = delivery
  first : next.history.streams.first = if released then live.history.streams.first else some delivery.localStep

theorem of_gap (live : Live initial current retries false)
    (delivery : CampusTCPGapDelivery.GapDelivered current.report complete current.endpoints index served emission emitted
      initial.receiver.run live.receiverFacts.recovery live.receiverFacts.reaction)
    (actor : served.ticket.value.produced.actor = sender) (payload : emission.asInput.packet.segment.payload = lower) :
    Nonempty (Received live index served emission emitted) := by
  have filled : Endpoint.GapFilled (endpoint current.endpoints sender.other) emission.asInput initial.receiver.run
      live.receiverFacts.recovery live.receiverFacts.reaction := by simpa only [actor] using delivery.filled
  have receiver : R.Facts initial delivery.after true := by
    rw [delivery.afterEq]
    simpa only [actor] using live.receiverFacts.gap_filled emission.asInput payload filled
  have localRelease : delivery.localStep.releasedPayload = lower ++ upper := by
    rw [delivery.localReleased, payload, initial.receiver.bytes]
  let move := deliveryMove current delivery.toDelivery
  let next := receipt_live live delivery.toDelivery actor receiver localRelease
  have selected : endpoint move.after.endpoints sender.other = delivery.after := selected_receiver delivery.toDelivery actor
  have available : Endpoint.ResponseAvailable (endpoint move.after.endpoints sender.other) false := by
    rw [selected]
    exact delivery.available_early
  refine ⟨⟨actor, delivery.toDelivery, move, next, selected, localRelease, ?_, delivery.read, available,
    pending_work next.receiverFacts available, fun _ => ⟨delivery, rfl⟩, ?_, rfl⟩⟩
  · simpa only [actor, payload, initial.receiver.bytes, Bool.false_eq_true, ite_false] using delivery.bytes
  · intro impossible
    cases impossible

theorem of_old (live : Live initial current retries true)
    (delivery : CampusTCPTimedOldData.OldDataDelivered current.report complete current.endpoints index served emission emitted live.receiverFacts.reaction)
    (actor : served.ticket.value.produced.actor = sender) : Nonempty (Received live index served emission emitted) := by
  have receiver : R.Facts initial delivery.after true := by
    rw [delivery.afterEq]
    simpa only [actor] using live.receiverFacts.sequence
  let move := deliveryMove current delivery.toDelivery
  let next := receipt_live live delivery.toDelivery actor receiver delivery.localReleased
  have selected : endpoint move.after.endpoints sender.other = delivery.after := selected_receiver delivery.toDelivery actor
  have available : Endpoint.ResponseAvailable (endpoint move.after.endpoints sender.other) false := by
    rw [selected]
    exact delivery.available_early
  refine ⟨⟨actor, delivery.toDelivery, move, next, selected, delivery.localReleased, ?_, delivery.read, available,
    pending_work next.receiverFacts available, ?_, fun _ => ⟨delivery, rfl⟩, rfl⟩⟩
  · simpa only [actor, ite_true] using delivery.released
  · intro impossible
    cases impossible

theorem receive_at (live : Live initial current retries released) (index : Nat) (served : Served input)
    (found : current.report.final.services[index]? = some served)
    (emission : WireForwarding.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (application : CampusTCPDeliveryEnabled.ApplicationSource served.ticket.value.produced)
    (pending : CampusTCPDeliveryEnabled.LinkPending current.report.final index)
    (actor : served.ticket.value.produced.actor = sender)
    (tuple : emission.asInput.packet.header = (R.source initial).core.inbound)
    (controls : EstablishedReceive.control emission.asInput.packet.segment = none)
    (ack : Flags.ack emission.asInput.packet.segment.flags = true)
    (sequence : emission.asInput.packet.segment.sequence = initial.lowerSource.attempt.output.packet.segment.sequence)
    (ackOld : Seq.distance emission.asInput.packet.segment.acknowledgment (R.source initial).core.sendUna ≤ EstablishedReceive.maxSendWindow)
    (payload : emission.asInput.packet.segment.payload = lower) :
    Nonempty (Received live index served emission emitted) := by
  cases released with
  | false =>
    have conditions : Endpoint.GapReceiveConditions (endpoint current.endpoints served.ticket.value.produced.actor.other)
        emission.asInput initial.receiver.run live.receiverFacts.recovery live.receiverFacts.reaction := by
      rw [actor]
      exact live.receiverFacts.gap_conditions emission.asInput tuple controls ack sequence ackOld payload
    obtain ⟨delivery⟩ := CampusTCPGapDelivery.Report.deliver_gap current.report complete current.endpoints current.connection index served found
      emission emitted application pending initial.receiver.run live.receiverFacts.recovery live.receiverFacts.reaction conditions
    exact of_gap live delivery actor payload
  | true =>
    have ready : CampusTCPGapOldData.OldSpanReady (endpoint current.endpoints served.ticket.value.produced.actor.other)
        emission.asInput live.receiverFacts.reaction (lower.length + upper.length) := by
      rw [actor]
      exact live.receiverFacts.old_span_ready emission.asInput tuple controls sequence payload
    obtain ⟨delivery⟩ := CampusTCPGapOldData.Report.deliver_old_span current.report complete current.endpoints current.connection index served found
      emission emitted application pending live.receiverFacts.reaction (lower.length + upper.length) ready
    exact of_old live delivery actor

private theorem application_read (before : State input) (actor : Actor) (event : T.Event)
    (effect : Effect input) (localStep : T.Step) (computed : applyApplication input before actor event = .ok effect)
    (recorded : effect.application = some (actor, localStep)) : effect.read = localStep.result.read := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; simp_all only [Option.some.injEq, Prod.mk.injEq])
    | (cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [unsupported] at recorded
    cases recorded

private def ackMove (current : Cut input complete) (actual : Step input)
    (facts : CampusTCPRoundAck.AckFacts current.report.final complete current.endpoints sender.other actual) : Move current actual :=
  let report := CampusTCPSchedule.Report.appendStep current.report current.supported current.finished actual facts.beforeEq facts.supported
  let next : Cut input complete := ⟨_, report, CampusTCPSchedule.Report.appendStep_supported _ _ _ _ _ _,
    rfl, facts.after, facts.connection⟩
  ⟨next, facts.beforeEq, facts.supported, facts.passed, rfl, rfl⟩

structure Acked (live : Live initial current retries true) (actual : Step input) where
  facts : CampusTCPRoundAck.AckFacts current.report.final complete current.endpoints sender.other actual
  move : Move current actual
  next : Live initial move.after retries true
  selected : endpoint move.after.endpoints sender.other = Endpoint.outputState (endpoint current.endpoints sender.other)
  peer : endpoint move.after.endpoints sender = endpoint current.endpoints sender
  localRelease : facts.localStep.releasedPayload = []
  localRead : facts.localStep.readBytes = []
  read : actual.result.read = []
  covering : facts.packet.packet.segment.acknowledgment = (R.source initial).core.receiveNext.add (lower.length + upper.length)
  sequence : facts.packet.packet.segment.sequence = (R.source initial).core.sendNext
  header : facts.packet.packet.header = Output.reverse (R.source initial).core.inbound
  first : next.history.streams.first = live.history.streams.first

theorem ack_at (live : Live initial current retries true) (pending : live.receiverFacts.reaction.work.pending ≠ []) :
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
  have receiver : R.Facts initial (endpoint move.after.endpoints sender.other) true := by
    rw [selected]
    exact live.receiverFacts.output
  have flight : CampusTCPGapProgressSender.Flight initial.flight (endpoint move.after.endpoints sender) retries := by
    rw [peer]
    exact live.senderFlight
  have release : facts.localStep.releasedPayload = [] := by
    simp only [ApplicationTrace.Step.releasedPayload, ApplicationTrace.releasedPayload, facts.localEvent]
  obtain ⟨wire, emitted, _, _, _, _, _, _, _, _⟩ := live.receiverFacts.emit_ack pending
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
    exact (show actual.result.read = facts.localStep.readBytes by simpa only [final, ApplicationTrace.Step.readBytes] using same).trans localRead
  have environment : CampusTCPRoundEnvironment.environment current.report.final =
      CampusTCPRoundEnvironment.environment move.after.report.final := by rw [move.final]; exact facts.environment
  have gateway (selected : Gateway) : beforeService input move.after.report.final selected = beforeService input current.report.final selected := by
    rw [move.final, ← facts.beforeEq]
    exact CampusTCPRoundLocal.step_service_nonservice actual (by rw [facts.event]; trivial) selected
  have steps : applicationSteps move.after.endpoints sender.other = applicationSteps current.endpoints sender.other ++ [facts.localStep] := by
    change applicationSteps facts.after sender.other = _
    exact facts.selectedSteps
  let history := live.history.quiet facts.localStep steps release localRead
  let next : Live initial move.after retries true :=
    ⟨⟨CampusTCPGapProgressState.endpoint_guards flight receiver, live.anchor.retained.trans move.retained,
      live.anchor.environment.trans environment⟩, flight, receiver,
      CampusTCPGapProgressState.gateway_reframe live.gateway (gateway .standby), history⟩
  refine ⟨actual, ⟨⟨facts, move, next, selected, peer, release, localRead, read, ?_, ?_, ?_, rfl⟩⟩⟩
  · simpa only [live.receiverFacts.receiveNext, ite_true] using facts.acknowledgment
  · exact facts.sequence.trans live.receiverFacts.sendNext
  · exact facts.header.trans (congrArg Output.reverse live.receiverFacts.inbound)

theorem Step.receive (actual : Step input) (live : Live initial current retries released)
    (before : actual.before = current.report.final) (event : actual.event = .deliver index emission.bytes true)
    (found : current.report.final.services[index]? = some served)
    (application : CampusTCPDeliveryEnabled.ApplicationSource served.ticket.value.produced)
    (pending : CampusTCPDeliveryEnabled.LinkPending current.report.final index)
    (actor : served.ticket.value.produced.actor = sender)
    (tuple : emission.asInput.packet.header = (R.source initial).core.inbound)
    (controls : EstablishedReceive.control emission.asInput.packet.segment = none)
    (ack : Flags.ack emission.asInput.packet.segment.flags = true)
    (sequence : emission.asInput.packet.segment.sequence = initial.lowerSource.attempt.output.packet.segment.sequence)
    (ackOld : Seq.distance emission.asInput.packet.segment.acknowledgment (R.source initial).core.sendUna ≤ EstablishedReceive.maxSendWindow)
    (payload : emission.asInput.packet.segment.payload = lower) :
    ∃ result : Received live index served emission emitted, result.delivery.step = actual := by
  obtain ⟨result⟩ := receive_at live index served found emission emitted application pending actor tuple controls ack sequence ackOld payload
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event result.delivery.step actual
    (result.move.beforeEq.trans before.symm) (result.delivery.event.trans event.symm)
  exact ⟨result, same⟩

theorem Step.emit_ack (actual : Step input) (live : Live initial current retries true)
    (before : actual.before = current.report.final) (event : actual.event = .emitAck sender.other true)
    (pending : live.receiverFacts.reaction.work.pending ≠ []) : Nonempty (Acked live actual) := by
  obtain ⟨enabled, ⟨result⟩⟩ := ack_at live pending
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (result.move.beforeEq.trans before.symm) (result.facts.event.trans event.symm)
  subst enabled
  exact ⟨result⟩

end Netlib.Check.CampusTCPGapProgressDataState
