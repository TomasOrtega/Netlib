import Netlib.Protocol.TCP.EndpointGapReceiveEnabled
import Netlib.Check.CampusTCPTimedOldData
import Netlib.Check.CampusTCPRecoveryRoundPhaseBase
import Netlib.Check.CampusTCPRoundAck

namespace Netlib.Check.CampusTCPGapDelivery

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTimedOldData (finish_application_delivery delivery_consumed)

namespace D
export CampusTCPDeliveryEnabled (ApplicationSource LinkPending)
end D

variable {input : CampusTCPModel.Input} {events : List CampusTCPModel.Event}

structure GapDelivered (report : Report input events) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (index : Nat) (served : Served input)
    (emission : WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission) (upper : ReceiveReassembly.Run)
    (recovery : Recovery.State) (reaction : AckReaction.State)
    extends CampusTCPRoundDelivery.Delivery report complete endpoints index served emission emitted where
  conditions : Endpoint.GapReceiveConditions (endpoint endpoints served.ticket.value.produced.actor.other)
    emission.asInput upper recovery reaction
  filled : Endpoint.GapFilled (endpoint endpoints served.ticket.value.produced.actor.other)
    emission.asInput upper recovery reaction
  afterEq : after = Endpoint.gapAfter (endpoint endpoints served.ticket.value.produced.actor.other)
    emission.asInput upper recovery reaction
  localReleased : localStep.releasedPayload = emission.asInput.packet.segment.payload ++ upper.bytes
  read : step.result.read = []
  available : Endpoint.ResponseAvailable after true

theorem Report.deliver_gap (report : Report input events) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : report.final.connection = .application complete endpoints)
    (index : Nat) (served : Served input) (found : report.final.services[index]? = some served)
    (emission : WireForwarding.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (application : D.ApplicationSource served.ticket.value.produced) (pending : D.LinkPending report.final index)
    (upper : ReceiveReassembly.Run) (recovery : Recovery.State) (reaction : AckReaction.State)
    (conditions : Endpoint.GapReceiveConditions (endpoint endpoints served.ticket.value.produced.actor.other)
      emission.asInput upper recovery reaction) :
    Nonempty (GapDelivered report complete endpoints index served emission emitted upper recovery reaction) := by
  let actor := served.ticket.value.produced.actor.other
  let state := endpoint endpoints actor
  let after := Endpoint.gapAfter state emission.asInput upper recovery reaction
  let filled := Endpoint.receive_gap_enabled conditions
  let result : Endpoint.Result :=
    ⟨after, .accepted (.receive 0 emission.asInput.packet.segment.payload.length), none, [],
      some (ReceiveReassembly.request after.core (Endpoint.offeredWindow after) .data)⟩
  have evaluated : ApplicationTrace.evaluate state (.receive emission.asInput) = result := filled.receive
  have earlier : ∀ old ∈ applicationSteps endpoints actor, old.stamp < report.final.time := by
    have chronology := CampusTCPChronology.Report.application_before report complete endpoints connection
    cases actor
    · exact chronology.1
    · exact chronology.2
  obtain ⟨applicationEffect, applied, supported, noOutput, read, recorded⟩ :=
    application_quiet report.final complete endpoints connection actor (.receive emission.asInput) earlier result
      (.receive 0 emission.asInput.packet.segment.payload.length) evaluated rfl rfl
  obtain ⟨actual, receipt, beforeEq, event, actualSupported, passed, quiet, applicationAt,
      receiptAt, receiptService, receiptPacket, receiptApplication, connectionEq, readEq⟩ :=
    finish_application_delivery report.final index served found emission emitted application pending
      (CampusTCPCustodyFacts.Report.history report) (CampusTCPCustodyFacts.Report.sources report)
      applicationEffect applied supported noOutput
  let localStep := ApplicationTrace.Step.make state (endpoint_valid endpoints actor) (.receive emission.asInput) report.final.time
  have localResult : localStep.result = result := evaluated
  have recordedAt : actual.result.application = some (actor, localStep) := applicationAt.trans recorded
  obtain ⟨updated, updatedConnection, selected, peer, selectedSteps, peerSteps, localBefore, localEvent, stamp⟩ :=
    application_frame report.final complete endpoints connection actor (.receive emission.asInput)
      applicationEffect localStep applied recorded
  have resultState : localStep.result.state = after := congrArg Endpoint.Result.state localResult
  obtain ⟨_, _, _, noService, receiptsHistory⟩ :=
    CampusTCPRoundDelivery.Step.delivery_application_frame actual complete endpoints (beforeEq.symm ▸ connection)
      index served (beforeEq.symm ▸ found) emission emitted application event localStep recordedAt receipt receiptAt
  have residents (gateway) : actual.result.state.resident gateway = report.final.resident gateway := by
    simpa only [beforeEq] using CampusTCPRoundEnvironment.Step.resident_nonservice actual (by rw [event]; trivial) gateway
  have environment := CampusTCPRoundEnvironment.Step.environment actual (by rw [event]; trivial)
  have outputs : actual.result.state.outputs = report.final.outputs := by
    rw [CampusTCPOrigins.output_history actual, quiet, beforeEq]
    simp only [Option.toList_none, List.append_nil]
  have services : actual.result.state.services = report.final.services := by
    rw [CampusTCPOrigins.service_history actual, noService, beforeEq]
    simp only [Option.toList_none, List.append_nil]
  let delivery : CampusTCPRoundDelivery.Delivery report complete endpoints index served emission emitted := {
    step := actual, receipt, localStep, after, updated, beforeEq, event, supported := actualSupported, passed,
    noOutput := quiet, noService, recorded := recordedAt, receiptAt, receiptService, receiptPacket,
    receiptStep := by rw [receiptApplication, recorded]; rfl,
    localBefore, localEvent, stamp, resultState, connection := connectionEq.trans updatedConnection,
    selected := selected.trans resultState, peer, selectedSteps, peerSteps,
    valid := filled.valid, prepared := filled.prepared, recoveryCoherent := filled.coherent, storageCoherent := filled.storage,
    residents, environment := by simpa only [beforeEq] using environment, outputs, services,
    receiptsHistory := by simpa only [beforeEq] using receiptsHistory,
    consumed := delivery_consumed report actual beforeEq index served found emission emitted event }
  refine ⟨{
    toDelivery := delivery, conditions, filled, afterEq := rfl, read := readEq.trans read,
    available := filled.response, localReleased := ?_ }⟩
  change localStep.releasedPayload = _
  simp only [ApplicationTrace.Step.releasedPayload, ApplicationTrace.releasedPayload, localEvent, localBefore, resultState]
  rw [Endpoint.gapAfter_core]
  exact List.drop_left

variable {report : Report input events} {complete : H.Completed input.active input.passive}
  {endpoints : Applications complete} {index : Nat} {served : Served input}
  {emission : WireForwarding.Emission served.ticket.value.source.packet} {emitted : served.evidence.output = some emission}
  {upper : ReceiveReassembly.Run} {recovery : Recovery.State} {reaction : AckReaction.State}

theorem GapDelivered.runs (delivery : GapDelivered report complete endpoints index served emission emitted upper recovery reaction) :
    Endpoint.receiveRuns (endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput =
      [Endpoint.gapLower (endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput, upper] := delivery.filled.runs

theorem GapDelivered.bytes (delivery : GapDelivered report complete endpoints index served emission emitted upper recovery reaction) :
    Endpoint.receivedBytes (endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput =
      emission.asInput.packet.segment.payload ++ upper.bytes := delivery.filled.bytes

theorem GapDelivered.header_receipts (delivery : GapDelivered report complete endpoints index served emission emitted upper recovery reaction) :
    (Endpoint.receiveEffect delivery.localStep.before emission.asInput).headers.map (fun header =>
      (header.run.receipt, header.run.metadata.receivedAt, header.acknowledged)) =
      [((endpoint endpoints served.ticket.value.produced.actor.other).receiveStore.nextID,
        (endpoint endpoints served.ticket.value.produced.actor.other).now, 0),
        (upper.receipt, upper.metadata.receivedAt, 0)] := by
  rw [delivery.localBefore]
  exact delivery.filled.header_receipts

theorem GapDelivered.received (delivery : GapDelivered report complete endpoints index served emission emitted upper recovery reaction) :
    delivery.after.core.received = (endpoint endpoints served.ticket.value.produced.actor.other).core.received ++
      (emission.asInput.packet.segment.payload ++ upper.bytes) := by
  rw [delivery.afterEq, Endpoint.gapAfter_core]
  rfl

theorem GapDelivered.cursor (delivery : GapDelivered report complete endpoints index served emission emitted upper recovery reaction) :
    delivery.after.core.receiveNext = (endpoint endpoints served.ticket.value.produced.actor.other).core.receiveNext.add
      (emission.asInput.packet.segment.payload.length + upper.bytes.length) := by
  rw [delivery.afterEq]
  exact Endpoint.gapAfter_cursor _ _ _ _ _

theorem GapDelivered.runtime (delivery : GapDelivered report complete endpoints index served emission emitted upper recovery reaction) :
    delivery.after.recovery = some { recovery with duplicateAcks := 0 } := by
  rw [delivery.afterEq, Endpoint.gapAfter_recovery]

theorem GapDelivered.available_early (delivery : GapDelivered report complete endpoints index served emission emitted upper recovery reaction) :
    Endpoint.ResponseAvailable delivery.after false := by
  rw [delivery.afterEq]
  exact delivery.filled.response_any

def GapDelivered.move {current : Cut input complete}
    (delivery : GapDelivered current.report complete current.endpoints index served emission emitted upper recovery reaction) :
    Move current delivery.step :=
  let next : Cut input complete := ⟨_, delivery.toDelivery.append current.supported current.finished,
    delivery.toDelivery.append_supported _ _, rfl, delivery.updated, delivery.connection⟩
  ⟨next, delivery.beforeEq, delivery.supported, delivery.passed, rfl, rfl⟩

theorem Step.deliver_gap (actual : Step input) (current : Cut input complete)
    (before : actual.before = current.report.final) (event : actual.event = .deliver index emission.bytes true)
    (found : current.report.final.services[index]? = some served) (application : D.ApplicationSource served.ticket.value.produced)
    (pending : D.LinkPending current.report.final index)
    (conditions : Endpoint.GapReceiveConditions (endpoint current.endpoints served.ticket.value.produced.actor.other)
      emission.asInput upper recovery reaction) :
    ∃ delivery : GapDelivered current.report complete current.endpoints index served emission emitted upper recovery reaction,
      delivery.step = actual := by
  obtain ⟨delivery⟩ := Report.deliver_gap current.report complete current.endpoints current.connection index served found emission emitted
    application pending upper recovery reaction conditions
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event delivery.step actual
    (delivery.beforeEq.trans before.symm) (delivery.event.trans event.symm)
  exact ⟨delivery, same⟩

private def ackMove (current : Cut input complete) (actual : Step input) (actor : Actor)
    (facts : CampusTCPRoundAck.AckFacts current.report.final complete current.endpoints actor actual) : Move current actual :=
  let report := CampusTCPSchedule.Report.appendStep current.report current.supported current.finished
    actual facts.beforeEq facts.supported
  let next : Cut input complete := ⟨_, report, CampusTCPSchedule.Report.appendStep_supported _ _ _ _ _ _,
    rfl, facts.after, facts.connection⟩
  ⟨next, facts.beforeEq, facts.supported, facts.passed, rfl, rfl⟩

structure GapAck {prior : Cut input complete}
    (delivery : GapDelivered prior.report complete prior.endpoints index served emission emitted upper recovery reaction)
    (current : Cut input complete) where
  actual : Step input
  facts : CampusTCPRoundAck.AckFacts current.report.final complete current.endpoints
    served.ticket.value.produced.actor.other actual
  move : Move current actual
  covering : facts.packet.packet.segment.acknowledgment =
    (endpoint prior.endpoints served.ticket.value.produced.actor.other).core.receiveNext.add
      (emission.asInput.packet.segment.payload.length + upper.bytes.length)
  sequence : facts.packet.packet.segment.sequence =
    (endpoint prior.endpoints served.ticket.value.produced.actor.other).core.sendNext
  header : facts.packet.packet.header = Output.reverse
    (endpoint prior.endpoints served.ticket.value.produced.actor.other).core.inbound
  localReleased : facts.localStep.releasedPayload = []

theorem GapDelivered.emit_ack_at {prior current : Cut input complete}
    (delivery : GapDelivered prior.report complete prior.endpoints index served emission emitted upper recovery reaction)
    (placement : CampusTCPRecoveryRoundPhaseBase.At delivery.move.after current)
    (timely : Endpoint.AckTimeReady delivery.after (endpoint current.endpoints served.ticket.value.produced.actor.other).now) :
    Nonempty (GapAck delivery current) := by
  let actor := served.ticket.value.produced.actor.other
  have frame : Endpoint.ClockFrame delivery.after (endpoint current.endpoints actor) := by
    have clock := placement.frame.endpointFrame actor
    change Endpoint.ClockFrame (endpoint delivery.updated actor) (endpoint current.endpoints actor) at clock
    rw [delivery.selected] at clock
    exact clock
  have prepared := frame.ack_prepared delivery.prepared timely
  have available : Endpoint.ResponseAvailable (endpoint current.endpoints actor) false := by
    simpa only [Endpoint.ResponseAvailable, frame.ackReaction, Bool.false_eq_true, false_implies, and_true] using
      delivery.available_early
  obtain ⟨actual, ⟨facts⟩⟩ := CampusTCPRoundAck.Report.emitAck_enabled current.report complete current.endpoints current.connection
    actor prepared available
  let move := ackMove current actual actor facts
  refine ⟨⟨actual, facts, move, ?_, ?_, ?_, ?_⟩⟩
  · exact facts.acknowledgment.trans ((congrArg EstablishedReceive.State.receiveNext frame.core).trans delivery.cursor)
  · have sendNext : delivery.after.core.sendNext = (endpoint prior.endpoints actor).core.sendNext := by
      rw [delivery.afterEq, Endpoint.gapAfter_core]
      rfl
    exact facts.sequence.trans ((congrArg EstablishedReceive.State.sendNext frame.core).trans sendNext)
  · have inbound : delivery.after.core.inbound = (endpoint prior.endpoints actor).core.inbound := by
      rw [delivery.afterEq, Endpoint.gapAfter_core]
      rfl
    exact facts.header.trans (congrArg Output.reverse ((congrArg EstablishedReceive.State.inbound frame.core).trans inbound))
  · simp only [ApplicationTrace.Step.releasedPayload, ApplicationTrace.releasedPayload, facts.localEvent]

theorem GapDelivered.emit_ack {prior : Cut input complete}
    (delivery : GapDelivered prior.report complete prior.endpoints index served emission emitted upper recovery reaction) :
    Nonempty (GapAck delivery delivery.move.after) := by
  apply delivery.emit_ack_at (CampusTCPRecoveryRoundPhaseBase.At.refl _)
  have selected : endpoint delivery.move.after.endpoints served.ticket.value.produced.actor.other = delivery.after :=
    delivery.selected
  rw [selected]
  intro value runtime
  have work := delivery.prepared.2
  rw [runtime] at work
  exact work.1

end Netlib.Check.CampusTCPGapDelivery
