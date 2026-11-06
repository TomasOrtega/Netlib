import Netlib.Protocol.TCP.EndpointPartialAckEnabled
import Netlib.Check.CampusTCPTimedOldData
import Netlib.Check.CampusTCPTimedTimeout
import Netlib.Check.CampusTCPRoundPhaseBase

namespace Netlib.Check.CampusTCPPartialAck

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTimedOldData (finish_application_delivery delivery_consumed)

namespace D
export CampusTCPDeliveryEnabled (ApplicationSource LinkPending)
end D

variable {input : CampusTCPModel.Input} {events : List CampusTCPModel.Event}
variable {report : Report input events} {complete : H.Completed input.active input.passive}
  {endpoints : Applications complete} {index : Nat} {served : Served input}
  {emission : WireForwarding.Emission served.ticket.value.source.packet} {emitted : served.evidence.output = some emission}

private theorem startup_work (before : State input) (event : Check.TCPHandshake.Event) (effect : Effect input)
    (computed : startup input before event = .ok effect) : effect.state.work = before.work := by
  unfold startup at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem delivery_work (delivery : CampusTCPRoundDelivery.Delivery report complete endpoints index served emission emitted) :
    delivery.step.result.state.work = report.final.work := by
  obtain ⟨effect, custody, computed, final⟩ := delivery.step.processed
  rw [delivery.event] at computed
  simp only [processCore] at computed
  have result : effect.state.work = delivery.step.before.work := by
    repeat' first
      | (solve | cases computed; dsimp only; exact (CampusTCPTimedTimeout.application_frames _ _ _ _ (by assumption)).1)
      | (solve | cases computed; dsimp only; exact startup_work _ _ _ (by assumption))
      | (cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)
  simpa only [final, delivery.beforeEq] using result

private theorem delivery_custody (delivery : CampusTCPRoundDelivery.Delivery report complete endpoints index served emission emitted) :
    ∃ id, ∃ resolved : Theory.PacketCustody.Resolved delivery.step.before.custody id .delivered,
      delivery.step.before.custody.pendingID (Transit.linkAt index) = some id ∧
      Theory.PacketCustody.resolve delivery.step.before.custody id .delivered = .ok resolved ∧
      resolved.item.value.payload = .link index served emission emitted ∧
      delivery.step.result.state.custody = resolved.state ∧
      ∀ item ∈ delivery.step.result.state.custody.pending, item.id ≠ id := by
  obtain ⟨id, resolved, selected, resolution, payload, absent⟩ := delivery.consumed
  obtain ⟨effect, custody, _, prepared, final⟩ := delivery.step.transaction
  have output : effect.output = none := by simpa only [final] using delivery.noOutput
  have service : effect.service = none := by simpa only [final] using delivery.noService
  have custodyEq : custody = resolved.state := by
    simp only [prepareCustody, delivery.event, selected, resolution, Except.mapError, bind, Except.bind,
      payload, Transit.bytes, ite_true, pure, Except.pure, Except.ok.injEq] at prepared
    exact prepared.symm
  exact ⟨id, resolved, selected, resolution, payload, by
    simp only [final, finishCustody, output, service, custodyEq], absent⟩

structure PartialAckDelivered (report : Report input events) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (index : Nat) (served : Served input)
    (emission : WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission) (recovery : Recovery.State) (reaction : AckReaction.State)
    extends CampusTCPRoundDelivery.Delivery report complete endpoints index served emission emitted where
  conditions : Endpoint.AdvancingAckConditions (endpoint endpoints served.ticket.value.produced.actor.other)
    emission.asInput recovery reaction
  protocol : Endpoint.AdvancingAck (endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput recovery after
  accepted : localStep.result.decision = .accepted
    (.receive (Endpoint.inOrderCount (endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput) 0)
  localReleased : localStep.releasedPayload = []
  localRead : localStep.readBytes = []
  read : step.result.read = []
  work : step.result.state.work = report.final.work
  custody : ∃ id, ∃ resolved : Theory.PacketCustody.Resolved step.before.custody id .delivered,
    step.before.custody.pendingID (Transit.linkAt index) = some id ∧
    Theory.PacketCustody.resolve step.before.custody id .delivered = .ok resolved ∧
    resolved.item.value.payload = .link index served emission emitted ∧ step.result.state.custody = resolved.state ∧
    ∀ item ∈ step.result.state.custody.pending, item.id ≠ id

theorem Report.deliver_partial_ack (report : Report input events) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : report.final.connection = .application complete endpoints)
    (index : Nat) (served : Served input) (found : report.final.services[index]? = some served)
    (emission : WireForwarding.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (application : D.ApplicationSource served.ticket.value.produced) (pending : D.LinkPending report.final index)
    (recovery : Recovery.State) (reaction : AckReaction.State)
    (conditions : Endpoint.AdvancingAckConditions (endpoint endpoints served.ticket.value.produced.actor.other)
      emission.asInput recovery reaction) :
    Nonempty (PartialAckDelivered report complete endpoints index served emission emitted recovery reaction) := by
  let actor := served.ticket.value.produced.actor.other
  let state := endpoint endpoints actor
  let count := Endpoint.inOrderCount state emission.asInput
  obtain ⟨after, protocol⟩ := Endpoint.receive_advancing_ack_enabled conditions
  let result : Endpoint.Result := ⟨after, .accepted (.receive count 0), none, [], none⟩
  have evaluated : ApplicationTrace.evaluate state (.receive emission.asInput) = result := protocol.receive
  have earlier : ∀ old ∈ applicationSteps endpoints actor, old.stamp < report.final.time := by
    have chronology := CampusTCPChronology.Report.application_before report complete endpoints connection
    cases actor
    · exact chronology.1
    · exact chronology.2
  obtain ⟨applicationEffect, applied, supported, noOutput, read, recorded⟩ :=
    application_quiet report.final complete endpoints connection actor (.receive emission.asInput) earlier result
      (.receive count 0) evaluated rfl rfl
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
    step := actual, receipt, localStep, after, updated, beforeEq, event, supported := actualSupported, passed
    noOutput := quiet, noService, recorded := recordedAt, receiptAt, receiptService, receiptPacket
    receiptStep := by rw [receiptApplication, recorded]; rfl
    localBefore, localEvent, stamp, resultState, connection := connectionEq.trans updatedConnection
    selected := selected.trans resultState, peer, selectedSteps, peerSteps
    valid := protocol.valid, prepared := protocol.prepared, recoveryCoherent := protocol.coherent, storageCoherent := protocol.storage
    residents, environment := by simpa only [beforeEq] using environment, outputs, services
    receiptsHistory := by simpa only [beforeEq] using receiptsHistory
    consumed := delivery_consumed report actual beforeEq index served found emission emitted event }
  refine ⟨{
    toDelivery := delivery, conditions, protocol, accepted := congrArg Endpoint.Result.decision localResult
    localReleased := ?_, localRead := ?_, read := readEq.trans read
    work := delivery_work delivery, custody := delivery_custody delivery }⟩
  · change localStep.releasedPayload = []
    simp only [ApplicationTrace.Step.releasedPayload, ApplicationTrace.releasedPayload, localEvent, localBefore, resultState]
    rw [protocol.core]
    simp only [EstablishedReceive.commit, List.append_nil]
    change state.core.received.drop state.core.received.length = []
    exact List.drop_length
  · change localStep.result.read = []
    rw [localResult]

variable {recovery : Recovery.State} {reaction : AckReaction.State}

def PartialAckDelivered.move {current : Cut input complete}
    (delivery : PartialAckDelivered current.report complete current.endpoints index served emission emitted recovery reaction) :
    Move current delivery.step :=
  let next : Cut input complete := ⟨_, delivery.toDelivery.append current.supported current.finished,
    delivery.toDelivery.append_supported _ _, rfl, delivery.updated, delivery.connection⟩
  ⟨next, delivery.beforeEq, delivery.supported, delivery.passed, rfl, rfl⟩

theorem PartialAckDelivered.gateway
    (delivery : PartialAckDelivered report complete endpoints index served emission emitted recovery reaction) (gateway : Gateway) :
    beforeService input delivery.step.result.state gateway = beforeService input report.final gateway := by
  rw [CampusTCPRoundLocal.step_service_nonservice delivery.step (by rw [delivery.event]; trivial), delivery.beforeEq]

theorem Step.deliver_partial_ack (actual : Step input) (current : Cut input complete)
    (before : actual.before = current.report.final) (event : actual.event = .deliver index emission.bytes true)
    (found : current.report.final.services[index]? = some served) (application : D.ApplicationSource served.ticket.value.produced)
    (pending : D.LinkPending current.report.final index)
    (conditions : Endpoint.AdvancingAckConditions (endpoint current.endpoints served.ticket.value.produced.actor.other)
      emission.asInput recovery reaction) :
    ∃ delivery : PartialAckDelivered current.report complete current.endpoints index served emission emitted recovery reaction,
      delivery.step = actual := by
  obtain ⟨delivery⟩ := Report.deliver_partial_ack current.report complete current.endpoints current.connection index served found
    emission emitted application pending recovery reaction conditions
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event delivery.step actual
    (delivery.beforeEq.trans before.symm) (delivery.event.trans event.symm)
  exact ⟨delivery, same⟩

end Netlib.Check.CampusTCPPartialAck
