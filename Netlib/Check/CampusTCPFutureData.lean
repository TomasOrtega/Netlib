import Netlib.Protocol.TCP.EndpointFutureReceiveEnabled
import Netlib.Check.CampusTCPTimedOldData
import Netlib.Check.CampusTCPTimedTimeout
import Netlib.Check.CampusTCPRoundPhaseBase

namespace Netlib.Check.CampusTCPFutureData

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

private theorem recovery_work (before : State input) (event : C.Event) (effect : Effect input)
    (computed : runRecovery input before event = .ok effect) : effect.state.work = before.work := by
  unfold runRecovery at computed
  cases connection : before.connection with
  | startup stage pending | application complete endpoints =>
    simp only [connection] at computed
    cases computed
    rfl
  | recovering current =>
    simp only [connection] at computed
    split at computed
    · cases computed
    · split at computed <;> cases computed <;> rfl

private theorem delivery_work (delivery : CampusTCPRoundDelivery.Delivery report complete endpoints index served emission emitted) :
    delivery.step.result.state.work = report.final.work := by
  obtain ⟨effect, custody, computed, final⟩ := delivery.step.processed
  rw [delivery.event] at computed
  simp only [processCore] at computed
  have result : effect.state.work = delivery.step.before.work := by
    repeat' first
      | (solve | cases computed; dsimp only; exact (CampusTCPTimedTimeout.application_frames _ _ _ _ (by assumption)).1)
      | (solve | cases computed; dsimp only; exact startup_work _ _ _ (by assumption))
      | (solve | cases computed; dsimp only; exact recovery_work _ _ _ (by assumption))
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

structure FutureDelivered (report : Report input events) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (index : Nat) (served : Served input)
    (emission : WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission) (gap : Nat) (recovery : Recovery.State) (reaction : AckReaction.State)
    extends CampusTCPRoundDelivery.Delivery report complete endpoints index served emission emitted where
  conditions : Endpoint.FutureReceiveConditions (endpoint endpoints served.ticket.value.produced.actor.other)
    emission.asInput gap recovery reaction
  protocol : Endpoint.FutureHeld (endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput gap reaction
  afterEq : after = Endpoint.futureAfter (endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput gap reaction
  accepted : localStep.result.decision = .accepted (.receive 0 emission.asInput.packet.segment.payload.length)
  allocation : ApplicationTrace.ActualAllocation localStep
  allocated : localStep.allocation = some allocation
  allocationResult : allocation.store.result = Endpoint.futureStore
    (endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput gap
  heldRun : Endpoint.futureRun (endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput gap = allocation.store.allocated
  localReleased : localStep.releasedPayload = []
  localRead : localStep.readBytes = []
  read : step.result.read = []
  available : Endpoint.ResponseAvailable after true
  pending : (Endpoint.futureReaction (endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput reaction).work.pending ≠ []
  work : step.result.state.work = report.final.work
  custody : ∃ id, ∃ resolved : Theory.PacketCustody.Resolved step.before.custody id .delivered,
    step.before.custody.pendingID (Transit.linkAt index) = some id ∧
    Theory.PacketCustody.resolve step.before.custody id .delivered = .ok resolved ∧
    resolved.item.value.payload = .link index served emission emitted ∧ step.result.state.custody = resolved.state ∧
    ∀ item ∈ step.result.state.custody.pending, item.id ≠ id

theorem Report.deliver_future_data (report : Report input events) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : report.final.connection = .application complete endpoints)
    (index : Nat) (served : Served input) (found : report.final.services[index]? = some served)
    (emission : WireForwarding.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (application : D.ApplicationSource served.ticket.value.produced) (pending : D.LinkPending report.final index)
    (gap : Nat) (recovery : Recovery.State) (reaction : AckReaction.State)
    (conditions : Endpoint.FutureReceiveConditions (endpoint endpoints served.ticket.value.produced.actor.other)
      emission.asInput gap recovery reaction) :
    Nonempty (FutureDelivered report complete endpoints index served emission emitted gap recovery reaction) := by
  let actor := served.ticket.value.produced.actor.other
  let state := endpoint endpoints actor
  let protocol := Endpoint.receive_future_enabled conditions
  let after := Endpoint.futureAfter state emission.asInput gap reaction
  let result : Endpoint.Result :=
    ⟨after, .accepted (.receive 0 emission.asInput.packet.segment.payload.length), none, [],
      some (ReceiveReassembly.request state.core (Endpoint.offeredWindow after) .data)⟩
  have evaluated : ApplicationTrace.evaluate state (.receive emission.asInput) = result := protocol.receive
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
    step := actual, receipt, localStep, after, updated, beforeEq, event, supported := actualSupported, passed
    noOutput := quiet, noService, recorded := recordedAt, receiptAt, receiptService, receiptPacket
    receiptStep := by rw [receiptApplication, recorded]; rfl
    localBefore, localEvent, stamp, resultState, connection := connectionEq.trans updatedConnection
    selected := selected.trans resultState, peer, selectedSteps, peerSteps
    valid := protocol.valid, prepared := protocol.prepared, recoveryCoherent := protocol.coherent, storageCoherent := protocol.storage
    residents, environment := by simpa only [beforeEq] using environment, outputs, services
    receiptsHistory := by simpa only [beforeEq] using receiptsHistory
    consumed := delivery_consumed report actual beforeEq index served found emission emitted event }
  have allocated : ∃ allocation : ApplicationTrace.ActualAllocation localStep, localStep.allocation = some allocation := by
    cases transition : localStep.storeTransition with
    | stutter same empty =>
      have counter := congrArg (fun store : ReceiveReassembly.Store => store.nextID) same
      rw [resultState, localBefore] at counter
      change state.receiveStore.nextID + 1 = state.receiveStore.nextID at counter
      omega
    | accepted allocation => exact ⟨allocation, by simp only [ApplicationTrace.Step.allocation, transition]⟩
  obtain ⟨allocation, allocated⟩ := allocated
  have allocationResult : allocation.store.result = Endpoint.futureStore state emission.asInput gap := by
    have packet := ApplicationTrace.Event.receive.inj (allocation.event.symm.trans localEvent)
    have committed := allocation.committed
    rw [packet, localBefore] at committed
    exact Option.some.inj (committed.symm.trans protocol.allocation.1)
  have heldRun : Endpoint.futureRun state emission.asInput gap = allocation.store.allocated := by
    have member : Endpoint.futureRun state emission.asInput gap ∈ allocation.store.after.held := by
      change _ ∈ allocation.store.result.state.held
      rw [allocationResult]
      exact List.mem_cons_self
    rcases allocation.store.source _ (.inr member) with old | fresh
    · rw [allocation.before, localBefore, conditions.empty] at old
      cases old
    · exact fresh
  refine ⟨{
    toDelivery := delivery, conditions, protocol, afterEq := rfl
    accepted := congrArg Endpoint.Result.decision localResult, allocation, allocated, allocationResult, heldRun
    localReleased := ?_, localRead := ?_, read := readEq.trans read, available := protocol.response, pending := ?_
    work := delivery_work delivery, custody := delivery_custody delivery }⟩
  · change localStep.releasedPayload = []
    simp only [ApplicationTrace.Step.releasedPayload, ApplicationTrace.releasedPayload, localEvent, localBefore, resultState]
    change state.core.received.drop state.core.received.length = []
    exact List.drop_length
  · change localStep.result.read = []
    rw [localResult]
  · exact Endpoint.receiveRelease_pending reaction state.now state.core.receiveNext emission.asInput.packet.segment.payload.length 0 true

variable {gap : Nat} {recovery : Recovery.State} {reaction : AckReaction.State}

def FutureDelivered.move {current : Cut input complete}
    (delivery : FutureDelivered current.report complete current.endpoints index served emission emitted gap recovery reaction) :
    Move current delivery.step :=
  let next : Cut input complete := ⟨_, delivery.toDelivery.append current.supported current.finished,
    delivery.toDelivery.append_supported _ _, rfl, delivery.updated, delivery.connection⟩
  ⟨next, delivery.beforeEq, delivery.supported, delivery.passed, rfl, rfl⟩

theorem FutureDelivered.gateway
    (delivery : FutureDelivered report complete endpoints index served emission emitted gap recovery reaction) (gateway : Gateway) :
    beforeService input delivery.step.result.state gateway = beforeService input report.final gateway := by
  rw [CampusTCPRoundLocal.step_service_nonservice delivery.step (by rw [delivery.event]; trivial), delivery.beforeEq]

theorem FutureDelivered.store
    (delivery : FutureDelivered report complete endpoints index served emission emitted gap recovery reaction) :
    delivery.after.receiveStore =
      ⟨(endpoint endpoints served.ticket.value.produced.actor.other).receiveStore.frontier,
        (endpoint endpoints served.ticket.value.produced.actor.other).receiveStore.nextID + 1,
        [Endpoint.futureRun (endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput gap], true⟩ := by
  rw [delivery.afterEq]
  rfl

theorem FutureDelivered.run_fields
    (delivery : FutureDelivered report complete endpoints index served emission emitted gap recovery reaction) :
    delivery.allocation.store.allocated.position =
        (endpoint endpoints served.ticket.value.produced.actor.other).receiveStore.frontier + gap ∧
      delivery.allocation.store.allocated.bytes = emission.asInput.packet.segment.payload ∧
      delivery.allocation.store.allocated.receipt = (endpoint endpoints served.ticket.value.produced.actor.other).receiveStore.nextID ∧
      delivery.allocation.store.allocated.metadata =
        ⟨emission.asInput.packet.segment, emission.asInput.packet.header,
          (endpoint endpoints served.ticket.value.produced.actor.other).now⟩ := by
  rw [← delivery.heldRun]
  exact Endpoint.futureRun_fields _ _ _

theorem FutureDelivered.core
    (delivery : FutureDelivered report complete endpoints index served emission emitted gap recovery reaction) :
    delivery.after.core = (endpoint endpoints served.ticket.value.produced.actor.other).core := by
  rw [delivery.afterEq]
  rfl

theorem FutureDelivered.runtime
    (delivery : FutureDelivered report complete endpoints index served emission emitted gap recovery reaction) :
    delivery.after.recovery = some recovery := by
  rw [delivery.afterEq]
  exact delivery.conditions.runtime

theorem FutureDelivered.frame
    (delivery : FutureDelivered report complete endpoints index served emission emitted gap recovery reaction) :
    { delivery.after with
      receiveStore := (endpoint endpoints served.ticket.value.produced.actor.other).receiveStore
      ackReaction := (endpoint endpoints served.ticket.value.produced.actor.other).ackReaction } =
      endpoint endpoints served.ticket.value.produced.actor.other := by
  rw [delivery.afterEq]
  rfl

theorem FutureDelivered.available_early
    (delivery : FutureDelivered report complete endpoints index served emission emitted gap recovery reaction) :
    Endpoint.ResponseAvailable delivery.after false := by
  rw [delivery.afterEq]
  change (Endpoint.futureReaction _ _ reaction).work.pending ≠ [] ∧ (false = true → _)
  exact ⟨delivery.pending, by intro impossible; cases impossible⟩

theorem Step.deliver_future_data (actual : Step input) (current : Cut input complete)
    (before : actual.before = current.report.final) (event : actual.event = .deliver index emission.bytes true)
    (found : current.report.final.services[index]? = some served) (application : D.ApplicationSource served.ticket.value.produced)
    (pending : D.LinkPending current.report.final index)
    (conditions : Endpoint.FutureReceiveConditions (endpoint current.endpoints served.ticket.value.produced.actor.other)
      emission.asInput gap recovery reaction) :
    ∃ delivery : FutureDelivered current.report complete current.endpoints index served emission emitted gap recovery reaction,
      delivery.step = actual := by
  obtain ⟨delivery⟩ := Report.deliver_future_data current.report complete current.endpoints current.connection index served found
    emission emitted application pending gap recovery reaction conditions
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event delivery.step actual
    (delivery.beforeEq.trans before.symm) (delivery.event.trans event.symm)
  exact ⟨delivery, same⟩

end Netlib.Check.CampusTCPFutureData
