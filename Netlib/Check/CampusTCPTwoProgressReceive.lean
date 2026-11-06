import Netlib.Check.CampusTCPTwoProgressWire
import Netlib.Check.CampusTCPFutureData
import Netlib.Check.CampusTCPGapDelivery
import Netlib.Check.CampusTCPGapOldData
import Netlib.Check.CampusTCPTimedTimeout

namespace Netlib.Check.CampusTCPTwoProgressReceive

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart (TwoWriteInitial)

namespace R
export CampusTCPTwoProgressReceiver (Facts Stage PacketFields)
end R
namespace D
export CampusTCPRoundDelivery (Delivery DataDelivered)
export CampusTCPDeliveryEnabled (ApplicationSource LinkPending InOrderReady)
end D
namespace W
export CampusTCPTwoProgressWire (DataFields)
end W

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper bytes : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {events : List CampusTCPModel.Event} {report : Report input events} {endpoints : Applications complete}
variable {index : Nat} {served : Served input} {emission : WireForwarding.Emission served.ticket.value.source.packet}
variable {emitted : served.evidence.output = some emission}

structure Link (initial : TwoWriteInitial cut sender gateway lower upper) (current : Cut input complete)
    (offset : Nat) (bytes : List UInt8) (index : Nat) (served : Served input)
    (emission : WireForwarding.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission) where
  found : current.report.final.services[index]? = some served
  application : D.ApplicationSource served.ticket.value.produced
  pending : D.LinkPending current.report.final index
  actor : served.ticket.value.produced.actor = sender
  fields : W.DataFields initial offset bytes served.ticket.value.produced
  target : emission.target = initial.gatewayState.session.entry.flow.output sender.direction

theorem Link.packet_fields (link : Link initial current offset bytes index served emission emitted) :
    R.PacketFields initial offset bytes emission.asInput := link.fields.receiver emission link.target

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

def deliveryMove (current : Cut input complete)
    (delivery : D.Delivery current.report complete current.endpoints index served emission emitted) : Move current delivery.step :=
  let next : Cut input complete := ⟨_, delivery.append current.supported current.finished,
    delivery.append_supported _ _, rfl, delivery.updated, delivery.connection⟩
  ⟨next, delivery.beforeEq, delivery.supported, delivery.passed, rfl, rfl⟩

theorem Delivery.local_result (delivery : D.Delivery report complete endpoints index served emission emitted) :
    delivery.localStep.result = Endpoint.receive (endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput := by
  rw [delivery.localStep.computed, delivery.localEvent, ApplicationTrace.evaluate, delivery.localBefore]

private theorem local_read (delivery : D.Delivery report complete endpoints index served emission emitted) :
    delivery.localStep.readBytes = [] := by
  rw [ApplicationTrace.Step.readBytes, Delivery.local_result delivery]
  exact (Endpoint.receiveEffect_effects _ _).read

private theorem local_release (delivery : D.Delivery report complete endpoints index served emission emitted) :
    delivery.localStep.releasedPayload =
      Endpoint.receivedBytes (endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput := by
  change ApplicationTrace.releasedPayload delivery.localStep.before delivery.localStep.event delivery.localStep.result = _
  rw [delivery.localEvent]
  change delivery.localStep.result.state.core.received.drop delivery.localStep.before.core.received.length = _
  rw [Delivery.local_result delivery, delivery.localBefore, (Endpoint.receive_effects _ _).2.2.1, List.drop_left]

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

private theorem delivery_read (delivery : D.Delivery current.report complete current.endpoints index served emission emitted)
    (found : current.report.final.services[index]? = some served) (application : D.ApplicationSource served.ticket.value.produced) :
    delivery.step.result.read = [] := by
  obtain ⟨effect, custody, computed, final⟩ := delivery.step.processed
  rw [delivery.event] at computed
  have foundBefore : delivery.step.before.services[index]? = some served := delivery.beforeEq ▸ found
  simp only [processCore, CampusTCPModel.get, foundBefore, bind, Except.bind] at computed
  split at computed
  · rename_i missing
    rw [emitted] at missing
    cases missing
  · rename_i selected selectedAt
    have same := Option.some.inj (selectedAt.symm.trans emitted)
    subst selected
    have parsedInput : EstablishedReceive.input emission.bytes = .ok emission.asInput :=
      EstablishedReceive.input_roundtrip emission.asInput
    have bytes : emission.asInput.bytes = emission.bytes := rfl
    simp only [pure, Except.pure, parsedInput, parsed, Except.mapError, bytes, dite_true] at computed
    split at computed
    · rename_i source output present produced
      simp only [D.ApplicationSource, produced] at application
    · rename_i actor source output origin produced
      cases applied : applyApplication input delivery.step.before served.ticket.value.produced.actor.other
          (.receive emission.asInput) with
      | error reason => simp [applied] at computed
      | ok applicationEffect =>
        simp only [applied, Except.ok.injEq] at computed
        subst effect
        have recorded : applicationEffect.application = some (served.ticket.value.produced.actor.other, delivery.localStep) := by
          simpa only [final] using delivery.recorded
        have read := application_read _ _ _ _ _ applied recorded
        have empty : delivery.localStep.result.read = [] := local_read delivery
        simpa only [final] using read.trans empty

structure Received (initial : TwoWriteInitial cut sender gateway lower upper) (current : Cut input complete)
    (beforeStage afterStage : R.Stage) (chunk : List UInt8) (index : Nat) (served : Served input)
    (emission : WireForwarding.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission) where
  beforeFacts : R.Facts initial (endpoint current.endpoints sender.other) beforeStage
  actor : served.ticket.value.produced.actor = sender
  delivery : D.Delivery current.report complete current.endpoints index served emission emitted
  move : Move current delivery.step
  selected : endpoint move.after.endpoints sender.other = delivery.after
  receiver : R.Facts initial (endpoint move.after.endpoints sender.other) afterStage
  peer : endpoint move.after.endpoints sender = endpoint current.endpoints sender
  selectedSteps : applicationSteps move.after.endpoints sender.other = applicationSteps current.endpoints sender.other ++ [delivery.localStep]
  peerSteps : applicationSteps move.after.endpoints sender = applicationSteps current.endpoints sender
  localRelease : delivery.localStep.releasedPayload = chunk
  releasedBytes : Endpoint.receivedBytes (endpoint current.endpoints sender.other) emission.asInput = chunk
  localRead : delivery.localStep.readBytes = []
  read : delivery.step.result.read = []
  available : Endpoint.ResponseAvailable (endpoint move.after.endpoints sender.other) false
  pending : receiver.reaction.work.pending ≠ []
  gateway : ∀ selected, beforeService input move.after.report.final selected = beforeService input current.report.final selected
  environment : CampusTCPRoundEnvironment.environment current.report.final = CampusTCPRoundEnvironment.environment move.after.report.final
  work : delivery.step.result.state.work = current.report.final.work
  custody : ∃ id, ∃ resolved : Theory.PacketCustody.Resolved delivery.step.before.custody id .delivered,
    delivery.step.before.custody.pendingID (Transit.linkAt index) = some id ∧
    Theory.PacketCustody.resolve delivery.step.before.custody id .delivered = .ok resolved ∧
    resolved.item.value.payload = .link index served emission emitted ∧ delivery.step.result.state.custody = resolved.state ∧
    ∀ item ∈ delivery.step.result.state.custody.pending, item.id ≠ id

private def finish (facts : R.Facts initial (endpoint current.endpoints sender.other) beforeStage)
    (actor : served.ticket.value.produced.actor = sender)
    (found : current.report.final.services[index]? = some served) (application : D.ApplicationSource served.ticket.value.produced)
    (delivery : D.Delivery current.report complete current.endpoints index served emission emitted)
    (receiver : R.Facts initial delivery.after afterStage)
    (released : Endpoint.receivedBytes (endpoint current.endpoints sender.other) emission.asInput = chunk)
    (available : Endpoint.ResponseAvailable delivery.after false) :
    Received initial current beforeStage afterStage chunk index served emission emitted := by
  let move := deliveryMove current delivery
  have selected : endpoint move.after.endpoints sender.other = delivery.after := by
    change endpoint delivery.updated sender.other = _
    simpa only [actor] using delivery.selected
  have next : R.Facts initial (endpoint move.after.endpoints sender.other) afterStage := selected.symm ▸ receiver
  have response : Endpoint.ResponseAvailable (endpoint move.after.endpoints sender.other) false := selected.symm ▸ available
  have twice : sender.other.other = sender := by cases sender <;> rfl
  refine {
    beforeFacts := facts, actor, delivery, move, selected, receiver := next
    peer := ?_, selectedSteps := ?_, peerSteps := ?_
    localRelease := ?_, releasedBytes := released, localRead := local_read delivery
    read := delivery_read delivery found application, available := response, pending := ?_
    gateway := ?_, environment := ?_, work := delivery_work delivery, custody := delivery_custody delivery }
  · change endpoint delivery.updated sender = endpoint current.endpoints sender
    simpa only [actor, twice] using delivery.peer
  · change applicationSteps delivery.updated sender.other = _
    simpa only [actor] using delivery.selectedSteps
  · change applicationSteps delivery.updated sender = _
    simpa only [actor, twice] using delivery.peerSteps
  · simpa only [actor] using (local_release delivery).trans (by simpa only [actor] using released)
  · simpa only [Endpoint.ResponseAvailable, next.ackRuntime, Bool.false_eq_true, false_implies, and_true] using response
  · intro selected
    rw [move.final, ← delivery.beforeEq]
    exact CampusTCPRoundLocal.step_service_nonservice delivery.step (by rw [delivery.event]; trivial) selected
  · rw [move.final]
    exact delivery.environment

theorem Received.step_eq (received : Received initial current beforeStage afterStage chunk index served emission emitted)
    (actual : Step input) (before : actual.before = current.report.final)
    (event : actual.event = .deliver index emission.bytes true) : received.delivery.step = actual :=
  CampusTCPRoundPhaseBase.Step.eq_of_before_event received.delivery.step actual
    (received.delivery.beforeEq.trans before.symm) (received.delivery.event.trans event.symm)

theorem Received.fresh_allocation (received : Received initial current beforeStage afterStage chunk index served emission emitted)
    (increment : beforeStage.allocations + 1 = afterStage.allocations) :
    ∃ allocation : ApplicationTrace.ActualAllocation received.delivery.localStep,
      received.delivery.localStep.allocation = some allocation := by
  cases transition : received.delivery.localStep.storeTransition with
  | stutter same empty =>
    have counter := congrArg (fun store : ReceiveReassembly.Store => store.nextID) same
    rw [received.delivery.resultState, received.delivery.localBefore, received.actor] at counter
    have facts : R.Facts initial received.delivery.after afterStage := received.selected ▸ received.receiver
    rw [facts.nextID, received.beforeFacts.nextID, ← increment] at counter
    omega
  | accepted allocation =>
    exact ⟨allocation, by simp only [ApplicationTrace.Step.allocation, transition]⟩

private theorem stage_bound (lower upper : List UInt8) (stage : R.Stage) :
    (stage.bytes lower upper).length ≤ lower.length + upper.length := by
  cases stage <;> simp only [CampusTCPTwoProgressReceiver.Stage.bytes, List.length_nil, List.length_append] <;> omega

private theorem remaining_fits (total prefixSize window size nextSize : Nat)
    (space : total ≤ prefixSize + window) (length : prefixSize + size = nextSize) (bound : nextSize ≤ total) :
    size ≤ window := by omega

theorem in_order_at {beforeStage afterStage : R.Stage}
    (facts : R.Facts initial (endpoint current.endpoints sender.other) beforeStage)
    (link : Link initial current (beforeStage.bytes lower upper).length bytes index served emission emitted)
    (notHeld : beforeStage ≠ .upperHeld) (nextNotHeld : afterStage ≠ .upperHeld) (nonempty : bytes ≠ [])
    (appended : beforeStage.bytes lower upper ++ bytes = afterStage.bytes lower upper)
    (allocations : beforeStage.allocations + 1 = afterStage.allocations) :
    Nonempty (Received initial current beforeStage afterStage bytes index served emission emitted) := by
  have fields := link.packet_fields
  have length := congrArg List.length appended
  simp only [List.length_append] at length
  have fits : bytes.length ≤ Endpoint.offeredWindow (endpoint current.endpoints sender.other) :=
    remaining_fits _ _ _ _ _ facts.space length (stage_bound lower upper afterStage)
  have zero : Endpoint.inOrderCount (endpoint current.endpoints sender.other) emission.asInput = 0 := by
    simp only [Endpoint.inOrderCount, fields.acknowledgment, facts.sendUna, Seq.distance_self]
  have ready : D.InOrderReady (endpoint current.endpoints sender.other) emission.asInput facts.recovery facts.reaction :=
    ⟨facts.coherent, facts.prepared, facts.storage, facts.runtime, facts.ackRuntime, facts.sentBy,
      facts.empty_held notHeld, fields.tuple.trans facts.inbound.symm, fields.controls, fields.ack,
      fields.sequence.trans facts.receiveNext.symm, by rw [fields.payload]; exact nonempty,
      by rw [fields.payload]; exact fits, by rw [zero]; exact Nat.zero_le _⟩
  have currentReady : D.InOrderReady (endpoint current.endpoints served.ticket.value.produced.actor.other)
      emission.asInput facts.recovery facts.reaction := by simpa only [link.actor] using ready
  obtain ⟨delivery⟩ := CampusTCPRoundDelivery.Report.deliver_data current.report complete current.endpoints
    current.connection index served link.found emission emitted link.application link.pending facts.recovery facts.reaction currentReady
  obtain ⟨after, actual, _, released, ⟨receiver⟩, _⟩ :=
    facts.in_order_enabled fields notHeld nextNotHeld nonempty appended allocations
  have computedResult : delivery.localStep.result = Endpoint.receive (endpoint current.endpoints sender.other) emission.asInput := by
    simpa only [link.actor] using Delivery.local_result delivery.toDelivery
  have same : delivery.after = after := delivery.resultState.symm.trans (congrArg Endpoint.Result.state (computedResult.trans actual))
  exact ⟨finish facts link.actor link.found link.application delivery.toDelivery (same.symm ▸ receiver) released delivery.available⟩

theorem lower_at (facts : R.Facts initial (endpoint current.endpoints sender.other) .empty)
    (link : Link initial current 0 lower index served emission emitted) :
    Nonempty (Received initial current .empty .lowerReleased lower index served emission emitted) :=
  in_order_at facts link (by decide) (by decide) initial.lowerNonempty (List.nil_append _) rfl

theorem upper_at (facts : R.Facts initial (endpoint current.endpoints sender.other) .lowerReleased)
    (link : Link initial current lower.length upper index served emission emitted) :
    Nonempty (Received initial current .lowerReleased .allReleased upper index served emission emitted) :=
  in_order_at facts link (by decide) (by decide) initial.upperNonempty rfl rfl

theorem hold_at (facts : R.Facts initial (endpoint current.endpoints sender.other) .empty)
    (link : Link initial current lower.length upper index served emission emitted) :
    Nonempty (Received initial current .empty .upperHeld [] index served emission emitted) := by
  have fields := link.packet_fields
  have conditions : Endpoint.FutureReceiveConditions (endpoint current.endpoints served.ticket.value.produced.actor.other)
      emission.asInput lower.length facts.recovery facts.reaction := by
    simpa only [link.actor] using facts.future_conditions fields
  obtain ⟨delivery⟩ := CampusTCPFutureData.Report.deliver_future_data current.report complete current.endpoints current.connection
    index served link.found emission emitted link.application link.pending lower.length facts.recovery facts.reaction conditions
  have held : Endpoint.FutureHeld (endpoint current.endpoints sender.other) emission.asInput lower.length facts.reaction := by
    simpa only [link.actor] using delivery.protocol
  have receiver : R.Facts initial delivery.after .upperHeld := by
    rw [delivery.afterEq]
    simpa only [link.actor] using facts.future_held fields held
  have released : Endpoint.receivedBytes (endpoint current.endpoints sender.other) emission.asInput = [] := held.no_release.2.1
  exact ⟨finish facts link.actor link.found link.application delivery.toDelivery receiver released delivery.available_early⟩

theorem gap_at (facts : R.Facts initial (endpoint current.endpoints sender.other) .upperHeld)
    (link : Link initial current 0 lower index served emission emitted) :
    Nonempty (Received initial current .upperHeld .allReleased (lower ++ upper) index served emission emitted) := by
  have fields := link.packet_fields
  obtain ⟨receipt, recorded, _⟩ := facts.upper_receipt
  have conditions : Endpoint.GapReceiveConditions (endpoint current.endpoints served.ticket.value.produced.actor.other)
      emission.asInput receipt.run facts.recovery facts.reaction := by
    simpa only [link.actor] using facts.gap_conditions receipt recorded fields
  obtain ⟨delivery⟩ := CampusTCPGapDelivery.Report.deliver_gap current.report complete current.endpoints current.connection
    index served link.found emission emitted link.application link.pending receipt.run facts.recovery facts.reaction conditions
  have filled : Endpoint.GapFilled (endpoint current.endpoints sender.other) emission.asInput receipt.run facts.recovery facts.reaction := by
    simpa only [link.actor] using delivery.filled
  have receiver : R.Facts initial delivery.after .allReleased := by
    rw [delivery.afterEq]
    simpa only [link.actor] using facts.gap_filled receipt recorded fields filled
  have released : Endpoint.receivedBytes (endpoint current.endpoints sender.other) emission.asInput = lower ++ upper := by
    simpa only [fields.payload, receipt.run_fields.2.1] using filled.bytes
  exact ⟨finish facts link.actor link.found link.application delivery.toDelivery receiver released delivery.available_early⟩

theorem old_at (facts : R.Facts initial (endpoint current.endpoints sender.other) stage)
    (link : Link initial current offset bytes index served emission emitted) (nonempty : bytes ≠ [])
    (old : offset + bytes.length ≤ (stage.bytes lower upper).length) :
    Nonempty (Received initial current stage stage [] index served emission emitted) := by
  have fields := link.packet_fields
  obtain ⟨inside, cursor, epoch⟩ := facts.old_span fields nonempty old
  have ready : CampusTCPGapOldData.OldSpanReady (endpoint current.endpoints sender.other) emission.asInput facts.reaction
      ((stage.bytes lower upper).length - offset) :=
    ⟨facts.coherent, facts.prepared, facts.storage, facts.ackRuntime, fields.tuple.trans facts.inbound.symm, fields.controls,
      by rw [fields.payload]; exact nonempty, by rw [fields.payload]; exact inside, cursor, epoch⟩
  have currentReady : CampusTCPGapOldData.OldSpanReady (endpoint current.endpoints served.ticket.value.produced.actor.other)
      emission.asInput facts.reaction ((stage.bytes lower upper).length - offset) := by simpa only [link.actor] using ready
  obtain ⟨delivery⟩ := CampusTCPGapOldData.Report.deliver_old_span current.report complete current.endpoints current.connection
    index served link.found emission emitted link.application link.pending facts.reaction
    ((stage.bytes lower upper).length - offset) currentReady
  obtain ⟨_, _, released, ⟨receiver⟩, _⟩ := facts.old_enabled fields nonempty old
  have next : R.Facts initial delivery.after stage := by
    rw [delivery.afterEq]
    simpa only [link.actor] using receiver
  exact ⟨finish facts link.actor link.found link.application delivery.toDelivery next released delivery.available_early⟩

end Netlib.Check.CampusTCPTwoProgressReceive
