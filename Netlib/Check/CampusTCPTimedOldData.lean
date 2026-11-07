import Netlib.Check.CampusTCPRoundDelivery

/-!
# Actual old-range receipts and renewed ACK work

A whole-old packet consumes its real link without releasing bytes again.
The stored sequence rejection creates a new immediate ACK cause.
-/

namespace Netlib.Check.CampusTCPTimedOldData

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled

namespace D
export CampusTCPDeliveryEnabled (ApplicationSource LinkPending prepare_deliver_exists)
end D

variable {input : CampusTCPModel.Input} {events : List CampusTCPModel.Event}

structure OldDataReady (state : Endpoint.State) (packet : EstablishedReceive.Input)
    (reaction : AckReaction.State) : Prop where
  recoveryCoherent : Endpoint.RecoveryCoherent state
  ackPrepared : Endpoint.AckPrepared state
  storageCoherent : Endpoint.StorageCoherent state
  ackRuntime : state.ackReaction = some reaction
  tuple : packet.packet.header = state.core.inbound
  controls : EstablishedReceive.control packet.packet.segment = none
  nonempty : packet.packet.segment.payload ≠ []
  ends : packet.packet.segment.sequence.add packet.packet.segment.payload.length = state.core.receiveNext
  epoch : packet.packet.segment.payload.length + Endpoint.offeredWindow state ≤ Seq.modulus

theorem application_sequence (before : State input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : before.connection = .application complete endpoints)
    (actor : Actor) (packet : EstablishedReceive.Input)
    (earlier : ∀ old ∈ applicationSteps endpoints actor, old.stamp < before.time)
    (result : Endpoint.Result)
    (evaluated : ApplicationTrace.evaluate (endpoint endpoints actor) (.receive packet) = result)
    (quiet : result.output = none) (decision : result.decision = .reject (.input .sequence)) :
    ∃ effect, applyApplication input before actor (.receive packet) = .ok effect ∧
      effect.supported = true ∧ effect.output = none ∧ effect.read = result.read ∧
      effect.application = some (actor, ApplicationTrace.Step.make (endpoint endpoints actor)
        (endpoint_valid endpoints actor) (.receive packet) before.time) := by
  cases actor
  all_goals
    obtain ⟨applied, computed, same⟩ := cursor_apply_enabled _ (.receive packet) before.time earlier
    have actual : applied.step.result = result := by
      simpa only [same, ApplicationTrace.Step.make, endpoint] using evaluated
    have present : applied.step.result.output = none := actual ▸ quiet
    have supported : applied.step.supported = true := by
      simp only [ApplicationTrace.Step.supported, actual, decision]
    simp only [applyApplication, connection, computed, parsed, Except.mapError, bind, Except.bind,
      pure, Except.pure, present]
    exact ⟨_, rfl, supported, rfl, by rw [actual], by simp only [same, endpoint]⟩

private theorem deliver_core_of_application (before : State input) (index : Nat) (served : Served input)
    (found : before.services[index]? = some served)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (application : D.ApplicationSource served.ticket.value.produced)
    (effect : Effect input)
    (applied : applyApplication input before served.ticket.value.produced.actor.other
      (.receive emission.asInput) = .ok effect) :
    ∃ result receipt, processCore input before (.deliver index emission.bytes true) = .ok result ∧
      result.supported = effect.supported ∧ result.output = effect.output ∧
      result.application = effect.application ∧ result.read = effect.read ∧
      result.receipt = some receipt ∧ receipt.served = served ∧ receipt.received = emission.asInput ∧
      receipt.application = effect.application.map (·.2) ∧
      result.passed = effect.passed ∧ result.state.connection = effect.state.connection := by
  simp only [processCore, CampusTCPModel.get, found, bind, Except.bind]
  split
  · rename_i missing
    rw [emitted] at missing
    cases missing
  · rename_i actual actualEmitted
    have sameEmission : actual = emission := Option.some.inj (actualEmitted.symm.trans emitted)
    subst actual
    have parsedInput : Protocol.TCP.EstablishedReceive.input emission.bytes = .ok emission.asInput :=
      Protocol.TCP.EstablishedReceive.input_roundtrip emission.asInput
    have bytes : emission.asInput.bytes = emission.bytes := rfl
    simp only [pure, Except.pure, parsedInput, parsed, Except.mapError, bytes, dite_true]
    split
    · rename_i source sourceOutput sourcePresent produced
      simp only [D.ApplicationSource, produced] at application
    · rename_i actor source sourceOutput origin produced
      simp only [applied]
      exact ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rename_i source occurrence present produced
      simp only [D.ApplicationSource, produced] at application

private theorem applyApplication_passed (before : State input) (actor : Actor) (event : T.Event)
    (effect : Effect input) (computed : applyApplication input before actor event = .ok effect) :
    effect.passed = true := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed)
    | (solve | cases computed; rfl)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

theorem finish_application_delivery (before : State input) (index : Nat) (served : Served input)
    (found : before.services[index]? = some served)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (application : D.ApplicationSource served.ticket.value.produced)
    (pending : D.LinkPending before index) (history : Theory.PacketCustody.History before.custody) (sources : CampusTCPCustodyFacts.Sources before)
    (applicationEffect : Effect input)
    (applied : applyApplication input before served.ticket.value.produced.actor.other
      (.receive emission.asInput) = .ok applicationEffect)
    (supported : applicationEffect.supported = true) (noOutput : applicationEffect.output = none) :
    ∃ actual : Step input, ∃ receipt,
      actual.before = before ∧ actual.event = .deliver index emission.bytes true ∧
      actual.result.supported = true ∧ actual.result.passed = true ∧ actual.result.output = none ∧
      actual.result.application = applicationEffect.application ∧ actual.result.receipt = some receipt ∧
      receipt.served = served ∧ receipt.received = emission.asInput ∧
      receipt.application = applicationEffect.application.map (·.2) ∧
      actual.result.state.connection = applicationEffect.state.connection ∧ actual.result.read = applicationEffect.read := by
  have applicationPassed := applyApplication_passed before _ (.receive emission.asInput) applicationEffect applied
  obtain ⟨core, receipt, coreComputed, coreSupport, coreOutput, coreApplication, coreRead, receiptAt, receiptService,
      receiptPacket, receiptApplication, corePassed, coreConnection⟩ :=
    deliver_core_of_application before index served found emission emitted application applicationEffect applied
  obtain ⟨custody, prepared⟩ := D.prepare_deliver_exists before index served found emission emitted pending history sources
  let effect : Effect input := { core with state := { core.state with
    custody := finishCustody before core custody, time := before.time + 1 } }
  have computed : step input before (.deliver index emission.bytes true) = .ok effect := by
    simp only [step, process, coreComputed, prepared, bind, Except.bind, pure, Except.pure]
    rfl
  let actual : Step input := ⟨before, .deliver index emission.bytes true, effect, computed⟩
  exact ⟨actual, receipt, rfl, rfl, coreSupport.trans supported, corePassed.trans applicationPassed,
    coreOutput.trans noOutput, coreApplication, receiptAt, receiptService, receiptPacket, receiptApplication, coreConnection, coreRead⟩

theorem delivery_consumed (report : Report input events) (actual : Step input) (beforeEq : actual.before = report.final)
    (index : Nat) (served : Served input) (found : report.final.services[index]? = some served)
    (emission : TCP.WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission) (event : actual.event = .deliver index emission.bytes true) :
    ∃ id, ∃ resolved : Theory.PacketCustody.Resolved actual.before.custody id .delivered,
      actual.before.custody.pendingID (Transit.linkAt index) = some id ∧
      Theory.PacketCustody.resolve actual.before.custody id .delivered = .ok resolved ∧
      resolved.item.value.payload = .link index served emission emitted ∧
      ∀ item ∈ actual.result.state.custody.pending, item.id ≠ id := by
  have history : Theory.PacketCustody.History actual.before.custody := by
    rw [beforeEq]
    exact CampusTCPCustodyFacts.Report.history report
  obtain ⟨id, resolved, selected, resolution, predicate, _, absent⟩ :=
    CampusTCPCustodyFacts.Step.deliver actual index emission.bytes true event history
  obtain ⟨selectedService, selectedEmission, selectedEmitted, payload⟩ := CampusTCPCustodyFacts.link_stage _ _ predicate
  have sources := CampusTCPCustodyFacts.Report.sources report resolved.item (by
    rw [← beforeEq]
    exact List.mem_append_right _ resolved.member)
  rw [payload] at sources
  have serviceEq : selectedService = served := Option.some.inj (sources.symm.trans found)
  subst selectedService
  have emissionEq : selectedEmission = emission := Option.some.inj (selectedEmitted.symm.trans emitted)
  subst selectedEmission
  exact ⟨id, resolved, selected, resolution, payload, absent⟩


structure OldDataDelivered (report : Report input events) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (index : Nat) (served : Served input)
    (emission : WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission) (reaction : AckReaction.State)
    extends CampusTCPRoundDelivery.Delivery report complete endpoints index served emission emitted where
  afterEq : after = Endpoint.sequenceAfter (endpoint endpoints served.ticket.value.produced.actor.other) reaction
  rejected : localStep.result.decision = .reject (.input .sequence)
  runs : Endpoint.receiveRuns (endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput = []
  released : Endpoint.receivedBytes (endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput = []
  localReleased : localStep.releasedPayload = []
  read : step.result.read = []
  available : Endpoint.ResponseAvailable after true

theorem Report.deliver_old_data (report : Report input events) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : report.final.connection = .application complete endpoints)
    (index : Nat) (served : Served input) (found : report.final.services[index]? = some served)
    (emission : WireForwarding.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (application : D.ApplicationSource served.ticket.value.produced) (pending : D.LinkPending report.final index)
    (reaction : AckReaction.State)
    (ready : OldDataReady (endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput reaction) :
    Nonempty (OldDataDelivered report complete endpoints index served emission emitted reaction) := by
  let actor := served.ticket.value.produced.actor.other
  let state := endpoint endpoints actor
  let after := Endpoint.sequenceAfter state reaction
  have valid := endpoint_valid endpoints actor
  obtain ⟨received, runs, released, prepared, available⟩ :=
    Endpoint.receive_old_whole_range state emission.asInput reaction valid ready.recoveryCoherent ready.ackPrepared
      ready.storageCoherent ready.ackRuntime ready.tuple ready.controls ready.nonempty ready.ends ready.epoch
  let result : Endpoint.Result := ⟨after, .reject (.input .sequence), none, [],
    some (ReceiveReassembly.request state.core (Endpoint.offeredWindow state) .sequence)⟩
  have evaluated : ApplicationTrace.evaluate state (.receive emission.asInput) = result := received
  have earlier : ∀ old ∈ applicationSteps endpoints actor, old.stamp < report.final.time := by
    have chronology := CampusTCPChronology.Report.application_before report complete endpoints connection
    cases actor
    · exact chronology.1
    · exact chronology.2
  obtain ⟨applicationEffect, applied, supported, noOutput, read, recorded⟩ :=
    application_sequence report.final complete endpoints connection actor emission.asInput earlier result evaluated rfl rfl
  obtain ⟨actual, receipt, beforeEq, event, actualSupported, passed, quiet, applicationAt,
      receiptAt, receiptService, receiptPacket, receiptApplication, connectionEq, readEq⟩ :=
    finish_application_delivery report.final index served found emission emitted application pending
      (CampusTCPCustodyFacts.Report.history report) (CampusTCPCustodyFacts.Report.sources report)
      applicationEffect applied supported noOutput
  let localStep := ApplicationTrace.Step.make state valid (.receive emission.asInput) report.final.time
  have localResult : localStep.result = result := evaluated
  have recordedAt : actual.result.application = some (actor, localStep) := applicationAt.trans recorded
  obtain ⟨updated, updatedConnection, selected, peer, selectedSteps, peerSteps, localBefore, localEvent, stamp⟩ :=
    application_frame report.final complete endpoints connection actor (.receive emission.asInput)
      applicationEffect localStep applied recorded
  have resultState : localStep.result.state = after := congrArg Endpoint.Result.state localResult
  have connected : actual.result.state.connection = .application complete updated := connectionEq.trans updatedConnection
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
  have readAt : actual.result.read = [] := readEq.trans read
  let delivery : CampusTCPRoundDelivery.Delivery report complete endpoints index served emission emitted := {
    step := actual, receipt, localStep, after, updated, beforeEq, event, supported := actualSupported, passed,
    noOutput := quiet, noService, recorded := recordedAt, receiptAt, receiptService, receiptPacket,
    receiptStep := by rw [receiptApplication, recorded]; rfl,
    localBefore, localEvent, stamp, resultState, connection := connected,
    selected := selected.trans resultState, peer, selectedSteps, peerSteps,
    valid, prepared, recoveryCoherent := ready.recoveryCoherent, storageCoherent := by
      simpa only [after, state, actor, Endpoint.sequenceAfter, Endpoint.StorageCoherent,
        Endpoint.State.StorageValid, ready.ackRuntime, AckReaction.receiveSequence, AckReaction.State.window] using ready.storageCoherent,
    residents, environment := by simpa only [beforeEq] using environment, outputs, services,
    receiptsHistory := by simpa only [beforeEq] using receiptsHistory,
    consumed := delivery_consumed report actual beforeEq index served found emission emitted event }
  refine ⟨{
    toDelivery := delivery
    afterEq := rfl
    rejected := congrArg Endpoint.Result.decision localResult
    runs := runs
    released := released
    localReleased := ?_
    read := readAt
    available := available }⟩
  change localStep.releasedPayload = []
  simp only [ApplicationTrace.Step.releasedPayload, ApplicationTrace.releasedPayload, localEvent, resultState]
  change (Endpoint.sequenceAfter state reaction).core.received.drop state.core.received.length = []
  exact List.drop_length

variable {report : Report input events} {complete : H.Completed input.active input.passive}
  {endpoints : Applications complete} {index : Nat} {served : Served input}
  {emission : WireForwarding.Emission served.ticket.value.source.packet}
  {emitted : served.evidence.output = some emission} {reaction : AckReaction.State}

def sequenceCause (state : Endpoint.State) (reaction : AckReaction.State) :
    Theory.TimedReaction.Cause Unit AckReaction.Demand :=
  Theory.TimedReaction.fresh reaction.work state.now (AckReaction.demand reaction .sequence state.core.receiveNext 0 0) 0

theorem OldDataDelivered.new_sequence_cause
    (delivery : OldDataDelivered report complete endpoints index served emission emitted reaction) :
    ∃ next, delivery.after.ackReaction = some next ∧
      next.work.pending = reaction.work.pending ++
        [sequenceCause (endpoint endpoints served.ticket.value.produced.actor.other) reaction] ∧
      next.work.nextID = reaction.work.nextID + 1 ∧
      (sequenceCause (endpoint endpoints served.ticket.value.produced.actor.other) reaction).demand.kind = .sequence ∧
      (sequenceCause (endpoint endpoints served.ticket.value.produced.actor.other) reaction).issuedAt =
        (endpoint endpoints served.ticket.value.produced.actor.other).now ∧
      (sequenceCause (endpoint endpoints served.ticket.value.produced.actor.other) reaction).due =
        (endpoint endpoints served.ticket.value.produced.actor.other).now := by
  rw [delivery.afterEq]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact Nat.add_zero _

theorem OldDataDelivered.available_early
    (delivery : OldDataDelivered report complete endpoints index served emission emitted reaction) :
    Endpoint.ResponseAvailable delivery.after false := by
  rw [delivery.afterEq]
  exact ⟨Endpoint.receiveSequence_pending _ _ _, by simp⟩

theorem OldDataDelivered.core
    (delivery : OldDataDelivered report complete endpoints index served emission emitted reaction) :
    delivery.after.core = (endpoint endpoints served.ticket.value.produced.actor.other).core := by
  rw [delivery.afterEq]
  rfl

theorem OldDataDelivered.store
    (delivery : OldDataDelivered report complete endpoints index served emission emitted reaction) :
    delivery.after.receiveStore = (endpoint endpoints served.ticket.value.produced.actor.other).receiveStore := by
  rw [delivery.afterEq]
  rfl

end Netlib.Check.CampusTCPTimedOldData
