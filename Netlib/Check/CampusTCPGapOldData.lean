import Netlib.Protocol.TCP.EndpointOldSpanEnabled
import Netlib.Check.CampusTCPTimedOldData

/-!
# Actual receipts for old data behind a closed gap

The selected span can end before the current receive cursor.
Its real receipt consumes the link and creates immediate sequence ACK work.
-/

namespace Netlib.Check.CampusTCPGapOldData

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPTimedOldData (OldDataDelivered application_sequence finish_application_delivery delivery_consumed)

namespace D
export CampusTCPDeliveryEnabled (ApplicationSource LinkPending)
end D

variable {input : CampusTCPModel.Input} {events : List CampusTCPModel.Event}

structure OldSpanReady (state : Endpoint.State) (packet : EstablishedReceive.Input)
    (reaction : AckReaction.State) (consumed : Nat) : Prop where
  recoveryCoherent : Endpoint.RecoveryCoherent state
  ackPrepared : Endpoint.AckPrepared state
  storageCoherent : Endpoint.StorageCoherent state
  ackRuntime : state.ackReaction = some reaction
  tuple : packet.packet.header = state.core.inbound
  controls : EstablishedReceive.control packet.packet.segment = none
  nonempty : packet.packet.segment.payload ≠ []
  inside : packet.packet.segment.payload.length ≤ consumed
  cursor : packet.packet.segment.sequence.add consumed = state.core.receiveNext
  epoch : consumed + Endpoint.offeredWindow state ≤ Seq.modulus

theorem Report.deliver_old_span (report : Report input events) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : report.final.connection = .application complete endpoints)
    (index : Nat) (served : Served input) (found : report.final.services[index]? = some served)
    (emission : WireForwarding.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (application : D.ApplicationSource served.ticket.value.produced) (pending : D.LinkPending report.final index)
    (reaction : AckReaction.State) (consumed : Nat)
    (ready : OldSpanReady (endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput reaction consumed) :
    Nonempty (OldDataDelivered report complete endpoints index served emission emitted reaction) := by
  let actor := served.ticket.value.produced.actor.other
  let state := endpoint endpoints actor
  let after := Endpoint.sequenceAfter state reaction
  have valid := endpoint_valid endpoints actor
  obtain ⟨received, runs, released, prepared, available⟩ :=
    Endpoint.receive_old_span state emission.asInput reaction consumed valid ready.recoveryCoherent ready.ackPrepared
      ready.storageCoherent ready.ackRuntime ready.tuple ready.controls ready.nonempty ready.inside ready.cursor ready.epoch
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

end Netlib.Check.CampusTCPGapOldData
