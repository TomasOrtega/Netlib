import Netlib.Check.CampusTCPDeliveryEnabled
import Netlib.Check.CampusTCPRoundEnvironment
import Netlib.Check.CampusTCPSchedule

/-!
# Actual packet delivery in one TCP round

The received bytes come from the selected stored emission.
The actual local step retains the preceding endpoint and receipt.
-/

namespace Netlib.Check.CampusTCPRoundDelivery

open CampusTCPModel
open Protocol

namespace A
export CampusTCPEnabled (endpoint applicationSteps)
end A
namespace D
export CampusTCPDeliveryEnabled (ApplicationSource LinkPending InOrderReady FullAckReady)
end D
namespace E
export TCP.Endpoint (State AckPrepared ResponseAvailable RecoveryCoherent StorageCoherent)
end E

theorem Step.delivery_application_frame (actual : Step input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : actual.before.connection = .application complete endpoints)
    (index : Nat) (served : Served input) (found : actual.before.services[index]? = some served)
    (emission : TCP.WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission) (application : D.ApplicationSource served.ticket.value.produced)
    (event : actual.event = .deliver index emission.bytes true) (localStep : T.Step)
    (recorded : actual.result.application = some (served.ticket.value.produced.actor.other, localStep))
    (receipt : Receipt input) (receiptAt : actual.result.receipt = some receipt) :
    localStep.before = A.endpoint endpoints served.ticket.value.produced.actor.other ∧
      localStep.event = .receive emission.asInput ∧ localStep.stamp = actual.before.time ∧
      actual.result.service = none ∧ actual.result.state.receipts = actual.before.receipts ++ [receipt] := by
  obtain ⟨effect, custody, computed, final⟩ := actual.processed
  rw [event] at computed
  simp only [processCore, CampusTCPModel.get, found, bind, Except.bind] at computed
  split at computed
  · rename_i missing
    rw [emitted] at missing
    cases missing
  · rename_i actualEmission actualEmitted
    have sameEmission : actualEmission = emission := Option.some.inj (actualEmitted.symm.trans emitted)
    subst actualEmission
    have parsedInput : TCP.EstablishedReceive.input emission.bytes = .ok emission.asInput :=
      TCP.EstablishedReceive.input_roundtrip emission.asInput
    have bytes : emission.asInput.bytes = emission.bytes := rfl
    simp only [pure, Except.pure, parsedInput, parsed, Except.mapError, bytes, dite_true] at computed
    split at computed
    · rename_i source sourceOutput sourcePresent produced
      simp only [D.ApplicationSource, produced] at application
    · rename_i actor source sourceOutput origin produced
      cases applied : applyApplication input actual.before served.ticket.value.produced.actor.other
          (.receive emission.asInput) with
      | error reason => simp [applied] at computed
      | ok applicationEffect =>
        simp only [applied, Except.ok.injEq] at computed
        subst effect
        have localRecorded : applicationEffect.application = some (served.ticket.value.produced.actor.other, localStep) := by
          simpa only [final] using recorded
        obtain ⟨updated, _, _, _, _, _, localBefore, localEvent, stamp⟩ :=
          CampusTCPEnabled.application_frame actual.before complete endpoints connection
            served.ticket.value.produced.actor.other (.receive emission.asInput) applicationEffect localStep applied localRecorded
        have sameReceipt : receipt = (⟨actual.before.time, index, served, emission, emitted,
            emission.asInput, rfl, served.ticket.value.produced.actor.other, rfl,
            applicationEffect.application.map (·.2), none⟩ : Receipt input) := by
          simpa only [final, Option.some.injEq] using receiptAt.symm
        refine ⟨localBefore, localEvent, stamp, ?_, ?_⟩
        · rw [final]
          have noService : applicationEffect.service = none := by
            unfold applyApplication at applied
            repeat' first
              | (solve | cases applied; rfl)
              | (cases applied)
              | (split at applied)
              | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at applied)
          exact noService
        · rw [final, sameReceipt]
    · rename_i source occurrence present produced
      simp only [D.ApplicationSource, produced] at application

variable {input : Input} {events : List CampusTCPModel.Event}

structure Delivery (report : Report input events) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (index : Nat) (served : Served input)
    (emission : TCP.WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission) where
  step : Step input
  receipt : Receipt input
  localStep : T.Step
  after : E.State
  updated : Applications complete
  beforeEq : step.before = report.final
  event : step.event = .deliver index emission.bytes true
  supported : step.result.supported = true
  passed : step.result.passed = true
  noOutput : step.result.output = none
  noService : step.result.service = none
  recorded : step.result.application = some (served.ticket.value.produced.actor.other, localStep)
  receiptAt : step.result.receipt = some receipt
  receiptService : receipt.served = served
  receiptPacket : receipt.received = emission.asInput
  receiptStep : receipt.application = some localStep
  localBefore : localStep.before = A.endpoint endpoints served.ticket.value.produced.actor.other
  localEvent : localStep.event = .receive emission.asInput
  stamp : localStep.stamp = report.final.time
  resultState : localStep.result.state = after
  connection : step.result.state.connection = .application complete updated
  selected : A.endpoint updated served.ticket.value.produced.actor.other = after
  peer : A.endpoint updated served.ticket.value.produced.actor.other.other =
    A.endpoint endpoints served.ticket.value.produced.actor.other.other
  selectedSteps : A.applicationSteps updated served.ticket.value.produced.actor.other =
    A.applicationSteps endpoints served.ticket.value.produced.actor.other ++ [localStep]
  peerSteps : A.applicationSteps updated served.ticket.value.produced.actor.other.other =
    A.applicationSteps endpoints served.ticket.value.produced.actor.other.other
  valid : after.Valid
  prepared : E.AckPrepared after
  recoveryCoherent : E.RecoveryCoherent after
  storageCoherent : E.StorageCoherent after
  residents : ∀ gateway, step.result.state.resident gateway = report.final.resident gateway
  environment : CampusTCPRoundEnvironment.environment report.final = CampusTCPRoundEnvironment.environment step.result.state
  outputs : step.result.state.outputs = report.final.outputs
  services : step.result.state.services = report.final.services
  receiptsHistory : step.result.state.receipts = report.final.receipts ++ [receipt]
  consumed : ∃ id, ∃ resolved : Theory.PacketCustody.Resolved step.before.custody id .delivered,
    step.before.custody.pendingID (Transit.linkAt index) = some id ∧
    Theory.PacketCustody.resolve step.before.custody id .delivered = .ok resolved ∧
    resolved.item.value.payload = .link index served emission emitted ∧
    ∀ item ∈ step.result.state.custody.pending, item.id ≠ id

structure DataDelivered (report : Report input events) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (index : Nat) (served : Served input)
    (emission : TCP.WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission) extends Delivery report complete endpoints index served emission emitted where
  released : TCP.Endpoint.receivedBytes (A.endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput =
    emission.asInput.packet.segment.payload
  received : after.core.received = (A.endpoint endpoints served.ticket.value.produced.actor.other).core.received ++
    emission.asInput.packet.segment.payload
  receiveNext : after.core.receiveNext =
    (A.endpoint endpoints served.ticket.value.produced.actor.other).core.receiveNext.add emission.asInput.packet.segment.payload.length
  available : E.ResponseAvailable after false
  core : after.core = TCP.Endpoint.inOrderCore (A.endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput
  inbound : after.core.inbound = (A.endpoint endpoints served.ticket.value.produced.actor.other).core.inbound
  sendNext : after.core.sendNext = (A.endpoint endpoints served.ticket.value.produced.actor.other).core.sendNext
  capacity : after.core.capacity = (A.endpoint endpoints served.ticket.value.produced.actor.other).core.capacity

structure AckDelivered (report : Report input events) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (index : Nat) (served : Served input)
    (emission : TCP.WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission) extends Delivery report complete endpoints index served emission emitted where
  released : TCP.Endpoint.receivedBytes (A.endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput = []
  sentEmpty : after.core.sent = []
  sendUna : after.core.sendUna = (A.endpoint endpoints served.ticket.value.produced.actor.other).core.sendNext
  nextRecovery : TCP.Recovery.State
  runtime : after.recovery = some nextRecovery
  outstanding : nextRecovery.outstanding = []
  deadline : nextRecovery.deadline = none
  timeoutCount : nextRecovery.timeoutCount = 0

private theorem delivery_consumed (report : Report input events) (actual : Step input) (beforeEq : actual.before = report.final)
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

theorem Report.deliver_data (report : Report input events) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : report.final.connection = .application complete endpoints)
    (index : Nat) (served : Served input) (found : report.final.services[index]? = some served)
    (emission : TCP.WireForwarding.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (application : D.ApplicationSource served.ticket.value.produced) (pending : D.LinkPending report.final index)
    (recovery : TCP.Recovery.State) (reaction : TCP.AckReaction.State)
    (ready : D.InOrderReady (A.endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput recovery reaction) :
    Nonempty (DataDelivered report complete endpoints index served emission emitted) := by
  obtain ⟨actual, beforeEq, event, supported, passed, noOutput, receipt, receiptAt, receiptService, receiptPacket,
    localStep, after, updated, recorded, receiptStep, resultState, connectionAfter, selected, peer, selectedSteps,
    peerSteps, stamp, released, received, receiveNext, valid, prepared, available, recoveryCoherent, storageCoherent⟩ :=
    CampusTCPDeliveryEnabled.Report.deliver_inOrder_enabled report complete endpoints connection index served found emission emitted
      application pending recovery reaction ready
  have connectionBefore : actual.before.connection = .application complete endpoints := beforeEq ▸ connection
  have foundBefore : actual.before.services[index]? = some served := beforeEq ▸ found
  obtain ⟨localBefore, localEvent, _, noService, receiptsHistory⟩ :=
    Step.delivery_application_frame actual complete endpoints connectionBefore index served foundBefore emission emitted
      application event localStep recorded receipt receiptAt
  have residents (gateway) : actual.result.state.resident gateway = report.final.resident gateway := by
    simpa only [beforeEq] using CampusTCPRoundEnvironment.Step.resident_nonservice actual (by rw [event]; trivial) gateway
  have environment := CampusTCPRoundEnvironment.Step.environment actual (by rw [event]; trivial)
  have outputs : actual.result.state.outputs = report.final.outputs := by
    rw [CampusTCPOrigins.output_history actual, noOutput, beforeEq]
    simp only [Option.toList_none, List.append_nil]
  have services : actual.result.state.services = report.final.services := by
    rw [CampusTCPOrigins.service_history actual, noService, beforeEq]
    simp only [Option.toList_none, List.append_nil]
  have oldValid := CampusTCPEnabled.endpoint_valid endpoints served.ticket.value.produced.actor.other
  obtain ⟨acknowledged, witnessed, _, witnessedEq, accepted, _, _, _, _, _, _⟩ :=
    TCP.Endpoint.receive_inOrder_prepared (A.endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput
      recovery reaction oldValid ready.recoveryCoherent ready.ackPrepared ready.storageCoherent ready.runtime ready.ackRuntime ready.sent
      ready.empty ready.tuple ready.controls ready.acknowledgment ready.sequence ready.nonempty ready.fits ready.bounded
  have afterEq : after = witnessed := by
    have computed := congrArg TCP.Endpoint.Result.state localStep.computed
    rw [localBefore, localEvent] at computed
    simp only [TCP.ApplicationTrace.evaluate] at computed
    rw [accepted] at computed
    exact resultState.symm.trans computed
  have core : after.core = TCP.Endpoint.inOrderCore (A.endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput := by
    rw [afterEq, witnessedEq]
    exact TCP.Endpoint.windowState_core _ _ _
  let delivery : Delivery report complete endpoints index served emission emitted := {
    step := actual, receipt, localStep, after, updated, beforeEq, event, supported, passed, noOutput, noService,
    recorded, receiptAt, receiptService, receiptPacket, receiptStep, localBefore, localEvent, stamp, resultState,
    connection := connectionAfter, selected, peer, selectedSteps, peerSteps, valid, prepared, recoveryCoherent, storageCoherent,
    residents, environment := by simpa only [beforeEq] using environment, outputs, services,
    receiptsHistory := by simpa only [beforeEq] using receiptsHistory,
    consumed := delivery_consumed report actual beforeEq index served found emission emitted event }
  refine ⟨{
    toDelivery := delivery, released := ?_, received := ?_, receiveNext := ?_, available, core,
    inbound := ?_, sendNext := ?_, capacity := ?_ }⟩
  · simpa only [localBefore] using released
  · simpa only [localBefore] using received
  · simpa only [localBefore] using receiveNext
  · exact (congrArg TCP.EstablishedReceive.State.inbound core).trans rfl
  · exact (congrArg TCP.EstablishedReceive.State.sendNext core).trans rfl
  · exact (congrArg TCP.EstablishedReceive.State.capacity core).trans rfl

theorem Report.deliver_full_ack (report : Report input events) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : report.final.connection = .application complete endpoints)
    (index : Nat) (served : Served input) (found : report.final.services[index]? = some served)
    (emission : TCP.WireForwarding.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (application : D.ApplicationSource served.ticket.value.produced) (pending : D.LinkPending report.final index)
    (recovery : TCP.Recovery.State) (reaction : TCP.AckReaction.State)
    (ready : D.FullAckReady (A.endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput recovery reaction) :
    Nonempty (AckDelivered report complete endpoints index served emission emitted) := by
  obtain ⟨actual, beforeEq, event, supported, passed, noOutput, receipt, receiptAt, receiptService, receiptPacket,
    localStep, after, updated, recorded, receiptStep, resultState, connectionAfter, selected, peer, selectedSteps,
    peerSteps, stamp, released, sentEmpty, sendUna, valid, prepared, recoveryCoherent, storageCoherent,
    nextRecovery, runtime, outstanding, deadline, timeoutCount⟩ :=
    CampusTCPDeliveryEnabled.Report.deliver_fullAck_enabled report complete endpoints connection index served found emission emitted
      application pending recovery reaction ready
  have connectionBefore : actual.before.connection = .application complete endpoints := beforeEq ▸ connection
  have foundBefore : actual.before.services[index]? = some served := beforeEq ▸ found
  obtain ⟨localBefore, localEvent, _, noService, receiptsHistory⟩ :=
    Step.delivery_application_frame actual complete endpoints connectionBefore index served foundBefore emission emitted
      application event localStep recorded receipt receiptAt
  have residents (gateway) : actual.result.state.resident gateway = report.final.resident gateway := by
    simpa only [beforeEq] using CampusTCPRoundEnvironment.Step.resident_nonservice actual (by rw [event]; trivial) gateway
  have environment := CampusTCPRoundEnvironment.Step.environment actual (by rw [event]; trivial)
  have outputs : actual.result.state.outputs = report.final.outputs := by
    rw [CampusTCPOrigins.output_history actual, noOutput, beforeEq]
    simp only [Option.toList_none, List.append_nil]
  have services : actual.result.state.services = report.final.services := by
    rw [CampusTCPOrigins.service_history actual, noService, beforeEq]
    simp only [Option.toList_none, List.append_nil]
  let delivery : Delivery report complete endpoints index served emission emitted := {
    step := actual, receipt, localStep, after, updated, beforeEq, event, supported, passed, noOutput, noService,
    recorded, receiptAt, receiptService, receiptPacket, receiptStep, localBefore, localEvent, stamp, resultState,
    connection := connectionAfter, selected, peer, selectedSteps, peerSteps, valid, prepared, recoveryCoherent, storageCoherent,
    residents, environment := by simpa only [beforeEq] using environment, outputs, services,
    receiptsHistory := by simpa only [beforeEq] using receiptsHistory,
    consumed := delivery_consumed report actual beforeEq index served found emission emitted event }
  refine ⟨{
    toDelivery := delivery, released := ?_, sentEmpty, sendUna := ?_, nextRecovery, runtime, outstanding, deadline, timeoutCount }⟩
  · simpa only [localBefore] using released
  · simpa only [localBefore] using sendUna

section

variable {report : Report input events} {complete : H.Completed input.active input.passive} {endpoints : Applications complete}
  {index : Nat} {served : Served input} {emission : TCP.WireForwarding.Emission served.ticket.value.source.packet}
  {emitted : served.evidence.output = some emission}

def Delivery.append (delivery : Delivery report complete endpoints index served emission emitted)
    (supported : report.supported = true) (finished : report.remaining = []) :
    Report input (events ++ [delivery.step.event]) :=
  CampusTCPSchedule.Report.appendStep report supported finished delivery.step delivery.beforeEq delivery.supported

theorem Delivery.append_supported (delivery : Delivery report complete endpoints index served emission emitted)
    (supported : report.supported = true) (finished : report.remaining = []) :
    (delivery.append supported finished).supported = true :=
  CampusTCPSchedule.Report.appendStep_supported report supported finished delivery.step delivery.beforeEq delivery.supported

end

end Netlib.Check.CampusTCPRoundDelivery
