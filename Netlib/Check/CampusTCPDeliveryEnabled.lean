import Netlib.Check.CampusTCPEnabled
import Netlib.Check.CampusTCPChronology
import Netlib.Protocol.TCP.EndpointAckReceiveEnabled

/-!
# Delivery from pending link packets

The receiver uses the exact stored gateway emission.
Old endpoint and custody conditions derive the actual receive operation.
-/

namespace Netlib.Protocol.TCP.EstablishedReceive

theorem input_roundtrip (value : Input) : input value.bytes = .ok value := by
  cases value with
  | mk bytes packet checked =>
    unfold input
    split
    · rename_i reason failed
      rw [checked] at failed
      cases failed
    · rename_i actual found
      have same : actual = packet := Except.ok.inj (found.symm.trans checked)
      subst actual
      rfl

end Netlib.Protocol.TCP.EstablishedReceive

namespace Netlib.Check.CampusTCPDeliveryEnabled

open CampusTCPModel
namespace C
export Netlib.Theory.PacketCustody (History State Item resolve)
end C
namespace F
export CampusTCPCustodyFacts (Sources)
end F
namespace E
export Protocol.TCP.Endpoint (State AckPrepared RecoveryCoherent StorageCoherent)
end E

variable {input : Input}

def ApplicationSource : Produced input.active input.passive → Prop
  | .startup .. => False
  | .application .. => True

def LinkPending (before : State input) (index : Nat) : Prop :=
  ∃ item ∈ before.custody.pending, Transit.linkAt index item.value.payload = true

instance (produced : Produced input.active input.passive) : Decidable (ApplicationSource produced) := by
  cases produced <;> dsimp only [ApplicationSource] <;> infer_instance

instance (before : State input) (index : Nat) : Decidable (LinkPending before index) :=
  decidable_of_iff ((before.custody.pendingID (Transit.linkAt index)).isSome = true) (by
    constructor
    · intro present
      obtain ⟨id, selected⟩ := Option.isSome_iff_exists.mp present
      obtain ⟨packet, member, _, linked⟩ := before.custody.pendingID_source (Transit.linkAt index) id selected
      exact ⟨packet, member, linked⟩
    · intro pending
      obtain ⟨id, selected⟩ := before.custody.pendingID_exists (Transit.linkAt index) pending
      exact Option.isSome_of_eq_some selected)

theorem prepare_deliver_exists (before : State input) (index : Nat) (served : Served input)
    (found : before.services[index]? = some served)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (pending : LinkPending before index) (history : C.History before.custody) (sources : F.Sources before) :
    ∃ custody, prepareCustody before (.deliver index emission.bytes true) = .ok custody := by
  obtain ⟨id, selected⟩ := before.custody.pendingID_exists (Transit.linkAt index) pending
  obtain ⟨packet, member, packetID, linked⟩ := before.custody.pendingID_source (Transit.linkAt index) id selected
  obtain ⟨actual, actualEmission, actualEmitted, payload⟩ := CampusTCPCustodyFacts.link_stage _ _ linked
  have source := sources packet (List.mem_append_right _ member)
  rw [payload] at source
  have sameService : actual = served := Option.some.inj (source.symm.trans found)
  subst actual
  have sameEmission : actualEmission = emission := Option.some.inj (actualEmitted.symm.trans emitted)
  subst actualEmission
  have selectedPacket : before.custody.pendingID (Transit.linkAt index) = some packet.id := by
    rw [packetID]
    exact selected
  obtain ⟨resolved, computed⟩ := Theory.PacketCustody.resolve_completes before.custody packet member .delivered
  have chosen : resolved.item = packet := resolved.item_eq history.valid packet member rfl
  have bytes : resolved.item.value.payload.bytes = emission.bytes := by rw [chosen, payload]; rfl
  exact ⟨resolved.state, by simp only [prepareCustody, selectedPacket, computed, Except.mapError,
    bind, Except.bind, bytes, ite_true, pure, Except.pure]⟩

private theorem deliver_core_of_application (before : State input) (index : Nat) (served : Served input)
    (found : before.services[index]? = some served)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (application : ApplicationSource served.ticket.value.produced)
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
      simp only [ApplicationSource, produced] at application
    · rename_i actor source sourceOutput origin produced
      simp only [applied]
      exact ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

namespace A
export CampusTCPEnabled (endpoint applicationSteps endpoint_valid application_quiet application_frame)
end A

structure InOrderReady (state : Protocol.TCP.Endpoint.State) (packet : Protocol.TCP.EstablishedReceive.Input)
    (recovery : Protocol.TCP.Recovery.State) (reaction : Protocol.TCP.AckReaction.State) : Prop where
  recoveryCoherent : Protocol.TCP.Endpoint.RecoveryCoherent state
  ackPrepared : Protocol.TCP.Endpoint.AckPrepared state
  storageCoherent : Protocol.TCP.Endpoint.StorageCoherent state
  runtime : state.recovery = some recovery
  ackRuntime : state.ackReaction = some reaction
  sent : recovery.SentBy recovery.now
  empty : state.receiveStore.held = []
  tuple : packet.packet.header = state.core.inbound
  controls : Protocol.TCP.EstablishedReceive.control packet.packet.segment = none
  acknowledgment : Protocol.TCP.Flags.ack packet.packet.segment.flags = true
  sequence : packet.packet.segment.sequence = state.core.receiveNext
  nonempty : packet.packet.segment.payload ≠ []
  fits : packet.packet.segment.payload.length ≤ Protocol.TCP.Endpoint.offeredWindow state
  bounded : Protocol.TCP.Endpoint.inOrderCount state packet ≤ state.core.sent.length

instance (state : Protocol.TCP.Endpoint.State) (packet : Protocol.TCP.EstablishedReceive.Input)
    (recovery : Protocol.TCP.Recovery.State) (reaction : Protocol.TCP.AckReaction.State) :
    Decidable (InOrderReady state packet recovery reaction) :=
  decidable_of_iff (Protocol.TCP.Endpoint.RecoveryCoherent state ∧ Protocol.TCP.Endpoint.AckPrepared state ∧
    Protocol.TCP.Endpoint.StorageCoherent state ∧ state.recovery = some recovery ∧ state.ackReaction = some reaction ∧
    recovery.SentBy recovery.now ∧ state.receiveStore.held = [] ∧ packet.packet.header = state.core.inbound ∧
    Protocol.TCP.EstablishedReceive.control packet.packet.segment = none ∧
    Protocol.TCP.Flags.ack packet.packet.segment.flags = true ∧ packet.packet.segment.sequence = state.core.receiveNext ∧
    packet.packet.segment.payload ≠ [] ∧ packet.packet.segment.payload.length ≤ Protocol.TCP.Endpoint.offeredWindow state ∧
    Protocol.TCP.Endpoint.inOrderCount state packet ≤ state.core.sent.length) (by
      constructor
      · rintro ⟨coherent, prepared, storage, runtime, ackRuntime, sent, empty, tuple, controls, ack, sequence, nonempty, fits, bounded⟩
        exact ⟨coherent, prepared, storage, runtime, ackRuntime, sent, empty, tuple, controls, ack, sequence, nonempty, fits, bounded⟩
      · intro ready
        exact ⟨ready.recoveryCoherent, ready.ackPrepared, ready.storageCoherent, ready.runtime, ready.ackRuntime,
          ready.sent, ready.empty, ready.tuple, ready.controls, ready.acknowledgment, ready.sequence, ready.nonempty, ready.fits, ready.bounded⟩)

structure FullAckReady (state : Protocol.TCP.Endpoint.State) (packet : Protocol.TCP.EstablishedReceive.Input)
    (recovery : Protocol.TCP.Recovery.State) (reaction : Protocol.TCP.AckReaction.State) : Prop where
  recoveryCoherent : Protocol.TCP.Endpoint.RecoveryCoherent state
  ackPrepared : Protocol.TCP.Endpoint.AckPrepared state
  storageCoherent : Protocol.TCP.Endpoint.StorageCoherent state
  runtime : state.recovery = some recovery
  ackRuntime : state.ackReaction = some reaction
  positive : recovery.Positive
  flight : 0 < state.core.sent.length
  emptyHeld : state.receiveStore.held = []
  tuple : packet.packet.header = state.core.inbound
  controls : Protocol.TCP.EstablishedReceive.control packet.packet.segment = none
  acknowledgment : Protocol.TCP.Flags.ack packet.packet.segment.flags = true
  sequence : packet.packet.segment.sequence = state.core.receiveNext
  empty : packet.packet.segment.payload = []
  covers : Protocol.TCP.Endpoint.inOrderCount state packet = state.core.sent.length

instance (state : Protocol.TCP.Endpoint.State) (packet : Protocol.TCP.EstablishedReceive.Input)
    (recovery : Protocol.TCP.Recovery.State) (reaction : Protocol.TCP.AckReaction.State) :
    Decidable (FullAckReady state packet recovery reaction) :=
  decidable_of_iff (Protocol.TCP.Endpoint.RecoveryCoherent state ∧ Protocol.TCP.Endpoint.AckPrepared state ∧
    Protocol.TCP.Endpoint.StorageCoherent state ∧ state.recovery = some recovery ∧ state.ackReaction = some reaction ∧
    recovery.Positive ∧ 0 < state.core.sent.length ∧ state.receiveStore.held = [] ∧ packet.packet.header = state.core.inbound ∧
    Protocol.TCP.EstablishedReceive.control packet.packet.segment = none ∧
    Protocol.TCP.Flags.ack packet.packet.segment.flags = true ∧ packet.packet.segment.sequence = state.core.receiveNext ∧
    packet.packet.segment.payload = [] ∧ Protocol.TCP.Endpoint.inOrderCount state packet = state.core.sent.length) (by
      constructor
      · rintro ⟨coherent, prepared, storage, runtime, ackRuntime, positive, flight, emptyHeld, tuple, controls, ack, sequence, empty, covers⟩
        exact ⟨coherent, prepared, storage, runtime, ackRuntime, positive, flight, emptyHeld, tuple, controls, ack, sequence, empty, covers⟩
      · intro ready
        exact ⟨ready.recoveryCoherent, ready.ackPrepared, ready.storageCoherent, ready.runtime, ready.ackRuntime,
          ready.positive, ready.flight, ready.emptyHeld, ready.tuple, ready.controls, ready.acknowledgment, ready.sequence, ready.empty, ready.covers⟩)

private theorem applyApplication_passed (before : State input) (actor : Actor) (event : T.Event)
    (effect : Effect input) (computed : applyApplication input before actor event = .ok effect) :
    effect.passed = true := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed)
    | (solve | cases computed; rfl)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

private theorem finish_application_delivery (before : State input) (index : Nat) (served : Served input)
    (found : before.services[index]? = some served)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (application : ApplicationSource served.ticket.value.produced)
    (pending : LinkPending before index) (history : C.History before.custody) (sources : F.Sources before)
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
      actual.result.state.connection = applicationEffect.state.connection := by
  have applicationPassed := applyApplication_passed before _ (.receive emission.asInput) applicationEffect applied
  obtain ⟨core, receipt, coreComputed, coreSupport, coreOutput, coreApplication, _, receiptAt, receiptService,
      receiptPacket, receiptApplication, corePassed, coreConnection⟩ :=
    deliver_core_of_application before index served found emission emitted application applicationEffect applied
  obtain ⟨custody, prepared⟩ := prepare_deliver_exists before index served found emission emitted pending history sources
  let effect : Effect input := { core with state := { core.state with
    custody := finishCustody before core custody, time := before.time + 1 } }
  have computed : step input before (.deliver index emission.bytes true) = .ok effect := by
    simp only [step, process, coreComputed, prepared, bind, Except.bind, pure, Except.pure]
    rfl
  let actual : Step input := ⟨before, .deliver index emission.bytes true, effect, computed⟩
  exact ⟨actual, receipt, rfl, rfl, coreSupport.trans supported, corePassed.trans applicationPassed,
    coreOutput.trans noOutput, coreApplication, receiptAt, receiptService, receiptPacket, receiptApplication, coreConnection⟩

theorem deliver_inOrder_enabled (before : State input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : before.connection = .application complete endpoints)
    (index : Nat) (served : Served input) (found : before.services[index]? = some served)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (application : ApplicationSource served.ticket.value.produced)
    (pending : LinkPending before index) (history : C.History before.custody) (sources : F.Sources before)
    (earlier : ∀ old ∈ A.applicationSteps endpoints served.ticket.value.produced.actor.other, old.stamp < before.time)
    (recovery : Protocol.TCP.Recovery.State) (reaction : Protocol.TCP.AckReaction.State)
    (ready : InOrderReady (A.endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput recovery reaction) :
    ∃ actual : Step input, actual.before = before ∧ actual.event = .deliver index emission.bytes true ∧
      actual.result.supported = true ∧ actual.result.passed = true ∧ actual.result.output = none ∧
      ∃ receipt, actual.result.receipt = some receipt ∧ receipt.served = served ∧ receipt.received = emission.asInput ∧
      ∃ endpointStep after, ∃ updated : Applications complete,
        actual.result.application = some (served.ticket.value.produced.actor.other, endpointStep) ∧
        receipt.application = some endpointStep ∧ endpointStep.result.state = after ∧
        actual.result.state.connection = .application complete updated ∧
        A.endpoint updated served.ticket.value.produced.actor.other = after ∧
        A.endpoint updated served.ticket.value.produced.actor.other.other =
          A.endpoint endpoints served.ticket.value.produced.actor.other.other ∧
        A.applicationSteps updated served.ticket.value.produced.actor.other =
          A.applicationSteps endpoints served.ticket.value.produced.actor.other ++ [endpointStep] ∧
        A.applicationSteps updated served.ticket.value.produced.actor.other.other =
          A.applicationSteps endpoints served.ticket.value.produced.actor.other.other ∧
        endpointStep.stamp = before.time ∧
        Protocol.TCP.Endpoint.receivedBytes endpointStep.before emission.asInput = emission.asInput.packet.segment.payload ∧
        after.core.received = endpointStep.before.core.received ++ emission.asInput.packet.segment.payload ∧
        after.core.receiveNext = endpointStep.before.core.receiveNext.add emission.asInput.packet.segment.payload.length ∧
        after.Valid ∧ Protocol.TCP.Endpoint.AckPrepared after ∧ Protocol.TCP.Endpoint.ResponseAvailable after false ∧
        Protocol.TCP.Endpoint.RecoveryCoherent after ∧ Protocol.TCP.Endpoint.StorageCoherent after := by
  let actor := served.ticket.value.produced.actor.other
  let state := A.endpoint endpoints actor
  obtain ⟨acknowledged, after, _, afterEq, received, _, released, afterValid, afterRecovery, afterPrepared, afterStorage⟩ :=
    Protocol.TCP.Endpoint.receive_inOrder_prepared state emission.asInput recovery reaction (A.endpoint_valid endpoints actor)
      ready.recoveryCoherent ready.ackPrepared ready.storageCoherent ready.runtime ready.ackRuntime ready.sent
      ready.empty ready.tuple ready.controls ready.acknowledgment ready.sequence ready.nonempty ready.fits ready.bounded
  let result : Protocol.TCP.Endpoint.Result :=
    ⟨after, .accepted (.receive (Protocol.TCP.Endpoint.inOrderCount state emission.asInput) emission.asInput.packet.segment.payload.length),
      none, [], some (Protocol.TCP.ReceiveReassembly.request after.core (Protocol.TCP.Endpoint.offeredWindow after) .data)⟩
  have evaluated : Protocol.TCP.ApplicationTrace.evaluate state (.receive emission.asInput) = result := received
  have receiveFacts := Protocol.TCP.Endpoint.receive_effects state emission.asInput
  rw [received, released] at receiveFacts
  have available : Protocol.TCP.Endpoint.ResponseAvailable after false := by
    rw [afterEq]
    exact Protocol.TCP.Endpoint.inOrderAfterWith_response state emission.asInput acknowledged reaction
  obtain ⟨applicationEffect, applied, supported, noOutput, _, recorded⟩ :=
    A.application_quiet before complete endpoints connection actor (.receive emission.asInput) earlier result
      (.receive (Protocol.TCP.Endpoint.inOrderCount state emission.asInput) emission.asInput.packet.segment.payload.length)
      evaluated rfl rfl
  obtain ⟨actual, receipt, beforeEq, eventEq, actualSupport, actualPassed, actualQuiet, actualApplication,
      receiptAt, receiptService, receiptPacket, receiptApplication, connectionEq⟩ :=
    finish_application_delivery before index served found emission emitted application pending history sources
      applicationEffect applied supported noOutput
  let endpointStep := Protocol.TCP.ApplicationTrace.Step.make state (A.endpoint_valid endpoints actor)
    (.receive emission.asInput) before.time
  have appAt : actual.result.application = some (actor, endpointStep) := actualApplication.trans recorded
  have stateAt : endpointStep.result.state = after := by
    change (Protocol.TCP.ApplicationTrace.evaluate state (.receive emission.asInput)).state = after
    rw [evaluated]
  obtain ⟨updated, updatedConnection, selectedState, peerState, selectedSteps, peerSteps, _, _, stamp⟩ :=
    A.application_frame before complete endpoints connection actor (.receive emission.asInput)
      applicationEffect endpointStep applied recorded
  refine ⟨actual, beforeEq, eventEq, actualSupport, actualPassed, actualQuiet,
    receipt, receiptAt, receiptService, receiptPacket, endpointStep, after, updated, appAt, ?_, stateAt,
    connectionEq.trans updatedConnection, selectedState.trans stateAt, peerState, selectedSteps, peerSteps, stamp, released,
    receiveFacts.2.2.1, receiveFacts.2.2.2.2.1, afterValid, afterPrepared, available, afterRecovery, afterStorage⟩
  rw [receiptApplication, recorded]
  rfl

theorem deliver_fullAck_enabled (before : State input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : before.connection = .application complete endpoints)
    (index : Nat) (served : Served input) (found : before.services[index]? = some served)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (application : ApplicationSource served.ticket.value.produced)
    (pending : LinkPending before index) (history : C.History before.custody) (sources : F.Sources before)
    (earlier : ∀ old ∈ A.applicationSteps endpoints served.ticket.value.produced.actor.other, old.stamp < before.time)
    (recovery : Protocol.TCP.Recovery.State) (reaction : Protocol.TCP.AckReaction.State)
    (ready : FullAckReady (A.endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput recovery reaction) :
    ∃ actual : Step input, actual.before = before ∧ actual.event = .deliver index emission.bytes true ∧
      actual.result.supported = true ∧ actual.result.passed = true ∧ actual.result.output = none ∧
      ∃ receipt, actual.result.receipt = some receipt ∧ receipt.served = served ∧ receipt.received = emission.asInput ∧
      ∃ endpointStep after, ∃ updated : Applications complete,
        actual.result.application = some (served.ticket.value.produced.actor.other, endpointStep) ∧
        receipt.application = some endpointStep ∧ endpointStep.result.state = after ∧
        actual.result.state.connection = .application complete updated ∧
        A.endpoint updated served.ticket.value.produced.actor.other = after ∧
        A.endpoint updated served.ticket.value.produced.actor.other.other =
          A.endpoint endpoints served.ticket.value.produced.actor.other.other ∧
        A.applicationSteps updated served.ticket.value.produced.actor.other =
          A.applicationSteps endpoints served.ticket.value.produced.actor.other ++ [endpointStep] ∧
        A.applicationSteps updated served.ticket.value.produced.actor.other.other =
          A.applicationSteps endpoints served.ticket.value.produced.actor.other.other ∧
        endpointStep.stamp = before.time ∧
        Protocol.TCP.Endpoint.receivedBytes endpointStep.before emission.asInput = [] ∧
        after.core.sent = [] ∧ after.core.sendUna = endpointStep.before.core.sendNext ∧
        after.Valid ∧ Protocol.TCP.Endpoint.AckPrepared after ∧
        Protocol.TCP.Endpoint.RecoveryCoherent after ∧ Protocol.TCP.Endpoint.StorageCoherent after ∧
        ∃ nextRecovery, after.recovery = some nextRecovery ∧ nextRecovery.outstanding = [] ∧
          nextRecovery.deadline = none ∧ nextRecovery.timeoutCount = 0 := by
  let actor := served.ticket.value.produced.actor.other
  let state := A.endpoint endpoints actor
  obtain ⟨acknowledged, after, _, afterEq, received, _, released, retired, una, afterValid, afterPrepared, afterRecovery, afterStorage,
      cleared, deadline, attempts⟩ :=
    Protocol.TCP.Endpoint.receive_empty_full_ack_coherent state emission.asInput recovery reaction (A.endpoint_valid endpoints actor)
      ready.recoveryCoherent ready.ackPrepared ready.storageCoherent ready.runtime ready.ackRuntime ready.positive
      ready.flight ready.emptyHeld ready.tuple ready.controls ready.acknowledgment ready.sequence ready.empty ready.covers
  let result : Protocol.TCP.Endpoint.Result :=
    ⟨after, .accepted (.receive state.core.sent.length 0), none, [], none⟩
  have evaluated : Protocol.TCP.ApplicationTrace.evaluate state (.receive emission.asInput) = result := received
  obtain ⟨applicationEffect, applied, supported, noOutput, _, recorded⟩ :=
    A.application_quiet before complete endpoints connection actor (.receive emission.asInput) earlier result
      (.receive state.core.sent.length 0) evaluated rfl rfl
  obtain ⟨actual, receipt, beforeEq, eventEq, actualSupport, actualPassed, actualQuiet, actualApplication,
      receiptAt, receiptService, receiptPacket, receiptApplication, connectionEq⟩ :=
    finish_application_delivery before index served found emission emitted application pending history sources
      applicationEffect applied supported noOutput
  let endpointStep := Protocol.TCP.ApplicationTrace.Step.make state (A.endpoint_valid endpoints actor)
    (.receive emission.asInput) before.time
  have appAt : actual.result.application = some (actor, endpointStep) := actualApplication.trans recorded
  have stateAt : endpointStep.result.state = after := by
    change (Protocol.TCP.ApplicationTrace.evaluate state (.receive emission.asInput)).state = after
    rw [evaluated]
  obtain ⟨updated, updatedConnection, selectedState, peerState, selectedSteps, peerSteps, _, _, stamp⟩ :=
    A.application_frame before complete endpoints connection actor (.receive emission.asInput)
      applicationEffect endpointStep applied recorded
  have receiptStep : receipt.application = some endpointStep := by
    rw [receiptApplication, recorded]
    rfl
  have afterRuntime : after.recovery = some { acknowledged with duplicateAcks := 0 } := by
    rw [afterEq]
    exact Protocol.TCP.Endpoint.windowState_recovery _ _ _
  exact ⟨actual, beforeEq, eventEq, actualSupport, actualPassed, actualQuiet,
    receipt, receiptAt, receiptService, receiptPacket, endpointStep, after, updated, appAt, receiptStep, stateAt,
    connectionEq.trans updatedConnection, selectedState.trans stateAt, peerState, selectedSteps, peerSteps, stamp,
    released, retired, una, afterValid, afterPrepared, afterRecovery, afterStorage, { acknowledged with duplicateAcks := 0 },
    afterRuntime, cleared, deadline, attempts⟩

theorem Report.deliver_inOrder_enabled (report : Report input events) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : report.final.connection = .application complete endpoints)
    (index : Nat) (served : Served input) (found : report.final.services[index]? = some served)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (application : ApplicationSource served.ticket.value.produced)
    (pending : LinkPending report.final index)
    (recovery : Protocol.TCP.Recovery.State) (reaction : Protocol.TCP.AckReaction.State)
    (ready : InOrderReady (A.endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput recovery reaction) :
    ∃ actual : Step input, actual.before = report.final ∧ actual.event = .deliver index emission.bytes true ∧
      actual.result.supported = true ∧ actual.result.passed = true ∧ actual.result.output = none ∧
      ∃ receipt, actual.result.receipt = some receipt ∧ receipt.served = served ∧ receipt.received = emission.asInput ∧
      ∃ endpointStep after, ∃ updated : Applications complete,
        actual.result.application = some (served.ticket.value.produced.actor.other, endpointStep) ∧
        receipt.application = some endpointStep ∧ endpointStep.result.state = after ∧
        actual.result.state.connection = .application complete updated ∧
        A.endpoint updated served.ticket.value.produced.actor.other = after ∧
        A.endpoint updated served.ticket.value.produced.actor.other.other =
          A.endpoint endpoints served.ticket.value.produced.actor.other.other ∧
        A.applicationSteps updated served.ticket.value.produced.actor.other =
          A.applicationSteps endpoints served.ticket.value.produced.actor.other ++ [endpointStep] ∧
        A.applicationSteps updated served.ticket.value.produced.actor.other.other =
          A.applicationSteps endpoints served.ticket.value.produced.actor.other.other ∧
        endpointStep.stamp = report.final.time ∧
        Protocol.TCP.Endpoint.receivedBytes endpointStep.before emission.asInput = emission.asInput.packet.segment.payload ∧
        after.core.received = endpointStep.before.core.received ++ emission.asInput.packet.segment.payload ∧
        after.core.receiveNext = endpointStep.before.core.receiveNext.add emission.asInput.packet.segment.payload.length ∧
        after.Valid ∧ Protocol.TCP.Endpoint.AckPrepared after ∧ Protocol.TCP.Endpoint.ResponseAvailable after false ∧
        Protocol.TCP.Endpoint.RecoveryCoherent after ∧ Protocol.TCP.Endpoint.StorageCoherent after := by
  have chronology := CampusTCPChronology.Report.application_before report complete endpoints connection
  have earlier (actor : Actor) : ∀ old ∈ A.applicationSteps endpoints actor, old.stamp < report.final.time := by
    cases actor
    · exact chronology.1
    · exact chronology.2
  exact CampusTCPDeliveryEnabled.deliver_inOrder_enabled report.final complete endpoints connection index served found emission emitted
    application pending (CampusTCPCustodyFacts.Report.history report) (CampusTCPCustodyFacts.Report.sources report)
    (earlier served.ticket.value.produced.actor.other) recovery reaction ready

theorem Report.deliver_fullAck_enabled (report : Report input events) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : report.final.connection = .application complete endpoints)
    (index : Nat) (served : Served input) (found : report.final.services[index]? = some served)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (application : ApplicationSource served.ticket.value.produced)
    (pending : LinkPending report.final index)
    (recovery : Protocol.TCP.Recovery.State) (reaction : Protocol.TCP.AckReaction.State)
    (ready : FullAckReady (A.endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput recovery reaction) :
    ∃ actual : Step input, actual.before = report.final ∧ actual.event = .deliver index emission.bytes true ∧
      actual.result.supported = true ∧ actual.result.passed = true ∧ actual.result.output = none ∧
      ∃ receipt, actual.result.receipt = some receipt ∧ receipt.served = served ∧ receipt.received = emission.asInput ∧
      ∃ endpointStep after, ∃ updated : Applications complete,
        actual.result.application = some (served.ticket.value.produced.actor.other, endpointStep) ∧
        receipt.application = some endpointStep ∧ endpointStep.result.state = after ∧
        actual.result.state.connection = .application complete updated ∧
        A.endpoint updated served.ticket.value.produced.actor.other = after ∧
        A.endpoint updated served.ticket.value.produced.actor.other.other =
          A.endpoint endpoints served.ticket.value.produced.actor.other.other ∧
        A.applicationSteps updated served.ticket.value.produced.actor.other =
          A.applicationSteps endpoints served.ticket.value.produced.actor.other ++ [endpointStep] ∧
        A.applicationSteps updated served.ticket.value.produced.actor.other.other =
          A.applicationSteps endpoints served.ticket.value.produced.actor.other.other ∧
        endpointStep.stamp = report.final.time ∧
        Protocol.TCP.Endpoint.receivedBytes endpointStep.before emission.asInput = [] ∧
        after.core.sent = [] ∧ after.core.sendUna = endpointStep.before.core.sendNext ∧
        after.Valid ∧ Protocol.TCP.Endpoint.AckPrepared after ∧
        Protocol.TCP.Endpoint.RecoveryCoherent after ∧ Protocol.TCP.Endpoint.StorageCoherent after ∧
        ∃ nextRecovery, after.recovery = some nextRecovery ∧ nextRecovery.outstanding = [] ∧
          nextRecovery.deadline = none ∧ nextRecovery.timeoutCount = 0 := by
  have chronology := CampusTCPChronology.Report.application_before report complete endpoints connection
  have earlier (actor : Actor) : ∀ old ∈ A.applicationSteps endpoints actor, old.stamp < report.final.time := by
    cases actor
    · exact chronology.1
    · exact chronology.2
  exact CampusTCPDeliveryEnabled.deliver_fullAck_enabled report.final complete endpoints connection index served found emission emitted
    application pending (CampusTCPCustodyFacts.Report.history report) (CampusTCPCustodyFacts.Report.sources report)
    (earlier served.ticket.value.produced.actor.other) recovery reaction ready

end Netlib.Check.CampusTCPDeliveryEnabled
