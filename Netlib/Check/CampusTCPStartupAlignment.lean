import Netlib.Check.CampusTCPFacts
import Netlib.Protocol.TCP.AdmissionMSSFacts
import Netlib.Protocol.TCP.AdmissionExecutionControlFacts
import Netlib.Check.CampusTCPStartupProductionFacts

/-!
# Endpoint and gateway alignment after actual startup

The three received startup packets determine the gateway lanes and NAT tuples.
The proof uses the stored service results.
-/

namespace Netlib.Protocol.TCP.Admission

theorem Result.established_lanes (result : Result before input lifecycle prepared)
    (pending : before.phase = .synAck entry clientISS clientWindow serverISS serverWindow clientMSS serverMSS) :
    ∃ session, result.state.phase = .data session ∧ session.entry = entry ∧
      session.original = Lane.initial (clientISS.add 1) serverWindow serverISS (clientISS.add 1) ∧
      session.reply = Lane.initial (serverISS.add 1) input.packet.segment.window
        input.packet.segment.sequence input.packet.segment.acknowledgment ∧
      session.clientMSS = clientMSS ∧ session.serverMSS = serverMSS := by
  cases before with
  | mk phase observations =>
    change phase = .synAck entry clientISS clientWindow serverISS serverWindow clientMSS serverMSS at pending
    subst phase
    rw [result.phase, nextPhase.eq_3]
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Netlib.Protocol.TCP.Admission

namespace Netlib.Protocol.ConntrackLifecycle

theorem process_fresh_output_records (pipeline : Pipeline) (prepared : Prepared input) (outcome : Outcome)
    (computed : process pipeline prepared = .ok outcome) (fresh : prepared.attachment.fresh = true)
    (output : outcome.output = some packet) :
    outcome.state.records = prepared.state.records ++ [⟨prepared.attachment.entry, false⟩] := by
  simp only [process] at computed
  split at computed
  · cases computed; cases output
  · split at computed
    · cases computed; cases output
    · split at computed
      · cases computed; cases output
      · split at computed
        · cases computed; rfl
        · cases computed

end Netlib.Protocol.ConntrackLifecycle

namespace Netlib.Check.CampusTCPService

open Protocol

theorem Evidence.processing_states (value : Evidence context before source zone ingress mode)
    (processing : Processing context before source zone mode) (selected : value.processing = some processing) :
    value.tracker = processing.outcome.state ∧ value.admission = processing.nextAdmission := by
  cases operation : value.operation with
  | earlyDrop denied => simp only [Evidence.processing, operation] at selected; cases selected
  | processed permitted actual =>
    simp only [Evidence.processing, operation, Option.some.injEq] at selected
    subst actual
    exact ⟨by simp only [Evidence.tracker, operation], by simp only [Evidence.admission, operation]⟩

theorem Processing.output_committed (value : Processing context before source zone mode)
    (emission : W.Emission source.packet) (output : value.outcome.output = some emission) :
    value.nextAdmission = TCP.AdmissionExecution.Result.state value.admitted := by
  rcases TCP.AdmissionExecution.commit_cases (mode := mode) value.admitted value.outcome.state _ value.committed with
    same | ⟨_, fresh, absent⟩
  · exact same.1
  · obtain ⟨model, processed, same, emitted, _⟩ := TCP.WireForwarding.process_output
      _ _ source.valid value.prepared value.outcome value.computed emission output
    have records := ConntrackLifecycle.process_fresh_output_records _ _ model processed fresh emitted
    have confirmed : TCP.Admission.confirmed value.prepared.attachment.entry value.outcome.state = true := by
      apply (TCP.Admission.confirmed_correct _ _).mpr
      refine ⟨⟨value.prepared.attachment.entry, false⟩, ?_, rfl⟩
      rw [same]
      change _ ∈ model.state.records
      rw [records]
      simp
    simp [confirmed] at absent

theorem Processing.fresh_output_records (value : Processing context before source zone mode)
    (emission : W.Emission source.packet) (output : value.outcome.output = some emission)
    (fresh : value.prepared.attachment.fresh = true) :
    value.outcome.state.records = before.tracker.records ++ [⟨value.prepared.attachment.entry, false⟩] := by
  obtain ⟨model, processed, same, emitted, _⟩ := TCP.WireForwarding.process_output
    _ _ source.valid value.prepared value.outcome value.computed emission output
  have records := ConntrackLifecycle.process_fresh_output_records _ _ model processed fresh emitted
  have prior := (ConntrackLifecycle.prepare_fresh _ _ _ value.attached fresh).1
  rw [same]
  change model.state.records = _
  rw [records, prior]

theorem Processing.output_target (value : Processing context before source zone mode)
    (emission : W.Emission source.packet) (output : value.outcome.output = some emission) :
    emission.target = value.prepared.attachment.entry.flow.output value.prepared.attachment.direction := by
  obtain ⟨model, processed, _, emitted, _⟩ := TCP.WireForwarding.process_output
    _ _ source.valid value.prepared value.outcome value.computed emission output
  exact ConntrackLifecycle.process_output _ _ model _ processed emitted

theorem Processing.existing_state (value : Processing context before source zone mode)
    (existing : value.prepared.attachment.fresh = false) : value.outcome.state = value.prepared.state := by
  apply TCP.WireForwarding.process_existing_state _ _ source.valid value.prepared value.outcome value.computed
  rw [TCP.WireForwarding.process_attachment _ _ source.valid value.prepared value.outcome value.computed]
  exact existing

end Netlib.Check.CampusTCPService

namespace Netlib.Check.CampusTCPStartupAlignment

open Packet Protocol

namespace M
export CampusTCPModel (Input State Report Receipt)
end M

structure Slice (history : CampusTCPFacts.StartupHistory (input := input) report complete) : Prop where
  emptyAdmission : history.syn.receive.receipt.served.before.admission.phase = .empty
  emptyTracker : history.syn.receive.receipt.served.before.tracker.records = []
  synAckAdmission : history.synAck.receive.receipt.served.before.admission =
    history.syn.receive.receipt.served.evidence.admission
  ackAdmission : history.ack.receive.receipt.served.before.admission =
    history.synAck.receive.receipt.served.evidence.admission
  synAckTracker : history.synAck.receive.receipt.served.before.tracker =
    history.syn.receive.receipt.served.evidence.tracker
  ackTracker : history.ack.receive.receipt.served.before.tracker =
    history.synAck.receive.receipt.served.evidence.tracker

structure Alignment (input : M.Input) (complete : TCPHandshake.Completed input.active input.passive)
    (entry : NetfilterNAT.Entry) (session : TCP.Admission.Session) : Prop where
  entryEq : session.entry = entry
  originalBase : session.original.base = input.active.iss.add 1
  replyBase : session.reply.base = input.passive.iss.add 1
  originalCoverage : session.original.coverage = TCP.Admission.Coverage.initial
  replyCoverage : session.reply.coverage = TCP.Admission.Coverage.initial
  originalAcknowledged : session.original.acknowledged = 0
  replyAcknowledged : session.reply.acknowledged = 0
  originalWindow : session.original.peerWindow.val = input.passive.capacity
  replyWindow : session.reply.peerWindow.val = input.active.capacity
  originalWindowSequence : session.original.windowSequence = input.passive.iss
  originalWindowAck : session.original.windowAcknowledgment = input.active.iss.add 1
  replyWindowSequence : session.reply.windowSequence = input.active.iss.add 1
  replyWindowAck : session.reply.windowAcknowledgment = input.passive.iss.add 1
  clientMSS : session.clientMSS = TCP.Handshake.receiveOffer input.active
  serverMSS : session.serverMSS = TCP.Handshake.receiveOffer input.passive
  originalZone : entry.flow.originalZone = input.zone
  replyZone : entry.flow.replyZone = input.zone
  clientInput : TCP.Output.reverse complete.certificate.activeSeed.core.inbound = entry.flow.input .original
  serverInput : TCP.Output.reverse complete.certificate.passiveSeed.core.inbound = entry.flow.input .reply
  clientOutput : complete.certificate.activeSeed.core.inbound = entry.flow.output .reply
  serverOutput : complete.certificate.passiveSeed.core.inbound = entry.flow.output .original

theorem receipt_packet (value : M.Receipt input) : value.received.packet = value.emission.decoded := by
  have decoded := value.received.checked
  rw [value.bytes, value.emission.decoded_eq] at decoded
  exact (Except.ok.inj decoded).symm

theorem receipt_header (value : M.Receipt input) : value.received.packet.header = value.emission.target := by
  rw [receipt_packet value, value.emission.header]

theorem receipt_tracker_valid (value : M.Receipt input) : value.served.evidence.tracker.Valid := by
  obtain ⟨processing, selected, _⟩ := value.served.evidence.processed_of_output value.emission value.emitted
  rw [(value.served.evidence.processing_states processing selected).1]
  exact processing.outcome.valid

theorem startup_inbound {input : M.Input} (complete : TCPHandshake.Completed input.active input.passive) :
    complete.certificate.activeSeed.core.inbound = complete.certificate.synAck.input.packet.header ∧
      complete.certificate.passiveSeed.core.inbound = complete.certificate.syn.input.packet.header := by
  constructor
  · simpa only [TCP.HandshakeExchange.Complete.activeSeed, complete.certificate.active.derived,
      TCP.Handshake.activeSeed] using complete.certificate.active.accepted.1.symm
  · simp only [TCP.HandshakeExchange.Complete.passiveSeed, complete.certificate.passive.derived,
      TCP.Handshake.passiveSeed, complete.certificate.pending_fields.2.2.2]

private theorem source_in_service_prefix
    (value : CampusTCPFacts.StartupDelivery (input := input) report time actor packet kind) :
    ∃ prior, CampusTCPModel.Trace input input.initial (prior.map (·.event)) prior value.service.joint.step.before [] ∧
      ∃ producer ∈ prior, producer.result.output = some value.receive.receipt.served.ticket.value.produced := by
  obtain ⟨prior, later, history, preceding, _, _⟩ :=
    CampusTCPFacts.step_origin report value.service.joint.step value.service.joint.member
  have pending : value.receive.receipt.served.ticket ∈ value.service.joint.step.before.work.pending := by
    rw [value.service.ticket]
    exact value.service.completed.member
  rcases CampusTCPOrigins.Trace.pending_origin preceding value.receive.receipt.served.ticket pending with old | created
  · simp only [CampusTCPModel.Input.initial, Theory.Outstanding.State.initial, List.not_mem_nil] at old
  · obtain ⟨assignment, index, ingress, produced, member, event, selected, exactItem, _⟩ := created
    obtain ⟨first, rest, split, prefixTrace⟩ := CampusTCPFacts.Trace.preceding preceding assignment member
    rcases CampusTCPOrigins.Trace.outputs_origin prefixTrace produced (List.mem_of_getElem? selected) with old | created
    · simp only [CampusTCPModel.Input.initial, List.not_mem_nil] at old
    · obtain ⟨producer, member, emitted, _, _⟩ := created
      have sameProduced : value.receive.receipt.served.ticket.value.produced = produced := by rw [exactItem]; rfl
      refine ⟨prior, preceding, producer, ?_, ?_⟩
      · rw [split]
        exact List.mem_append_left _ member
      · rw [sameProduced]
        exact emitted

private theorem startup_service_ordinary
    (value : CampusTCPFacts.StartupDelivery (input := input) report time actor packet kind)
    (notSyn : kind ≠ .syn) : value.receive.receipt.served.mode = .ordinary := by
  rw [CampusTCPOrigins.service_mode value.service.joint.step value.receive.receipt.served value.service.present]
  cases connected : value.service.joint.step.before.connection with
  | startup stage pending => rfl
  | application complete endpoints => rfl
  | recovering current =>
    obtain ⟨prior, preceding, producer, member, emitted⟩ := source_in_service_prefix value
    have opens := CampusTCPStartupOrigins.Trace.recovering_startup_opens preceding rfl connected
    have kindEq := value.sourceKind
    cases produced : value.receive.receipt.served.ticket.value.produced with
    | startup actual output present =>
      have recorded := CampusTCPStartupProductionFacts.Step.startup_output_recorded producer actual output present
        (by simpa only [produced] using emitted)
      obtain ⟨remote, policy, event⟩ := opens actual (List.mem_filterMap.mpr ⟨producer, member, recorded⟩)
      simp only [produced, CampusTCPFacts.startupKind, event, Option.some.injEq] at kindEq
      exact False.elim (notSyn kindEq.symm)
    | application actor actual output origin | recovery actual occurrence present =>
      simp only [produced, CampusTCPFacts.startupKind, reduceCtorEq] at kindEq

theorem Slice.lanes (history : CampusTCPFacts.StartupHistory (input := input) report complete)
    (slice : Slice history) :
    ∃ entry session,
      history.ack.receive.receipt.served.evidence.admission.phase = .data session ∧
      session.entry = entry ∧
      session.original = TCP.Admission.Lane.initial (input.active.iss.add 1)
        history.synAck.receive.receipt.served.ticket.value.source.packet.segment.window
        input.passive.iss (input.active.iss.add 1) ∧
      session.reply = TCP.Admission.Lane.initial (input.passive.iss.add 1)
        history.ack.receive.receipt.served.ticket.value.source.packet.segment.window
        (input.active.iss.add 1) (input.passive.iss.add 1) ∧
      session.clientMSS = TCP.Handshake.receiveOffer input.active ∧
      session.serverMSS = TCP.Handshake.receiveOffer input.passive ∧
      ∃ syn : CampusTCPService.Processing
          (input.contextFor history.syn.receive.receipt.served.ticket.value.gateway)
          history.syn.receive.receipt.served.before history.syn.receive.receipt.served.ticket.value.source input.zone
          history.syn.receive.receipt.served.mode,
        history.syn.receive.receipt.served.evidence.processing = some syn ∧ entry = syn.prepared.attachment.entry := by
  obtain ⟨syn, synSelected, synOutput⟩ := history.syn.receive.receipt.served.evidence.processed_of_output
    history.syn.receive.receipt.emission history.syn.receive.receipt.emitted
  obtain ⟨synAck, synAckSelected, synAckOutput⟩ := history.synAck.receive.receipt.served.evidence.processed_of_output
    history.synAck.receive.receipt.emission history.synAck.receive.receipt.emitted
  obtain ⟨ack, ackSelected, ackOutput⟩ := history.ack.receive.receipt.served.evidence.processed_of_output
    history.ack.receive.receipt.emission history.ack.receive.receipt.emitted
  have synStates := history.syn.receive.receipt.served.evidence.processing_states syn synSelected
  have synAckStates := history.synAck.receive.receipt.served.evidence.processing_states synAck synAckSelected
  have ackStates := history.ack.receive.receipt.served.evidence.processing_states ack ackSelected
  have synCommitted := syn.output_committed _ synOutput
  have synAckCommitted := synAck.output_committed _ synAckOutput
  have ackCommitted := ack.output_committed _ ackOutput
  have synAckOrdinary := startup_service_ordinary history.synAck (by decide)
  have ackOrdinary := startup_service_ordinary history.ack (by decide)
  obtain ⟨clientMSS, clientSelected, synPhase⟩ := TCP.AdmissionExecution.Result.learned_syn syn.admitted slice.emptyAdmission
  have synAckBefore : history.synAck.receive.receipt.served.before.admission.phase =
      .syn syn.prepared.attachment.entry
        history.syn.receive.receipt.served.ticket.value.source.packet.segment.sequence
        history.syn.receive.receipt.served.ticket.value.source.packet.segment.window clientMSS := by
    rw [slice.synAckAdmission, synStates.2, synCommitted]
    exact synPhase
  obtain ⟨serverMSS, serverSelected, synAckPhase⟩ := TCP.Admission.Result.learned_synAck
    (TCP.AdmissionExecution.Result.asLegacy synAck.admitted
      (TCP.AdmissionExecution.Result.ordinary_legacy synAck.admitted synAckOrdinary)) synAckBefore
  rw [TCP.AdmissionExecution.Result.asLegacy_state] at synAckPhase
  have ackBefore : history.ack.receive.receipt.served.before.admission.phase =
      .synAck syn.prepared.attachment.entry
        history.syn.receive.receipt.served.ticket.value.source.packet.segment.sequence
        history.syn.receive.receipt.served.ticket.value.source.packet.segment.window
        history.synAck.receive.receipt.served.ticket.value.source.packet.segment.sequence
        history.synAck.receive.receipt.served.ticket.value.source.packet.segment.window clientMSS serverMSS := by
    rw [slice.ackAdmission, synAckStates.2, synAckCommitted]
    exact synAckPhase
  obtain ⟨session, phase, entry, original, reply, client, server⟩ := TCP.Admission.Result.established_lanes
    (TCP.AdmissionExecution.Result.asLegacy ack.admitted
      (TCP.AdmissionExecution.Result.ordinary_legacy ack.admitted ackOrdinary)) ackBefore
  rw [TCP.AdmissionExecution.Result.asLegacy_state] at phase
  have synPacket := history.syn.receive.same.trans history.syn.packet
  have synAckPacket := history.synAck.receive.same.trans history.synAck.packet
  have ackPacket := history.ack.receive.same.trans history.ack.packet
  have synSequence := history.syn.receive.receipt.bytePath.fields.2.symm.trans
    (congrArg (fun value : TCP.EstablishedReceive.Input => value.packet.segment.sequence) synPacket)
  have synAckSequence := history.synAck.receive.receipt.bytePath.fields.2.symm.trans
    (congrArg (fun value : TCP.EstablishedReceive.Input => value.packet.segment.sequence) synAckPacket)
  have ackSequence := history.ack.receive.receipt.bytePath.fields.2.symm.trans
    (congrArg (fun value : TCP.EstablishedReceive.Input => value.packet.segment.sequence) ackPacket)
  have ackAcknowledgment := history.ack.receive.receipt.bytePath.control_fields.1.symm.trans
    (congrArg (fun value : TCP.EstablishedReceive.Input => value.packet.segment.acknowledgment) ackPacket)
  have clientSequence := complete.certificate.syn.path.fields.2.trans
    complete.certificate.activePending.output_fields.2.1
  rw [complete.certificate.pending_fields.1, complete.activeConfig] at clientSequence
  have serverSequence := complete.certificate.synAck.path.fields.2.trans
    complete.certificate.passivePending.output_fields.2.1
  rw [complete.certificate.pending_fields.2.2.1, complete.passiveConfig] at serverSequence
  have ackSequenceExpected := complete.certificate.passive.accepted.2.2.1
  rw [complete.certificate.pending_fields.2.2.2, clientSequence] at ackSequenceExpected
  have ackAcknowledgmentExpected := complete.certificate.passive.accepted.2.2.2
  rw [complete.certificate.pending_fields.2.2.1, complete.passiveConfig] at ackAcknowledgmentExpected
  have synOptions := history.syn.receive.receipt.bytePath.control_fields.2.2.2.symm.trans
    ((congrArg (fun value : TCP.EstablishedReceive.Input => value.packet.segment.options) synPacket).trans
      (complete.certificate.syn.path.control_fields.2.2.2.trans
        complete.certificate.activePending.output_fields.2.2.2.2.2.1))
  rw [complete.certificate.pending_fields.1, complete.activeConfig] at synOptions
  have synAckOptions := history.synAck.receive.receipt.bytePath.control_fields.2.2.2.symm.trans
    ((congrArg (fun value : TCP.EstablishedReceive.Input => value.packet.segment.options) synAckPacket).trans
      (complete.certificate.synAck.path.control_fields.2.2.2.trans
        complete.certificate.passivePending.output_fields.2.2.2.2.2.1))
  rw [complete.certificate.pending_fields.2.2.1, complete.passiveConfig] at synAckOptions
  change TCP.MSS.readStartup history.syn.receive.receipt.served.ticket.value.produced.output.packet.segment.options =
    .ok clientMSS at clientSelected
  change TCP.MSS.readStartup history.synAck.receive.receipt.served.ticket.value.produced.output.packet.segment.options =
    .ok serverMSS at serverSelected
  rw [synOptions, TCP.Handshake.options_selected] at clientSelected
  rw [synAckOptions, TCP.Handshake.options_selected] at serverSelected
  have clientOffer := (Except.ok.inj clientSelected).symm
  have serverOffer := (Except.ok.inj serverSelected).symm
  refine ⟨syn.prepared.attachment.entry, session, ?_, entry, ?_, ?_, client.trans clientOffer,
    server.trans serverOffer, ?_⟩
  · rw [ackStates.2, ackCommitted]
    exact phase
  · change session.original = TCP.Admission.Lane.initial
      (history.syn.receive.receipt.served.ticket.value.produced.output.packet.segment.sequence.add 1)
      history.synAck.receive.receipt.served.ticket.value.source.packet.segment.window
      history.synAck.receive.receipt.served.ticket.value.produced.output.packet.segment.sequence
      (history.syn.receive.receipt.served.ticket.value.produced.output.packet.segment.sequence.add 1) at original
    simpa only [synSequence, clientSequence, synAckSequence, serverSequence] using original
  · change session.reply = TCP.Admission.Lane.initial
      (history.synAck.receive.receipt.served.ticket.value.produced.output.packet.segment.sequence.add 1)
      history.ack.receive.receipt.served.ticket.value.source.packet.segment.window
      history.ack.receive.receipt.served.ticket.value.produced.output.packet.segment.sequence
      history.ack.receive.receipt.served.ticket.value.produced.output.packet.segment.acknowledgment at reply
    simpa only [synAckSequence, serverSequence, ackSequence, ackSequenceExpected,
      ackAcknowledgment, ackAcknowledgmentExpected] using reply
  · exact ⟨syn, synSelected, rfl⟩

theorem Slice.aligned (history : CampusTCPFacts.StartupHistory (input := input) report complete)
    (slice : Slice history) :
    ∃ entry session, history.ack.receive.receipt.served.evidence.admission.phase = .data session ∧
      Alignment input complete entry session ∧
      history.ack.receive.receipt.served.evidence.tracker.records = [⟨entry, true⟩] := by
  obtain ⟨entry, session, phase, entryEq, original, reply, clientMSS, serverMSS,
    syn, synSelected, synEntry⟩ := slice.lanes history
  obtain ⟨synAck, synAckSelected, synAckOutput⟩ := history.synAck.receive.receipt.served.evidence.processed_of_output
    history.synAck.receive.receipt.emission history.synAck.receive.receipt.emitted
  obtain ⟨ack, ackSelected, ackOutput⟩ := history.ack.receive.receipt.served.evidence.processed_of_output
    history.ack.receive.receipt.emission history.ack.receive.receipt.emitted
  have synOutput : syn.outcome.output = some history.syn.receive.receipt.emission := by
    obtain ⟨actual, selected, emitted⟩ := history.syn.receive.receipt.served.evidence.processed_of_output
      history.syn.receive.receipt.emission history.syn.receive.receipt.emitted
    have same : actual = syn := Option.some.inj (selected.symm.trans synSelected)
    exact same ▸ emitted
  have synStates := history.syn.receive.receipt.served.evidence.processing_states syn synSelected
  have synAckStates := history.synAck.receive.receipt.served.evidence.processing_states synAck synAckSelected
  have ackStates := history.ack.receive.receipt.served.evidence.processing_states ack ackSelected
  have synCommitted := syn.output_committed _ synOutput
  have synAckCommitted := synAck.output_committed _ synAckOutput
  have synAckOrdinary := startup_service_ordinary history.synAck (by decide)
  have ackOrdinary := startup_service_ordinary history.ack (by decide)
  have synAllowed := TCP.AdmissionExecution.Result.legacy_empty syn.admitted slice.emptyAdmission
  rw [slice.emptyAdmission] at synAllowed
  have synFresh : syn.prepared.attachment.fresh = true := synAllowed.1
  have synDirection : syn.prepared.attachment.direction = .original := synAllowed.2.1
  obtain ⟨clientOffer, _, synPhase⟩ := TCP.AdmissionExecution.Result.learned_syn syn.admitted slice.emptyAdmission
  have synAckBefore : history.synAck.receive.receipt.served.before.admission.phase =
      .syn syn.prepared.attachment.entry
        history.syn.receive.receipt.served.ticket.value.source.packet.segment.sequence
        history.syn.receive.receipt.served.ticket.value.source.packet.segment.window clientOffer := by
    rw [slice.synAckAdmission, synStates.2, synCommitted]
    exact synPhase
  have synAckAllowed := TCP.AdmissionExecution.Result.ordinary_legacy synAck.admitted synAckOrdinary
  rw [synAckBefore] at synAckAllowed
  have synAckEntry : synAck.prepared.attachment.entry = entry := synAckAllowed.1.trans synEntry.symm
  have synAckFresh : synAck.prepared.attachment.fresh = false := synAckAllowed.2.1
  have synAckDirection : synAck.prepared.attachment.direction = .reply := synAckAllowed.2.2.1
  obtain ⟨serverOffer, _, synAckPhase⟩ := TCP.Admission.Result.learned_synAck
    (TCP.AdmissionExecution.Result.asLegacy synAck.admitted
      (TCP.AdmissionExecution.Result.ordinary_legacy synAck.admitted synAckOrdinary)) synAckBefore
  rw [TCP.AdmissionExecution.Result.asLegacy_state] at synAckPhase
  have ackBefore : history.ack.receive.receipt.served.before.admission.phase =
      .synAck syn.prepared.attachment.entry
        history.syn.receive.receipt.served.ticket.value.source.packet.segment.sequence
        history.syn.receive.receipt.served.ticket.value.source.packet.segment.window
        history.synAck.receive.receipt.served.ticket.value.source.packet.segment.sequence
        history.synAck.receive.receipt.served.ticket.value.source.packet.segment.window clientOffer serverOffer := by
    rw [slice.ackAdmission, synAckStates.2, synAckCommitted]
    exact synAckPhase
  have ackAllowed := TCP.AdmissionExecution.Result.ordinary_legacy ack.admitted ackOrdinary
  rw [ackBefore] at ackAllowed
  have ackEntry : ack.prepared.attachment.entry = entry := ackAllowed.1.trans synEntry.symm
  have ackFresh : ack.prepared.attachment.fresh = false := ackAllowed.2.1
  have ackDirection : ack.prepared.attachment.direction = .original := ackAllowed.2.2.1
  have originalZone : entry.flow.originalZone = input.zone := by
    have key := congrArg Prod.fst syn.prepared.attached
    change syn.prepared.attachment.entry.flow.zone syn.prepared.attachment.direction = input.zone at key
    simpa only [FlowNAT.Entry.key, FlowNAT.Entry.zone, synDirection, ← synEntry] using key
  have replyZone : entry.flow.replyZone = input.zone := by
    have key := congrArg Prod.fst synAck.prepared.attached
    change synAck.prepared.attachment.entry.flow.zone synAck.prepared.attachment.direction = input.zone at key
    simpa only [FlowNAT.Entry.key, FlowNAT.Entry.zone, synAckDirection, synAckEntry] using key
  have synTarget := syn.output_target _ synOutput
  have synAckTarget := synAck.output_target _ synAckOutput
  rw [synDirection, ← synEntry] at synTarget
  rw [synAckDirection, synAckEntry] at synAckTarget
  have synPacket := history.syn.receive.same.trans history.syn.packet
  have synAckPacket := history.synAck.receive.same.trans history.synAck.packet
  have ackPacket := history.ack.receive.same.trans history.ack.packet
  have serverOutput : complete.certificate.passiveSeed.core.inbound = entry.flow.output .original := by
    rw [(startup_inbound complete).2, ← synPacket, receipt_header, synTarget]
  have clientOutput : complete.certificate.activeSeed.core.inbound = entry.flow.output .reply := by
    rw [(startup_inbound complete).1, ← synAckPacket, receipt_header, synAckTarget]
  have serverWindow : history.synAck.receive.receipt.served.ticket.value.source.packet.segment.window.val =
      input.passive.capacity := by
    change history.synAck.receive.receipt.served.ticket.value.produced.output.packet.segment.window.val = _
    rw [← history.synAck.receive.receipt.bytePath.control_fields.2.2.1, synAckPacket]
    rw [← complete.certificate.window_history.1, complete.certificate.peer_capacities.1, complete.passiveConfig]
  have clientWindow : history.ack.receive.receipt.served.ticket.value.source.packet.segment.window.val =
      input.active.capacity := by
    change history.ack.receive.receipt.served.ticket.value.produced.output.packet.segment.window.val = _
    rw [← history.ack.receive.receipt.bytePath.control_fields.2.2.1, ackPacket]
    rw [← complete.certificate.window_history.2.2.2.1, complete.certificate.peer_capacities.2, complete.activeConfig]
  have firstRecords : syn.outcome.state.records = [⟨entry, false⟩] := by
    rw [syn.fresh_output_records _ synOutput synFresh, slice.emptyTracker, List.nil_append, ← synEntry]
  have secondRecords : synAck.outcome.state.records = [⟨entry, true⟩] := by
    rw [synAck.existing_state synAckFresh,
      (ConntrackLifecycle.prepare_reply _ _ _ synAck.attached synAckDirection).2.2,
      synAckEntry, slice.synAckTracker, synStates.1]
    simp only [ConntrackLifecycle.State.markReply, firstRecords, List.map_cons, List.map_nil,
      ConntrackLifecycle.State.markRecord, ite_true]
  have thirdRecords : ack.outcome.state.records = [⟨entry, true⟩] := by
    rw [ack.existing_state ackFresh,
      (ConntrackLifecycle.prepare_existing_original _ _ _ ack.attached ackFresh ackDirection).choose_spec.2.2.2,
      slice.ackTracker, synAckStates.1, secondRecords]
  refine ⟨entry, session, phase, ?_, ?_⟩
  · refine ⟨entryEq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, clientMSS, serverMSS,
      originalZone, replyZone, ?_, ?_, clientOutput, serverOutput⟩
    · rw [original]; rfl
    · rw [reply]; rfl
    · rw [original]; rfl
    · rw [reply]; rfl
    · rw [original]; rfl
    · rw [reply]; rfl
    · rw [original]; exact serverWindow
    · rw [reply]; exact clientWindow
    · rw [original]; rfl
    · rw [original]; rfl
    · rw [reply]; rfl
    · rw [reply]; rfl
    · rw [clientOutput]
      exact entry.flow.reply_output_reverse
    · rw [serverOutput]
      exact entry.flow.original_output_reverse
  · rw [ackStates.1, thirdRecords]

theorem Alignment.lookup_original (aligned : Alignment input complete entry session)
    (tracker : ConntrackLifecycle.State) (valid : tracker.Valid) (records : tracker.records = [⟨entry, true⟩]) :
    tracker.model.lookup input.zone (TCP.Output.reverse complete.certificate.activeSeed.core.inbound) =
      some ⟨entry.flow, .original⟩ := by
  have member : entry.flow ∈ tracker.model.entries := by
    simp only [ConntrackLifecycle.State.model, records, List.map_cons, List.map_nil, List.mem_singleton]
  have found := FlowNAT.Snapshot.lookup_complete tracker.model valid.1 ⟨entry.flow, .original⟩ member
  simpa only [FlowNAT.Hit.key, FlowNAT.Entry.key, FlowNAT.Entry.zone, aligned.originalZone,
    aligned.clientInput] using found

theorem Alignment.lookup_reply (aligned : Alignment input complete entry session)
    (tracker : ConntrackLifecycle.State) (valid : tracker.Valid) (records : tracker.records = [⟨entry, true⟩]) :
    tracker.model.lookup input.zone (TCP.Output.reverse complete.certificate.passiveSeed.core.inbound) =
      some ⟨entry.flow, .reply⟩ := by
  have member : entry.flow ∈ tracker.model.entries := by
    simp only [ConntrackLifecycle.State.model, records, List.map_cons, List.map_nil, List.mem_singleton]
  have found := FlowNAT.Snapshot.lookup_complete tracker.model valid.1 ⟨entry.flow, .reply⟩ member
  simpa only [FlowNAT.Hit.key, FlowNAT.Entry.key, FlowNAT.Entry.zone, aligned.replyZone,
    aligned.serverInput] using found

theorem Alignment.binding (aligned : Alignment input complete entry session)
    (tracker : ConntrackLifecycle.State) (records : tracker.records = [⟨entry, true⟩]) :
    ∀ record ∈ tracker.records, record.entry.flow = entry.flow → record.entry = session.entry := by
  intro record member _
  simp only [records, List.mem_singleton] at member
  subst record
  exact aligned.entryEq.symm

end Netlib.Check.CampusTCPStartupAlignment
