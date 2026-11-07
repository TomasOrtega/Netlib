import Netlib.Check.CampusTCPRecoveryStartupLinkInput
import Netlib.Check.CampusTCPRecoveryStartupLinkTarget

/-!
# Current endpoint fields for an actual startup link

Gateway rewrites retain the control fields. The current phase supplies the
endpoint tuple and cursors without changing the retained window markers.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupReceiveFields

open Packet Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupCurrentNative (Current)
open CampusTCPRecoveryStartupPhase (sideDirection)

namespace J
export CampusTCPStartupJobs (Source PacketItem)
end J
namespace R
export TCPHandshakeRecovery (PacketShape PacketInventory Template PhaseInvariant PreDataClean)
end R

variable {input : Input} {baseEvents events : List CampusTCPModel.Event}
variable {base : Report input baseEvents} {report : Report input events}
variable {current : C.State input.active input.passive} {header : Header}
variable {profile : CampusTCPStartupNative.Profile (input.contextFor .primary)
  (beforeService input base.final .primary) input.zone header}
variable {source : C.Emission} {packet : Handshake.Input}
variable {opened : TCPHandshake.Opened input.active}
variable {answered : TCPHandshake.Answered input.active input.passive}
variable {acknowledged : TCPHandshake.Acknowledged input.active input.passive}
variable {complete : TCPHandshake.Completed input.active input.passive}

def PassiveTarget (entry : NetfilterNAT.Entry) (passive : Handshake.Local) : Prop :=
  (entry.flow.output .original).destination = passive.socket.address ∧
    (entry.flow.output .original).destinationPort = passive.socket.port

structure Fields (current : C.State input.active input.passive) (entry : NetfilterNAT.Entry)
    (source : C.Emission) (packet : Handshake.Input) : Prop where
  member : source ∈ current.emissions
  shape : R.PacketShape input.active input.passive source.actor source.kind packet
  header : packet.packet.header = entry.flow.output (sideDirection source.actor)

private theorem emission_shape {wire : W.Source} {active passive : Handshake.Local}
    {actor : TCPHandshakeRecovery.Side} {kind : TCPHandshakeRecovery.Kind}
    (emission : W.Emission wire.packet)
    (shape : R.PacketShape active passive actor kind wire.asInput) :
    R.PacketShape active passive actor kind emission.asInput := by
  have control := emission.control
  have options : emission.asInput.packet.segment.options = wire.asInput.packet.segment.options := control.2.2.2.2.2.2
  refine ⟨shape.actorEq, ?_, control.1.trans shape.sequence,
    control.2.1.trans shape.acknowledgment,
    (congrArg (fun window : InternetChecksum.Word => window.val) control.2.2.2.2.1).trans shape.capacity,
    control.2.2.2.2.2.2.trans shape.options⟩
  refine ⟨control.2.2.2.1.trans shape.profile.1, ?_, emission.payload.trans shape.payload⟩
  change Handshake.optionProfile emission.asInput kind.flags
  unfold Handshake.optionProfile
  split
  · exact options.trans (by simpa only [Handshake.optionProfile, show kind.flags = 16 by assumption, ite_true] using shape.profile.2.1)
  · rw [options]
    simpa only [Handshake.optionProfile, show kind.flags ≠ 16 by assumption, ite_false] using shape.profile.2.1

theorem link_fields (value : Current base profile report current)
    (item : J.PacketItem input) (serviceIndex : Nat) (served : Served input)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (selected : J.Source input) (production : served.ticket.value.produced = selected.produced)
    (payload : item.value.payload = .link serviceIndex served emission emitted)
    (pending : item ∈ report.final.custody.pending) :
    Fields current profile.entry selected.occurrence emission.asInput := by
  let job : CampusTCPStartupJobs.Job input := .link item serviceIndex served emission emitted selected production payload
  have inside := CampusTCPRecoveryStartupCurrentSources.Job.recovering_member report job pending value.connected
  have shape := (CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report value.connected).output_shape inside
  have actualShape : R.PacketShape input.active input.passive selected.occurrence.actor selected.occurrence.kind
      served.ticket.value.source.asInput := by
    change R.PacketShape input.active input.passive selected.occurrence.actor selected.occurrence.kind served.ticket.value.produced.output
    rw [production]
    exact shape
  exact ⟨inside, emission_shape emission actualShape,
    CampusTCPRecoveryStartupLinkTarget.link_header value item serviceIndex served emission emitted selected production payload pending⟩

private theorem template_header (value : Current base profile report current)
    (template : R.Template current index actor kind original) :
    original.packet.header = profile.entry.flow.input (sideDirection actor) := by
  obtain ⟨output, member, stamp, selectedActor, selectedKind, same⟩ := template
  have actual := value.headers output member
  rw [same, selectedActor] at actual
  exact actual

private theorem Fields.template (fields : Fields current profile.entry source packet)
    (value : Current base profile report current) (control : TCPHandshakeRecovery.TemplateKind source.kind)
    (selected : current.phase.controlTemplate source.kind = some original) : source.packet = original := by
  have known := (CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report value.connected).packet_inventory.templates source fields.member control
  exact Option.some.inj (known.symm.trans selected)

theorem Fields.syn_opened (fields : Fields current profile.entry source packet)
    (value : Current base profile report current) (kind : source.kind = .syn)
    (phase : current.phase = .opened opened) (valid : input.passive.Valid)
    (target : PassiveTarget profile.entry input.passive) :
    source.packet = opened.pending.output ∧ input.passive.Valid ∧
      Handshake.destination input.passive packet ∧ Handshake.Profile packet 2 := by
  have same := Fields.template fields value (Or.inl kind) (by rw [phase, kind]; rfl)
  have actor : source.actor = .active := by simpa only [kind, TCPHandshakeRecovery.Kind.actor] using fields.shape.actorEq
  refine ⟨same, valid, ?_, ?_⟩
  · change packet.packet.header.destination = _ ∧ packet.packet.header.destinationPort = _
    rw [fields.header, actor]
    exact target
  · simpa only [kind, TCPHandshakeRecovery.Kind.flags] using fields.shape.profile

private theorem opened_tuple (fields : Fields current profile.entry source packet)
    (value : Current base profile report current)
    (template : R.Template current opened.index .active .syn opened.pending.output)
    (actor : source.actor = .passive) :
    packet.packet.header = Handshake.inbound opened.pending.config opened.pending.remote := by
  have original := template_header value template
  rw [Handshake.inbound, ← opened.pending.output_fields.1, original]
  rw [fields.header, actor]
  rfl

theorem Fields.synAck_answered (fields : Fields current profile.entry source packet)
    (value : Current base profile report current) (kind : source.kind = .synAck)
    (phase : current.phase = .answered answered) :
    source.packet = answered.pending.output ∧ Handshake.ActiveAccepted answered.opened.pending packet := by
  have prior := (CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report value.connected).template_sources
  have templates : R.Template current answered.opened.index .active .syn answered.opened.pending.output ∧
      R.Template current answered.index .passive .synAck answered.pending.output := by
    simpa only [TCPHandshakeRecovery.TemplateSources, phase] using prior
  have actor : source.actor = .passive := by simpa only [kind, TCPHandshakeRecovery.Kind.actor] using fields.shape.actorEq
  have config := (Handshake.activeOpen_fields _ _ _ _ answered.opened.computed).1
  refine ⟨Fields.template fields value (Or.inr kind) (by rw [phase, kind]; rfl),
    opened_tuple fields value templates.1 actor, ?_, ?_⟩
  · simpa only [kind, TCPHandshakeRecovery.Kind.flags] using fields.shape.profile
  · rw [config]
    simpa only [kind, TCPHandshakeRecovery.Kind.acknowledgment] using fields.shape.acknowledgment

private theorem discard_ack (fields : Fields current profile.entry source packet)
    (value : Current base profile report current) (kind : source.kind = .synReplyAck)
    (template : R.Template current opened.index .active .syn opened.pending.output) :
    TCPHandshakeRecovery.DiscardAckFields input.active opened packet := by
  have actor : source.actor = .passive := by simpa only [kind, TCPHandshakeRecovery.Kind.actor] using fields.shape.actorEq
  have openedFields := Handshake.activeOpen_fields _ _ _ _ opened.computed
  refine ⟨?_, ?_, ?_⟩
  · simpa only [kind, TCPHandshakeRecovery.Kind.flags] using fields.shape.profile
  · simpa only [openedFields.1, openedFields.2.1] using opened_tuple fields value template actor
  · simpa only [kind, TCPHandshakeRecovery.Kind.acknowledgment] using fields.shape.acknowledgment

theorem Fields.discard_opened (fields : Fields current profile.entry source packet)
    (value : Current base profile report current) (kind : source.kind = .synReplyAck)
    (phase : current.phase = .opened opened) : TCPHandshakeRecovery.DiscardAckFields input.active opened packet := by
  have prior := (CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report value.connected).template_sources
  exact discard_ack fields value kind (by simpa only [TCPHandshakeRecovery.TemplateSources, phase] using prior)

theorem Fields.discard_answered (fields : Fields current profile.entry source packet)
    (value : Current base profile report current) (kind : source.kind = .synReplyAck)
    (phase : current.phase = .answered answered) : TCPHandshakeRecovery.DiscardAckFields input.active answered.opened packet := by
  have prior := (CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report value.connected).template_sources
  have templates : R.Template current answered.opened.index .active .syn answered.opened.pending.output ∧
      R.Template current answered.index .passive .synAck answered.pending.output := by
    simpa only [TCPHandshakeRecovery.TemplateSources, phase] using prior
  exact discard_ack fields value kind templates.1


private theorem reverse_reverse (header : Header) : Output.reverse (Output.reverse header) = header := by
  cases header
  rfl

private theorem active_tuple (fields : Fields current profile.entry source packet)
    (value : Current base profile report current)
    (template : R.Template current index .active kind original)
    {seed : Endpoint.State} (seedHeader : Output.reverse seed.core.inbound = original.packet.header)
    (actor : source.actor = .passive) : packet.packet.header = seed.core.inbound := by
  have originalHeader := template_header value template
  have restored := congrArg Output.reverse seedHeader
  rw [reverse_reverse] at restored
  rw [restored, originalHeader, fields.header, actor]
  rfl

private theorem passive_tuple (fields : Fields current profile.entry source packet)
    (value : Current base profile report current)
    (template : R.Template current index .passive kind original)
    {seed : Endpoint.State} (seedHeader : Output.reverse seed.core.inbound = original.packet.header)
    (actor : source.actor = .active) : packet.packet.header = seed.core.inbound := by
  have originalHeader := template_header value template
  have restored := congrArg Output.reverse seedHeader
  rw [reverse_reverse] at restored
  rw [restored, originalHeader, fields.header, actor]
  rfl

theorem Fields.final_ack_accepted (fields : Fields current profile.entry source packet)
    (value : Current base profile report current) (kind : source.kind = .finalAck)
    (phase : current.phase = .acknowledged acknowledged client) :
    Handshake.PassiveAccepted acknowledged.answered.pending packet := by
  have prior := (CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report value.connected).template_sources
  have templates : R.Template current acknowledged.answered.opened.index .active .syn acknowledged.answered.opened.pending.output ∧
      R.Template current acknowledged.answered.index .passive .synAck acknowledged.answered.pending.output := by
    simpa only [TCPHandshakeRecovery.TemplateSources, phase] using prior
  have actor : source.actor = .active := by simpa only [kind, TCPHandshakeRecovery.Kind.actor] using fields.shape.actorEq
  have listened := Handshake.listenSyn_fields _ _ _ _ acknowledged.answered.computed
  have passiveHeader := template_header value templates.2
  have tuple : packet.packet.header = acknowledged.answered.pending.input.packet.header := by
    have restore := congrArg Output.reverse acknowledged.answered.pending.output_fields.1
    rw [reverse_reverse] at restore
    rw [← restore, passiveHeader, fields.header, actor]
    rfl
  refine ⟨tuple, ?_, ?_, ?_⟩
  · simpa only [kind, TCPHandshakeRecovery.Kind.flags] using fields.shape.profile
  · rw [listened.2.1, TCPHandshakeRecovery.Answered.input_sequence acknowledged.answered]
    simpa only [kind, TCPHandshakeRecovery.Kind.sequence] using fields.shape.sequence
  · rw [listened.1]
    simpa only [kind, TCPHandshakeRecovery.Kind.acknowledgment] using fields.shape.acknowledgment

private theorem local_earlier (value : Current base profile report current) :
    ∀ actor operation, operation ∈ current.applicationSteps actor → operation.stamp < report.final.time := by
  simpa only [CampusTCPChronology.Chronological, value.connected, CampusTCPChronology.Earlier] using
    CampusTCPChronology.Report.chronological report

theorem Fields.empty_ack_acknowledged (fields : Fields current profile.entry source packet)
    (value : Current base profile report current) (kind : source.kind = .synReplyAck)
    (phase : current.phase = .acknowledged acknowledged client) :
    TCPHandshakeRecovery.EmptyAckFields client packet report.final.time := by
  have reachable := CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report value.connected
  have clean : R.PreDataClean acknowledged.ready.seed client := by
    simpa only [TCPHandshakeRecovery.PreDataFrames, phase] using reachable.predata_frames
  have templates : R.Template current acknowledged.answered.opened.index .active .syn acknowledged.answered.opened.pending.output ∧
      R.Template current acknowledged.answered.index .passive .synAck acknowledged.answered.pending.output := by
    simpa only [TCPHandshakeRecovery.TemplateSources, phase] using reachable.template_sources
  have actor : source.actor = .passive := by simpa only [kind, TCPHandshakeRecovery.Kind.actor] using fields.shape.actorEq
  have tuple := active_tuple fields value templates.1 (TCPHandshakeRecovery.Acknowledged.seed_header acknowledged) actor
  have coordinates := TCPHandshakeRecovery.Acknowledged.seed_coordinates acknowledged
  have config := (Handshake.activeOpen_fields _ _ _ _ acknowledged.answered.opened.computed).1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [kind, TCPHandshakeRecovery.Kind.flags] using fields.shape.profile
  · rw [clean.1.core]
    exact tuple
  · rw [clean.1.core, coordinates.2.1]
    simpa only [kind, TCPHandshakeRecovery.Kind.sequence] using fields.shape.sequence
  · rw [clean.1.core, acknowledged.ready.derived]
    change packet.packet.segment.acknowledgment = acknowledged.answered.opened.pending.config.iss.add 1
    rw [config]
    simpa only [kind, TCPHandshakeRecovery.Kind.acknowledgment] using fields.shape.acknowledgment
  · intro old member
    exact local_earlier value .active old (by simpa only [TCPHandshakeRecovery.State.applicationSteps, phase] using member)

theorem Fields.empty_ack_complete_client (fields : Fields current profile.entry source packet)
    (value : Current base profile report current) (kind : source.kind = .synReplyAck)
    (phase : current.phase = .complete complete client server) :
    TCPHandshakeRecovery.EmptyAckFields client packet report.final.time := by
  have reachable := CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report value.connected
  have clean : R.PreDataClean complete.certificate.activeSeed client := by
    have frames : R.PreDataClean complete.certificate.activeSeed client ∧ R.PreDataClean complete.certificate.passiveSeed server := by
      simpa only [TCPHandshakeRecovery.PreDataFrames, phase] using reachable.predata_frames
    exact frames.1
  have templates : R.Template current complete.input.times.opened .active .syn complete.certificate.activePending.output ∧
      R.Template current complete.input.times.synReceived .passive .synAck complete.certificate.passivePending.output := by
    simpa only [TCPHandshakeRecovery.TemplateSources, phase] using reachable.template_sources
  have actor : source.actor = .passive := by simpa only [kind, TCPHandshakeRecovery.Kind.actor] using fields.shape.actorEq
  have tuple := active_tuple fields value templates.1 (TCPHandshakeRecovery.Completed.active_header complete) actor
  have coordinates := complete.certificate.initial_sequences
  rw [complete.activeConfig, complete.passiveConfig] at coordinates
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [kind, TCPHandshakeRecovery.Kind.flags] using fields.shape.profile
  · rw [clean.1.core]
    exact tuple
  · rw [clean.1.core, coordinates.2.2.1]
    simpa only [kind, TCPHandshakeRecovery.Kind.sequence] using fields.shape.sequence
  · rw [clean.1.core, coordinates.1]
    simpa only [kind, TCPHandshakeRecovery.Kind.acknowledgment] using fields.shape.acknowledgment
  · intro old member
    exact local_earlier value .active old (by simpa only [TCPHandshakeRecovery.State.applicationSteps, phase] using member)

theorem Fields.empty_ack_complete_server (fields : Fields current profile.entry source packet)
    (value : Current base profile report current) (kind : source.kind = .finalAck)
    (phase : current.phase = .complete complete client server) :
    TCPHandshakeRecovery.EmptyAckFields server packet report.final.time := by
  have reachable := CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report value.connected
  have clean : R.PreDataClean complete.certificate.passiveSeed server := by
    have frames : R.PreDataClean complete.certificate.activeSeed client ∧ R.PreDataClean complete.certificate.passiveSeed server := by
      simpa only [TCPHandshakeRecovery.PreDataFrames, phase] using reachable.predata_frames
    exact frames.2
  have templates : R.Template current complete.input.times.opened .active .syn complete.certificate.activePending.output ∧
      R.Template current complete.input.times.synReceived .passive .synAck complete.certificate.passivePending.output := by
    simpa only [TCPHandshakeRecovery.TemplateSources, phase] using reachable.template_sources
  have actor : source.actor = .active := by simpa only [kind, TCPHandshakeRecovery.Kind.actor] using fields.shape.actorEq
  have tuple := passive_tuple fields value templates.2 (TCPHandshakeRecovery.Completed.passive_header complete) actor
  have coordinates := complete.certificate.initial_sequences
  rw [complete.activeConfig, complete.passiveConfig] at coordinates
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [kind, TCPHandshakeRecovery.Kind.flags] using fields.shape.profile
  · rw [clean.1.core]
    exact tuple
  · rw [clean.1.core, coordinates.2.2.2.2.2]
    simpa only [kind, TCPHandshakeRecovery.Kind.sequence] using fields.shape.sequence
  · rw [clean.1.core, coordinates.2.2.2.1]
    simpa only [kind, TCPHandshakeRecovery.Kind.acknowledgment] using fields.shape.acknowledgment
  · intro old member
    exact local_earlier value .passive old (by simpa only [TCPHandshakeRecovery.State.applicationSteps, phase] using member)

end Netlib.Check.CampusTCPRecoveryStartupReceiveFields
