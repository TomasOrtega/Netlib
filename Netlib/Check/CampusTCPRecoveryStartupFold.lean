import Netlib.Check.CampusTCPRecoveryStartupTransport
import Netlib.Check.CampusTCPRecoveryStartupCold
import Netlib.Check.CampusTCPRecoveryStartupKeys
import Netlib.Check.CampusTCPRecoveryStartupRecords
import Netlib.Check.CampusTCPRecoveryStartupMilestones
import Netlib.Check.TCPHandshakeRecoveryAdvancingOriginsFacts

/-!
# Coordinates from the full actual startup service chain

Each control source is an actual earlier recovery occurrence in the same
report. Its complete header is retained across NAT and retries.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupTransport

open Protocol Protocol.TCP CampusTCPModel CampusTCPRecoveredSetup

variable {input : Input} {events : List CampusTCPModel.Event} {report : Report input events}

structure Aligned (ready : DrainReady report) where
  entry : NetfilterNAT.Entry
  session : Admission.Session
  phase : report.final.primary.transport.admission.phase = .data session
  static : CampusTCPStartupBasis.StaticAlignment input ready.complete entry session
  geometry : CampusTCPRecoveryStartupGeometry.Geometry input.active input.passive session
  trackerValid : report.final.primary.transport.tracker.Valid
  record : ConntrackLifecycle.Record
  member : record ∈ report.final.primary.transport.tracker.records
  recordEntry : record.entry = session.entry
  confirmed : record.seenReply = true

end Netlib.Check.CampusTCPRecoveryStartupTransport

namespace Netlib.Check.CampusTCPRecoveryStartupFold

open Packet Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupTransport (ServiceChain beforeTransport afterTransport PrimaryServices)
open CampusTCPRecoveryStartupCold (ColdProfile)
open CampusTCPRecoveredSetup (DrainReady)

namespace K
export CampusTCPRecoveryStartupKeys (TupleKeys sideHeader)
end K

namespace S
export CampusTCPRecoveryStartupSources (ServiceSource)
end S

variable {input : Input} {events : List CampusTCPModel.Event} {report : Report input events} {ready : DrainReady report}

theorem ServiceChain.after_entry (history : ServiceChain initial services final) (served : Served input)
    (member : served ∈ services) (selected : (afterTransport served).admission.phase.entry = some entry) :
    final.admission.phase.entry = some entry := by
  induction history with
  | nil => cases member
  | cons head primary before rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst served
      exact CampusTCPRecoveryStartupTransport.ServiceChain.entry_preserved rest selected
    · exact ih later

theorem ServiceChain.before_entry (history : ServiceChain initial services final) (served : Served input)
    (member : served ∈ services) (selected : (beforeTransport served).admission.phase.entry = some entry) :
    final.admission.phase.entry = some entry :=
  ServiceChain.after_entry history served member
    (CampusTCPRecoveryStartupTransport.Evidence.entry_preserved served.evidence selected)

structure ObservedService (ready : DrainReady report) (served : Served input) where
  control : C.Step input.active input.passive
  occurrence : C.Emission
  present : control.result.output = some occurrence
  production : served.ticket.value.produced = .recovery control occurrence present
  source : S.ServiceSource report served
  member : occurrence ∈ ready.current.emissions
  shape : TCPHandshakeRecovery.PacketShape input.active input.passive occurrence.actor occurrence.kind served.ticket.value.source.asInput
  header : served.ticket.value.source.packet.header = K.sideHeader ready.complete occurrence.actor

theorem DrainReady.observed_service (ready : DrainReady report) (cold : ColdProfile report)
    (served : Served input) (member : served ∈ report.final.services) : Nonempty (ObservedService ready served) := by
  have only := CampusTCPRecoveryStartupCold.Report.recovery_services report cold served member
  obtain ⟨source⟩ := CampusTCPRecoveryStartupSources.Report.service_source report served member
  cases production : served.ticket.value.produced with
  | startup actual output present | application actor actual output origin =>
    simp only [production, Produced.isRecovery] at only
    cases only
  | recovery control occurrence present =>
    have inside := source.recovering_member control occurrence present production ready.current ready.connection
    have shape := source.recovering_shape control occurrence present production ready.current ready.connection
    refine ⟨⟨control, occurrence, present, production, source, inside, shape, ?_⟩⟩
    change served.ticket.value.produced.output.packet.header = _
    rw [production]
    cases actor : occurrence.actor with
    | active => exact ready.reachable.complete_active_header ready.phase inside actor
    | passive => exact ready.reachable.complete_passive_header ready.phase inside actor

theorem ServiceChain.output_entry (history : ServiceChain initial services final) (served : Served input)
    (member : served ∈ services) (emission : WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission) :
    ∃ processing : CampusTCPService.Processing (input.contextFor served.ticket.value.gateway) served.before
        served.ticket.value.source input.zone served.mode,
      served.evidence.processing = some processing ∧ final.admission.phase.entry = some processing.prepared.attachment.entry := by
  obtain ⟨processing, selected, output⟩ := served.evidence.processed_of_output emission emitted
  have states := served.evidence.processing_states processing selected
  have committed := processing.output_committed emission output
  refine ⟨processing, selected, ServiceChain.after_entry history served member ?_⟩
  change served.evidence.admission.phase.entry = _
  rw [states.2, committed]
  exact AdmissionExecution.Result.selected_entry processing.admitted

private theorem empty_of_no_entry (phase : Admission.Phase) (selected : phase.entry = none) : phase = .empty := by
  cases phase <;> first | rfl | cases selected

private theorem active_of_syn (shape : TCPHandshakeRecovery.PacketShape active passive actor kind packet)
    (flags : packet.packet.segment.flags = 2) : actor = .active := by
  have same := shape.profile.1.symm.trans flags
  cases kind with
  | syn => exact shape.actorEq
  | synAck => exact False.elim ((by decide : (18 : UInt8) ≠ 2) same)
  | finalAck | synReplyAck => exact False.elim ((by decide : (16 : UInt8) ≠ 2) same)

private theorem service_role (history : ServiceChain initial services final) (served : Served input)
    (member : served ∈ services) (observed : ObservedService ready served)
    (processing : CampusTCPService.Processing (input.contextFor served.ticket.value.gateway) served.before
      served.ticket.value.source input.zone served.mode)
    (keys : K.TupleKeys input ready.complete entry) (finalEntry : final.admission.phase.entry = some entry) :
    processing.prepared.attachment.direction = CampusTCPRecoveryStartupPhase.sideDirection observed.occurrence.actor := by
  cases selected : served.before.admission.phase.entry with
  | none =>
    have empty := empty_of_no_entry _ selected
    have legacy := AdmissionExecution.Result.legacy_empty processing.admitted empty
    simp only [Admission.Allowed, empty] at legacy
    have flags := legacy.2.2.1
    have actor := active_of_syn observed.shape flags
    rw [actor]
    exact legacy.2.1
  | some prior =>
    have continued := ServiceChain.before_entry history served member selected
    have same : prior = entry := Option.some.inj (continued.symm.trans finalEntry)
    have picked := CampusTCPRecoveryStartupTransport.admission_before_entry processing.admitted selected
    have entryEq := picked.trans same
    have found := AdmissionExecution.Result.selectedKey processing.admitted
    change processing.prepared.attachment.entry.flow.key processing.prepared.attachment.direction =
      (input.zone, served.ticket.value.source.packet.header) at found
    rw [entryEq] at found
    have compatible : entry.Compatible := entryEq ▸ processing.prepared.compatible
    exact keys.direction compatible found observed.header

private theorem service_coordinates (history : ServiceChain initial services final) (served : Served input)
    (member : served ∈ services) (observed : ObservedService ready served)
    (keys : K.TupleKeys input ready.complete entry) (finalEntry : final.admission.phase.entry = some entry)
    (prior : CampusTCPRecoveryStartupPhase.Coordinates input.active input.passive served.before.admission.phase) :
    CampusTCPRecoveryStartupPhase.Coordinates input.active input.passive served.evidence.admission.phase := by
  cases operation : served.evidence.operation with
  | earlyDrop denied => simpa only [CampusTCPService.Evidence.admission, operation] using prior
  | processed permitted processing =>
    have selected : served.evidence.processing = some processing := by
      simp only [CampusTCPService.Evidence.processing, operation]
    have states := served.evidence.processing_states processing selected
    have role := service_role history served member observed processing keys finalEntry
    have current := CampusTCPRecoveryStartupPhase.Coordinates.admitted prior processing.admitted observed.shape role
    rw [states.2]
    rcases AdmissionExecution.commit_cases processing.admitted processing.outcome.state _ processing.committed with kept | reset
    · rw [kept.1]
      exact current
    · rw [reset.1]
      trivial

private theorem fold_coordinates (history : ServiceChain initial services final)
    (sources : ∀ served ∈ services, Nonempty (ObservedService ready served))
    (keys : K.TupleKeys input ready.complete entry) (finalEntry : final.admission.phase.entry = some entry)
    (prior : CampusTCPRecoveryStartupPhase.Coordinates input.active input.passive initial.admission.phase) :
    CampusTCPRecoveryStartupPhase.Coordinates input.active input.passive final.admission.phase := by
  induction history with
  | nil => exact prior
  | cons served primary before rest ih =>
    obtain ⟨observed⟩ := sources served List.mem_cons_self
    have beforeCoordinates : CampusTCPRecoveryStartupPhase.Coordinates input.active input.passive served.before.admission.phase := by
      change CampusTCPRecoveryStartupPhase.Coordinates input.active input.passive (beforeTransport served).admission.phase
      rw [before]
      exact prior
    have current := service_coordinates (.cons served primary before rest) served List.mem_cons_self observed keys finalEntry beforeCoordinates
    exact ih (fun value member => sources value (List.mem_cons_of_mem served member)) finalEntry current

private theorem admitted_final_ack_data (value : AdmissionExecution.Result mode before packet lifecycle prepared)
    (flags : packet.packet.segment.flags = 16) (original : prepared.attachment.direction = .original) :
    ∃ session, (AdmissionExecution.Result.state value).phase = .data session := by
  cases phase : before.phase with
  | empty =>
    have legacy := AdmissionExecution.Result.legacy_empty value phase
    simp only [Admission.Allowed, phase] at legacy
    exact False.elim ((by decide : (16 : UInt8) ≠ 2) (flags.symm.trans legacy.2.2.1))
  | syn entry iss window mss =>
    rcases AdmissionExecution.Result.legacy_or_stutter value with legacy | ⟨_, stutter⟩
    · simp only [Admission.Allowed, phase] at legacy
      exact False.elim ((by decide : (16 : UInt8) ≠ 18) (flags.symm.trans legacy.2.2.2.1.1))
    · rw [phase] at stutter
      rcases stutter.2.2 with ⟨_, syn, _⟩ | ⟨reply, _⟩
      · exact False.elim ((by decide : (16 : UInt8) ≠ 2) (flags.symm.trans syn.1.1))
      · exact False.elim (FlowNAT.Direction.noConfusion (original.symm.trans reply))
  | synAck entry clientISS clientWindow serverISS serverWindow clientMSS serverMSS =>
    have legacy := AdmissionExecution.Result.legacy_finalAck_control value phase original flags
    obtain ⟨session, data, _⟩ := (AdmissionExecution.Result.asLegacy value legacy).established_lanes phase
    exact ⟨session, by simpa only [AdmissionExecution.Result.asLegacy_state] using data⟩
  | data session =>
    have rank := CampusTCPRecoveryStartupTransport.admission_phase_rank value
    rw [phase] at rank
    cases after : (AdmissionExecution.Result.state value).phase with
    | empty | syn entry iss window mss | synAck entry clientISS clientWindow serverISS serverWindow clientMSS serverMSS =>
      simp only [after, CampusTCPRecoveryStartupTransport.phaseRank] at rank
      omega
    | data current => exact ⟨current, rfl⟩

private theorem data_of_rank (rank : 3 ≤ CampusTCPRecoveryStartupTransport.phaseRank phase) :
    ∃ session, phase = .data session := by
  cases phase with
  | empty | syn entry iss window mss | synAck entry clientISS clientWindow serverISS serverWindow clientMSS serverMSS =>
    simp only [CampusTCPRecoveryStartupTransport.phaseRank] at rank
    omega
  | data session => exact ⟨session, rfl⟩

private theorem after_data (history : ServiceChain initial services final) (served : Served input)
    (member : served ∈ services) (session : Admission.Session)
    (data : (afterTransport served).admission.phase = .data session) :
    ∃ session, final.admission.phase = .data session := by
  induction history with
  | nil => cases member
  | cons head primary before rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst served
      have rank := CampusTCPRecoveryStartupTransport.ServiceChain.phase_rank rest
      rw [data] at rank
      exact data_of_rank rank
    · exact ih later

private theorem derived_alignment (ready : DrainReady report) (cold : ColdProfile report) (primary : PrimaryServices report) :
    Nonempty (CampusTCPRecoveryStartupTransport.Aligned ready) := by
  have milestones : TCPHandshakeRecovery.CompleteMilestones ready.current.receipts ready.complete := by
    simpa only [TCPHandshakeRecovery.AdvancingOrigins, ready.phase] using ready.reachable.advancing_origins
  obtain ⟨syn⟩ := CampusTCPRecoveryStartupMilestones.DrainReady.milestone_service ready milestones.1
  obtain ⟨synAck⟩ := CampusTCPRecoveryStartupMilestones.DrainReady.milestone_service ready milestones.2.1
  obtain ⟨ack⟩ := CampusTCPRecoveryStartupMilestones.DrainReady.milestone_service ready milestones.2.2
  let synService := syn.actual.delivery.receipt.served
  let synAckService := synAck.actual.delivery.receipt.served
  let ackService := ack.actual.delivery.receipt.served
  have stored : ∀ served, served ∈ report.final.services → served ∈ report.steps.filterMap (·.result.service) := by
    intro served member
    exact (congrArg (fun values => served ∈ values) (CampusTCPPrimaryTransport.Report.services report)).mp member
  have synMember := stored synService syn.actual.serviceMember
  have synAckMember := stored synAckService synAck.actual.serviceMember
  have ackMember := stored ackService ack.actual.serviceMember
  have chain := CampusTCPRecoveryStartupTransport.Report.service_chain report primary
  obtain ⟨synObserved⟩ := DrainReady.observed_service ready cold synService syn.actual.serviceMember
  obtain ⟨synAckObserved⟩ := DrainReady.observed_service ready cold synAckService synAck.actual.serviceMember
  obtain ⟨ackObserved⟩ := DrainReady.observed_service ready cold ackService ack.actual.serviceMember
  have synOccurrence := syn.occurrence synObserved.control synObserved.occurrence synObserved.present synObserved.production
  have synAckOccurrence := synAck.occurrence synAckObserved.control synAckObserved.occurrence synAckObserved.present synAckObserved.production
  have ackOccurrence := ack.occurrence ackObserved.control ackObserved.occurrence ackObserved.present ackObserved.production
  have synKind := (congrArg (fun value : C.Emission => value.kind) synOccurrence).trans syn.kindEq
  have synAckKind := (congrArg (fun value : C.Emission => value.kind) synAckOccurrence).trans synAck.kindEq
  have ackKind := (congrArg (fun value : C.Emission => value.kind) ackOccurrence).trans ack.kindEq
  have synActor := (congrArg (fun value : C.Emission => value.actor) synOccurrence).trans syn.actorEq
  have synAckActor := (congrArg (fun value : C.Emission => value.actor) synAckOccurrence).trans synAck.actorEq
  have ackActor := (congrArg (fun value : C.Emission => value.actor) ackOccurrence).trans ack.actorEq
  have synFlags : synService.ticket.value.source.packet.segment.flags = 2 := by
    simpa only [TCP.WireForwarding.Source.asInput, synKind, TCPHandshakeRecovery.Kind.flags] using synObserved.shape.profile.1
  have synAckFlags : synAckService.ticket.value.source.packet.segment.flags = 18 := by
    simpa only [TCP.WireForwarding.Source.asInput, synAckKind, TCPHandshakeRecovery.Kind.flags] using synAckObserved.shape.profile.1
  have ackFlags : ackService.ticket.value.source.packet.segment.flags = 16 := by
    simpa only [TCP.WireForwarding.Source.asInput, ackKind, TCPHandshakeRecovery.Kind.flags] using ackObserved.shape.profile.1
  obtain ⟨synProcessing, synSelected, synFinal⟩ := ServiceChain.output_entry chain synService synMember
    syn.actual.delivery.receipt.emission syn.actual.delivery.receipt.emitted
  obtain ⟨synAckProcessing, synAckSelected, synAckFinal⟩ := ServiceChain.output_entry chain synAckService synAckMember
    synAck.actual.delivery.receipt.emission synAck.actual.delivery.receipt.emitted
  let entry := synProcessing.prepared.attachment.entry
  have synAckEntry : synAckProcessing.prepared.attachment.entry = entry :=
    Option.some.inj (synAckFinal.symm.trans synFinal)
  have synDirection := CampusTCPRecoveryStartupKeys.syn_original synProcessing.admitted synFlags
  have synAckDirection := CampusTCPRecoveryStartupKeys.synAck_reply synAckProcessing.admitted synAckFlags
  have originalKey := AdmissionExecution.Result.selectedKey synProcessing.admitted
  change entry.flow.key synProcessing.prepared.attachment.direction = (input.zone, synService.ticket.value.source.packet.header) at originalKey
  rw [synDirection, synObserved.header, synActor] at originalKey
  have replyKey := AdmissionExecution.Result.selectedKey synAckProcessing.admitted
  change synAckProcessing.prepared.attachment.entry.flow.key synAckProcessing.prepared.attachment.direction =
    (input.zone, synAckService.ticket.value.source.packet.header) at replyKey
  rw [synAckEntry, synAckDirection, synAckObserved.header, synAckActor] at replyKey
  let keys : K.TupleKeys input ready.complete entry :=
    ⟨congrArg Prod.fst originalKey, congrArg Prod.fst replyKey, congrArg Prod.snd originalKey, congrArg Prod.snd replyKey⟩
  obtain ⟨ackProcessing, ackSelected, ackOutput⟩ := ackService.evidence.processed_of_output
    ack.actual.delivery.receipt.emission ack.actual.delivery.receipt.emitted
  have role := service_role chain ackService ackMember ackObserved ackProcessing keys synFinal
  have original : ackProcessing.prepared.attachment.direction = .original := by
    simpa only [ackActor, CampusTCPRecoveryStartupPhase.sideDirection] using role
  obtain ⟨after, data⟩ := admitted_final_ack_data ackProcessing.admitted ackFlags original
  have states := ackService.evidence.processing_states ackProcessing ackSelected
  have committed := ackProcessing.output_committed ack.actual.delivery.receipt.emission ackOutput
  have afterData : (afterTransport ackService).admission.phase = .data after := by
    change ackService.evidence.admission.phase = _
    rw [states.2, committed]
    exact data
  obtain ⟨session, phase⟩ := after_data chain ackService ackMember after afterData
  have selected : session.entry = entry := by
    have current := synFinal
    rw [phase] at current
    exact Option.some.inj current
  have sources : ∀ served ∈ report.steps.filterMap (·.result.service), Nonempty (ObservedService ready served) := by
    intro served member
    apply DrainReady.observed_service ready cold served
    exact (congrArg (fun values => served ∈ values) (CampusTCPPrimaryTransport.Report.services report)).mpr member
  have coordinates := fold_coordinates chain sources keys synFinal (by trivial)
  have geometry : CampusTCPRecoveryStartupGeometry.Geometry input.active input.passive session := by
    simpa only [CampusTCPRecoveryStartupPhase.Coordinates, phase] using coordinates
  obtain ⟨record, member, recordEntry, confirmed⟩ := CampusTCPRecoveryStartupRecords.ServiceChain.reply_record chain
    synAckService synAckMember synAckProcessing synAckSelected synAckDirection
  exact ⟨⟨entry, session, phase, keys.static geometry selected, geometry,
    report.final.primary.history.tracker_valid, record, member, recordEntry.trans (synAckEntry.trans selected.symm), confirmed⟩⟩

end Netlib.Check.CampusTCPRecoveryStartupFold

namespace Netlib.Check.CampusTCPRecoveryStartupTransport

open CampusTCPModel CampusTCPRecoveredSetup CampusTCPRecoveryStartupCold

theorem aligned (ready : DrainReady report) (cold : ColdProfile report) (primary : PrimaryServices report) :
    Nonempty (Aligned ready) :=
  CampusTCPRecoveryStartupFold.derived_alignment ready cold primary

end Netlib.Check.CampusTCPRecoveryStartupTransport
