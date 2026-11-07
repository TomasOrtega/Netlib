import Netlib.Check.CampusTCPRecoveryStartupCurrentCoordinates
import Netlib.Check.CampusTCPRecoveryStartupEmptyTracker
import Netlib.Check.CampusTCPRecoveryStartupOpened
import Netlib.Check.CampusTCPRecoveryStartupAdmissionGuards
import Netlib.Check.TCPHandshakeRecoveryOutputTTLFacts

/-!
# Native startup readiness from the current actual prefix

The installed profile and actual OPEN derive current binding, packet roles,
observations, and lane geometry. The source TTL comes from its real occurrence.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupCurrentNative

open Packet Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupTransport (PrimaryServices)
open CampusTCPRecoveryStartupCurrentEntry (History EntryMatches)
open CampusTCPRecoveryStartupPhase (Coordinates sideDirection)

variable {input : Input} {baseEvents events : List CampusTCPModel.Event}
variable {base : Report input baseEvents} {report : Report input events}
variable {current : C.State input.active input.passive} {header : Header}

abbrev gatewayBefore (report : Report input events) := beforeService input report.final .primary

structure Current (base : Report input baseEvents)
    (profile : CampusTCPStartupNative.Profile (input.contextFor .primary) (beforeService input base.final .primary) input.zone header)
    (report : Report input events) (current : C.State input.active input.passive) : Prop where
  connected : report.final.connection = .recovering current
  cold : CampusTCPRecoveryStartupCold.ColdProfile report
  primary : PrimaryServices report
  environment : (beforeService input base.final .primary).environment = (gatewayBefore report).environment
  entry : EntryMatches profile.entry (gatewayBefore report).admission
  coordinates : Coordinates input.active input.passive (gatewayBefore report).admission.phase
  fresh : (gatewayBefore report).admission.phase = .empty → ConntrackLifecycle.FreshKeys (gatewayBefore report).tracker profile.entry
  trackerValid : (gatewayBefore report).tracker.Valid
  headers : ∀ output ∈ current.emissions, output.packet.packet.header = profile.entry.flow.input (sideDirection output.actor)

variable {profile : CampusTCPStartupNative.Profile (input.contextFor .primary) (beforeService input base.final .primary) input.zone header}

theorem of_open (history : History base report)
    (profile : CampusTCPStartupNative.Profile (input.contextFor .primary) (beforeService input base.final .primary)
      input.zone (Handshake.outbound input.active remote))
    (cold : CampusTCPRecoveryStartupCold.ColdProfile report) (connected : report.final.connection = .recovering current)
    (primary : PrimaryServices report) (actual : Step input) (member : actual ∈ report.steps)
    (idle : actual.before.connection = .startup .idle pending) (event : actual.event = .openRecovering remote policy) :
    Current base profile report current := by
  obtain ⟨opened⟩ := CampusTCPRecoveryStartupOpened.Step.opened actual idle event
  obtain ⟨opening⟩ := opened.source_at report member
  have reachable := CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connected
  have matching := history.entry_matches profile cold connected opening rfl opened.source_header
  refine ⟨connected, cold, primary,
    CampusTCPRoundEnvironment.Trace.service_environment history.trace history.transport .primary,
    matching, CampusTCPRecoveryStartupCurrentCoordinates.History.coordinates history profile cold connected primary opening rfl opened.source_header,
    CampusTCPRecoveryStartupEmptyTracker.History.fresh_keys history profile,
    report.final.primary.history.tracker_valid, ?_⟩
  intro output inside
  cases actor : output.actor with
  | active =>
    have same := reachable.packet_inventory.same_header inside (opening.recovering_member connected) actor
    exact same.trans (opened.source_header.trans profile.original.symm)
  | passive =>
    exact CampusTCPRecoveryStartupCurrentHeaders.Report.passive_header report connected primary matching inside actor

private theorem phase_empty {phase : Admission.Phase} (absent : phase.entry = none) : phase = .empty := by
  cases phase <;> first | rfl | cases absent

private theorem Current.source_service_enabled (value : Current base profile report current)
    (source : CampusTCPStartupJobs.Source input) (origin : CampusTCPRecoveryStartupCurrentSources.ProducedAt report source) :
    ∃ evidence emission,
      CampusTCPService.run (input.contextFor .primary) (gatewayBefore report) source.produced.source input.zone
        (profile.paths (sideDirection source.occurrence.actor)).ingress 100000 .startupRecovery = .ok evidence ∧
      evidence.output = some emission ∧ evidence.passed = true ∧
      emission.target = profile.entry.flow.output (sideDirection source.occurrence.actor) := by
  let wire := source.produced.source
  let direction := sideDirection source.occurrence.actor
  have reachable := CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report value.connected
  have inside := origin.recovering_member value.connected
  have shape : TCPHandshakeRecovery.PacketShape input.active input.passive source.occurrence.actor source.occurrence.kind wire.asInput :=
    reachable.output_shape inside
  have ttl : 1 < wire.packet.ip.packet.ttl.toNat := reachable.output_ttl inside
  have wireHeader : wire.packet.header = profile.entry.flow.input direction := value.headers source.occurrence inside
  have floor := CampusTCPRecoveryStartupCurrentFloors.Report.output_gateway_floor report value.connected value.primary inside
  change CampusTCPRecoveryStartupCurrentFloors.requiredLevel source.occurrence.kind ≤
    CampusTCPRecoveryStartupTransport.phaseRank (gatewayBefore report).admission.phase at floor
  cases selected : (gatewayBefore report).admission.phase.entry with
  | none =>
    have empty := phase_empty selected
    have kind : source.occurrence.kind = .syn := by
      rw [empty] at floor
      cases same : source.occurrence.kind <;> simp only [same, CampusTCPRecoveryStartupCurrentFloors.requiredLevel,
        CampusTCPRecoveryStartupTransport.phaseRank] at floor
      · rfl
      all_goals omega
    rw [kind] at shape
    have directionEq : direction = .original := by
      simp only [direction, shape.actorEq, TCPHandshakeRecovery.Kind.actor, sideDirection]
    have sourceHeader : wire.packet.header = header := by
      rw [directionEq] at wireHeader
      exact wireHeader.trans profile.original
    have synProfile : Admission.Startup wire.packet.segment 2 := by
      refine ⟨shape.profile.1, ?_, shape.payload⟩
      change (MSS.readStartup wire.asInput.packet.segment.options).isOk = true
      rw [shape.options, TCPHandshakeRecovery.Kind.options, Handshake.options_selected]
      rfl
    have ready := profile.fresh_ready value.environment wire sourceHeader value.trackerValid (value.fresh empty) empty synProfile ttl
    have selectedDirection : sideDirection source.occurrence.actor = .original := directionEq
    rw [selectedDirection]
    obtain ⟨evidence, emission, computed, emitted, passed, target, _, _⟩ :=
      CampusTCPService.run_fresh_syn_enabled _ _ _ _ _ _ _ ready .startupRecovery
    exact ⟨evidence, emission, computed, emitted, passed, target⟩
  | some selectedEntry =>
    have entryEq := value.entry selectedEntry selected
    have selectedProfile : (gatewayBefore report).admission.phase.entry = some profile.entry := selected.trans (congrArg some entryEq)
    obtain ⟨record, member, recordEntry⟩ := CampusTCPRecoveryStartupTransport.Report.tracker_linked report value.primary profile.entry selectedProfile
    have allowed : ∀ other ∈ (gatewayBefore report).tracker.records, other.entry.flow = profile.entry.flow →
        CampusTCPService.X.Allowed .startupRecovery (gatewayBefore report).admission.phase
          (ConntrackLifecycle.selectedAttachment other direction) wire.packet.segment (gatewayBefore report).admission.observations := by
      intro other stored flow
      have exactEntry := profile.binding value.trackerValid record member recordEntry other stored flow
      apply CampusTCPRecoveryStartupAdmissionGuards.existing_allowed value.coordinates shape selectedProfile exactEntry rfl rfl floor
      · intro syn
        exact CampusTCPRecoveryStartupControlLedger.Report.known_syn report value.cold value.primary value.connected selectedProfile inside syn
      · intro synAck level
        exact CampusTCPRecoveryStartupControlLedger.Report.known_synAck report value.cold value.primary value.connected selectedProfile level inside synAck
    have ready := profile.existing_admission_ready value.environment wire direction wireHeader value.trackerValid record member recordEntry allowed ttl
    obtain ⟨evidence, emission, computed, emitted, passed, target, _, _⟩ :=
      CampusTCPService.run_existing_admission_enabled _ _ _ _ _ _ _ ready
    exact ⟨evidence, emission, computed, emitted, passed, target⟩

theorem Current.job_service_enabled (value : Current base profile report current)
    (job : CampusTCPStartupJobs.Job input) (pending : job.Pending report.final) :
    ∃ evidence emission,
      CampusTCPService.run (input.contextFor .primary) (gatewayBefore report) job.source.produced.source input.zone
        (profile.paths (sideDirection job.source.occurrence.actor)).ingress 100000 .startupRecovery = .ok evidence ∧
      evidence.output = some emission ∧ evidence.passed = true ∧
      emission.target = profile.entry.flow.output (sideDirection job.source.occurrence.actor) := by
  obtain ⟨source⟩ := CampusTCPRecoveryStartupCurrentSources.Job.source_at report job pending
  exact Current.source_service_enabled value job.source source

end Netlib.Check.CampusTCPRecoveryStartupCurrentNative
