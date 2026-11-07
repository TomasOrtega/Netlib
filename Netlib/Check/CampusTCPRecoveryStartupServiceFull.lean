import Netlib.Check.CampusTCPRecoveryStartupCurrentNative

/-!
# The actual native startup service route

The enabling result retains its processing and current native next hop.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupServiceFull

open Packet Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupCurrentNative (Current gatewayBefore)
open CampusTCPRecoveryStartupPhase (sideDirection)

variable {input : Input} {baseEvents events : List CampusTCPModel.Event}
variable {base : Report input baseEvents} {report : Report input events}
variable {current : C.State input.active input.passive} {header : Header}
variable {profile : CampusTCPStartupNative.Profile (input.contextFor .primary) (beforeService input base.final .primary) input.zone header}

private theorem phase_empty {phase : Admission.Phase} (absent : phase.entry = none) : phase = .empty := by
  cases phase <;> first | rfl | cases absent

private theorem source_service_full_enabled (value : Current base profile report current)
    (source : CampusTCPStartupJobs.Source input) (origin : CampusTCPRecoveryStartupCurrentSources.ProducedAt report source) :
    ∃ evidence emission,
      CampusTCPService.run (input.contextFor .primary) (gatewayBefore report) source.produced.source input.zone
        (profile.paths (sideDirection source.occurrence.actor)).ingress 100000 .startupRecovery = .ok evidence ∧
      evidence.output = some emission ∧ evidence.passed = true ∧
      emission.target = profile.entry.flow.output (sideDirection source.occurrence.actor) ∧
      ∃ processing, evidence.processing = some processing ∧
        processing.outcome.nextHop = some (profile.paths (sideDirection source.occurrence.actor)).hop := by
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
    obtain ⟨evidence, emission, computed, emitted, passed, target, _, processing, processingAt, nextHop⟩ :=
      CampusTCPService.run_fresh_syn_enabled _ _ _ _ _ _ _ ready .startupRecovery
    exact ⟨evidence, emission, computed, emitted, passed, target, processing, processingAt, nextHop⟩
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
    obtain ⟨evidence, emission, computed, emitted, passed, target, _, processing, processingAt, nextHop⟩ :=
      CampusTCPService.run_existing_admission_enabled _ _ _ _ _ _ _ ready
    exact ⟨evidence, emission, computed, emitted, passed, target, processing, processingAt, nextHop⟩

theorem Current.job_service_full_enabled (value : Current base profile report current)
    (job : CampusTCPStartupJobs.Job input) (pending : job.Pending report.final) :
    ∃ evidence emission,
      CampusTCPService.run (input.contextFor .primary) (gatewayBefore report) job.source.produced.source input.zone
        (profile.paths (sideDirection job.source.occurrence.actor)).ingress 100000 .startupRecovery = .ok evidence ∧
      evidence.output = some emission ∧ evidence.passed = true ∧
      emission.target = profile.entry.flow.output (sideDirection job.source.occurrence.actor) ∧
      ∃ processing, evidence.processing = some processing ∧
        processing.outcome.nextHop = some (profile.paths (sideDirection job.source.occurrence.actor)).hop := by
  obtain ⟨source⟩ := CampusTCPRecoveryStartupCurrentSources.Job.source_at report job pending
  exact source_service_full_enabled value job.source source


end Netlib.Check.CampusTCPRecoveryStartupServiceFull
