import Netlib.Check.CampusTCPTwoProgressStart
import Netlib.Check.CampusTCPGapProgressGateway

/-!
# Current gateway evidence for two TCP records

Fresh admissions can add ranges to the selected lane.
Each retained range has a source in the actual gateway history.
-/

namespace Netlib.Check.CampusTCPTwoProgressGateway

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {anchor cut next : Cut input complete} {basis : StartupBasis anchor} {gateway : Gateway}

structure Current (start : GatewayStart anchor basis gateway) (cut : Cut input complete) where
  session : Admission.Session
  phase : (beforeService input cut.report.final gateway).admission.phase = .data session
  identity : Identity start.session session
  observations : (beforeService input anchor.report.final gateway).admission.observations <+:
    (beforeService input cut.report.final gateway).admission.observations
  trackerValid : (beforeService input cut.report.final gateway).tracker.Valid
  record : ConntrackLifecycle.Record
  member : record ∈ (beforeService input cut.report.final gateway).tracker.records
  entry : record.entry = session.entry
  confirmed : record.seenReply = true

variable {start : GatewayStart anchor basis gateway}

def Current.ofStart (start : GatewayStart anchor basis gateway) : Current start anchor :=
  ⟨start.session, start.phase, CampusTCPGapProgressStart.Identity.refl _, List.prefix_refl _, start.trackerValid,
    start.record, start.member, start.entry, start.confirmed⟩

def Current.reframe (current : Current start cut)
    (same : beforeService input next.report.final gateway = beforeService input cut.report.final gateway) :
    Current start next :=
  ⟨current.session, by rw [same]; exact current.phase, current.identity,
    by rw [same]; exact current.observations, by rw [same]; exact current.trackerValid,
    current.record, by rw [same]; exact current.member, current.entry, current.confirmed⟩

theorem Current.coverage_sources (_current : Current start cut) :
    (beforeService input cut.report.final gateway).admission.CoverageSources :=
  (cut.report.final.resident gateway).history.coverage_sources

def Current.source (current : Current start cut) (direction : Admission.Direction)
    (run : Admission.Coverage.Run Nat) (member : run ∈ (current.session.lane direction).coverage.runs) :
    Admission.CoverageSource (beforeService input cut.report.final gateway).admission.observations
      current.session.entry direction (current.session.lane direction) run :=
  (current.session.lane direction).coverageSource _ _ _
    (Admission.State.coverage_sources_lane _ current.coverage_sources current.session current.phase direction) run member

def Current.origin (current : Current start cut) (direction : Admission.Direction)
    (run : Admission.Coverage.Run Nat) (member : run ∈ (current.session.lane direction).coverage.runs) :
    Checkpoint.CoverageOrigin (cut.report.final.resident gateway).history current.session direction run :=
  (cut.report.final.resident gateway).history.coverageOrigin current.session current.phase direction run member

theorem Current.known_of_slice (current : Current start cut) (direction : Admission.Direction)
    (segment : Segment) (run : Admission.Coverage.Run Nat)
    (member : run ∈ (current.session.lane direction).coverage.runs)
    (nonempty : segment.payload ≠ []) (offset : Nat)
    (slice : Theory.SparseCoverage.Slice run (Seq.distance (current.session.lane direction).base segment.sequence)
      segment.payload offset) :
    Admission.KnownRange (current.session.lane direction) current.session.entry direction segment
      (beforeService input cut.report.final gateway).admission.observations := by
  have valid : (current.session.lane direction).Valid := by
    cases direction
    · exact current.session.originalValid
    · exact current.session.replyValid
  obtain ⟨placed, accepted, _, sourceEq, _, novel⟩ := CampusTCPGapProgressGateway.accept_slice_exists
    (current.session.lane direction).coverage run _ segment.payload
    (beforeService input cut.report.final gateway).admission.observations.length Admission.coverageBound offset
    valid.2.2.2 member nonempty slice
  let source := current.source direction run member
  have seenNonempty : source.seen.segment.payload ≠ [] := by
    rw [← source.evidence.bytes]
    exact (valid.2.2.2.2.1 run member).1
  have profile := CampusTCPGapProgressGateway.history_nonempty_profile
    (cut.report.final.resident gateway).history run.metadata source.seen source.evidence.selected seenNonempty
  have highEnd := (current.session.lane direction).coverage.limit_le_highEnd run member
  have coordinates := slice.1
  have bounded := slice.2.1
  have bytes := slice.2.2
  have difference : Seq.distance (current.session.lane direction).base segment.sequence - run.position = offset := by omega
  unfold Admission.KnownRange Admission.placement
  rw [accepted]
  dsimp only
  rw [sourceEq, source.evidence.selected]
  refine ⟨novel, source.evidence.entry, source.evidence.direction, profile, seenNonempty, ?_, ?_, ?_, ?_⟩
  · rw [← source.evidence.position]
    omega
  · rw [← source.evidence.position, ← source.evidence.bytes]
    omega
  · rw [← source.evidence.position, ← source.evidence.bytes]
    exact highEnd
  · rw [← source.evidence.position, ← source.evidence.bytes, difference]
    exact bytes.symm

private theorem record_eq (record : ConntrackLifecycle.Record) (entry : NetfilterNAT.Entry)
    (same : record.entry = entry) (confirmed : record.seenReply = true) : record = ⟨entry, true⟩ := by
  cases record
  cases same
  cases confirmed
  rfl

theorem Current.binding (current : Current start cut) (record : ConntrackLifecycle.Record)
    (member : record ∈ (beforeService input cut.report.final gateway).tracker.records)
    (same : record.entry.flow = current.session.entry.flow) : record.entry = current.session.entry := by
  have equal := CampusTCPGapProgressGateway.tracker_record_unique _ current.trackerValid member current.member
    (same.trans (congrArg NetfilterNAT.Entry.flow current.entry).symm)
  exact (congrArg ConntrackLifecycle.Record.entry equal).trans current.entry

theorem Current.confirmed_binding (current : Current start cut) (record : ConntrackLifecycle.Record)
    (member : record ∈ (beforeService input cut.report.final gateway).tracker.records)
    (same : record.entry.flow = current.session.entry.flow) : record = ⟨current.session.entry, true⟩ := by
  have equal := CampusTCPGapProgressGateway.tracker_record_unique _ current.trackerValid member current.member
    (same.trans (congrArg NetfilterNAT.Entry.flow current.entry).symm)
  exact equal.trans (record_eq current.record current.session.entry current.entry current.confirmed)

theorem Current.lookup (current : Current start cut) (direction : Admission.Direction) :
    (beforeService input cut.report.final gateway).tracker.model.lookup
      (current.session.entry.flow.zone direction) (current.session.entry.flow.input direction) =
      some ⟨current.session.entry.flow, direction⟩ := by
  have member : current.session.entry.flow ∈ (beforeService input cut.report.final gateway).tracker.model.entries :=
    List.mem_map.mpr ⟨current.record, current.member, congrArg NetfilterNAT.Entry.flow current.entry⟩
  simpa only [FlowNAT.Hit.key, FlowNAT.Entry.key] using FlowNAT.Snapshot.lookup_complete _
    current.trackerValid.1 ⟨current.session.entry.flow, direction⟩ member

theorem Current.tracker_ready (current : Current start cut)
    (native : CampusTCPRoundGateway.Native context initial ingress start.session.entry direction hop)
    (same : initial.environment = (beforeService input cut.report.final gateway).environment)
    (source : WireForwarding.Source) (zone : Nat)
    (header : source.packet.header = current.session.entry.flow.input direction)
    (zoneEq : current.session.entry.flow.zone direction = zone) :
    ConntrackLifecycle.ExistingReady
      ((beforeService input cut.report.final gateway).configuration.pipeline context.routing)
      (beforeService input cut.report.final gateway).tracker
      (CampusTCPService.packetInput (beforeService input cut.report.final gateway) source zone).lifecycle
      ⟨current.session.entry.flow, direction⟩ hop := by
  have configuration := congrArg CampusTCPService.Before.Environment.configuration same
  change initial.configuration = (beforeService input cut.report.final gateway).configuration at configuration
  have found : (beforeService input cut.report.final gateway).tracker.model.lookup zone source.packet.header =
      some ⟨current.session.entry.flow, direction⟩ := by
    rw [header, ← zoneEq]
    exact current.lookup direction
  refine ⟨current.trackerValid, ?_, ?_, ?_, found, ?_⟩
  · have compatible := current.trackerValid.2 current.record current.member
    rw [current.entry] at compatible
    simp only [CampusTCPService.packetInput, TCP.WireForwarding.Input.lifecycle]
    rw [← zoneEq]
    cases direction
    · exact compatible.1.2.2.1
    · exact compatible.1.2.2.2.1
  · have tcp : source.packet.header.protocol = Packet.Protocol.tcp := by simp only [DecodedIPv4.header]
    simp only [CampusTCPService.packetInput, TCP.WireForwarding.Input.lifecycle, Conntrack.transport, tcp, true_or, decide_true]
  · change (if ((beforeService input cut.report.final gateway).tracker.model.lookup zone source.packet.header).isNone then _ else none) = none
    rw [found]
    rfl
  · intro record member bound
    rw [current.confirmed_binding record member bound]
    change ConntrackLifecycle.ForwardConditions
      ((beforeService input cut.report.final gateway).configuration.pipeline context.routing)
      source.packet.header (ConntrackLifecycle.selectedAttachment ⟨current.session.entry, true⟩ direction) hop
    rw [← configuration, header, current.identity.entry]
    exact native.forwarding

def Current.existing_ready (current : Current start cut)
    (native : CampusTCPRoundGateway.Native context initial ingress start.session.entry direction hop)
    (same : initial.environment = (beforeService input cut.report.final gateway).environment)
    (source : WireForwarding.Source) (zone : Nat)
    (header : source.packet.header = current.session.entry.flow.input direction)
    (zoneEq : current.session.entry.flow.zone direction = zone)
    (data : Admission.DataReady current.session direction source.packet.segment)
    (ttl : 1 < source.packet.ip.packet.ttl.toNat) :
    CampusTCPService.ExistingDataReady context (beforeService input cut.report.final gateway) source zone ingress
      ⟨current.session.entry.flow, direction⟩ current.session hop := by
  let checks := native.checks.reframe _ same
  have guard := congrArg CampusTCPService.Before.Environment.guard same
  change initial.guard = (beforeService input cut.report.final gateway).guard at guard
  refine ⟨checks, (CampusTCPService.Checks.reframe_budget _ _ same).trans native.budget,
    ?_, current.tracker_ready native same source zone header zoneEq, current.phase,
    current.binding, data, ttl,
    (CampusTCPService.Checks.reframe_forward_passed _ _ same).trans native.forwardComparison,
    (CampusTCPService.Checks.reframe_guard_passed _ _ same).trans native.guardComparison, ?_⟩
  · rw [← guard, header, current.identity.entry]
    exact native.ingressPermit
  · simp only [CampusTCPService.coverage, header, current.identity.entry]
    exact native.covered

def Current.repeated_ready (current : Current start cut)
    (native : CampusTCPRoundGateway.Native context initial ingress start.session.entry direction hop)
    (same : initial.environment = (beforeService input cut.report.final gateway).environment)
    (source : WireForwarding.Source) (zone : Nat)
    (header : source.packet.header = current.session.entry.flow.input direction)
    (zoneEq : current.session.entry.flow.zone direction = zone)
    (data : Admission.RepeatedReady current.session direction source.packet.segment
      (beforeService input cut.report.final gateway).admission.observations)
    (ttl : 1 < source.packet.ip.packet.ttl.toNat) :
    CampusTCPService.ExistingRepeatedReady context (beforeService input cut.report.final gateway) source zone ingress
      ⟨current.session.entry.flow, direction⟩ current.session hop := by
  let checks := native.checks.reframe _ same
  have guard := congrArg CampusTCPService.Before.Environment.guard same
  change initial.guard = (beforeService input cut.report.final gateway).guard at guard
  refine ⟨checks, (CampusTCPService.Checks.reframe_budget _ _ same).trans native.budget,
    ?_, current.tracker_ready native same source zone header zoneEq, current.phase,
    current.binding, data, ttl,
    (CampusTCPService.Checks.reframe_forward_passed _ _ same).trans native.forwardComparison,
    (CampusTCPService.Checks.reframe_guard_passed _ _ same).trans native.guardComparison, ?_⟩
  · rw [← guard, header, current.identity.entry]
    exact native.ingressPermit
  · simp only [CampusTCPService.coverage, header, current.identity.entry]
    exact native.covered

theorem lane_highEnd_lt_modulus (lane : Admission.Lane) (valid : lane.Valid) : lane.highEnd < Seq.modulus := by
  have epoch := valid.2.1
  unfold Seq.halfSpace Seq.modulus at *
  omega

theorem lane_observed_lt_modulus (lane : Admission.Lane) (valid : lane.Valid) : lane.observed < Seq.modulus := by
  have bound := lane.coverage.frontier_le_highEnd
  change lane.observed ≤ lane.highEnd at bound
  exact Nat.lt_of_le_of_lt bound (lane_highEnd_lt_modulus lane valid)

theorem ack_offset_add (session : Admission.Session) (direction : Admission.Direction)
    (segment : Segment) (count : Nat) (within : count ≤ (session.peer direction).observed)
    (ack : segment.acknowledgment = (session.peer direction).base.add count) :
    Admission.ackOffset (session.peer direction) segment = count := by
  have bounded := Nat.lt_of_le_of_lt within (lane_observed_lt_modulus _ (session.peer_valid direction))
  rw [Admission.ackOffset, ack, Seq.distance_add, Nat.mod_eq_of_lt bounded]

theorem Current.ack_ready (current : Current start cut) (direction : Admission.Direction)
    (segment : Segment) (position count : Nat) (profile : Admission.DataProfile segment)
    (empty : segment.payload = [])
    (sequence : segment.sequence = (current.session.sender direction).base.add position)
    (positionBound : position ≤ (current.session.sender direction).highEnd)
    (ack : segment.acknowledgment = (current.session.peer direction).base.add count)
    (countBound : count ≤ (current.session.peer direction).observed)
    (stale : (current.session.peer direction).acknowledged ≤ count + 65535) :
    Admission.AckReady current.session direction segment := by
  have bounded := Nat.lt_of_le_of_lt positionBound
    (lane_highEnd_lt_modulus _ (current.session.sender_valid direction))
  have offset := ack_offset_add current.session direction segment count countBound ack
  refine ⟨profile, empty, ?_, ?_, ?_⟩
  · rw [sequence, Seq.distance_add, Nat.mod_eq_of_lt bounded]
    exact positionBound
  · rw [offset]
    exact countBound
  · rw [offset]
    exact stale

private theorem map_fixed (function : α → α) (values : List α)
    (fixed : ∀ value ∈ values, function value = value) : values.map function = values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    rw [List.map_cons, fixed head List.mem_cons_self, ih (fun value member => fixed value (List.mem_cons_of_mem _ member))]

private theorem markReply_fixed (state : ConntrackLifecycle.State) (flow : FlowNAT.Entry)
    (confirmed : ∀ record ∈ state.records, record.entry.flow = flow → record.seenReply = true) :
    state.markReply flow = state := by
  have unchanged : state.records.map (ConntrackLifecycle.State.markRecord flow) = state.records := by
    apply map_fixed
    intro record member
    unfold ConntrackLifecycle.State.markRecord
    split
    · rename_i same
      have marked := confirmed record member same
      cases record
      simp_all only
    · rfl
  cases state
  exact congrArg ConntrackLifecycle.State.mk unchanged

variable {source : WireForwarding.Source} {mode : AdmissionExecution.Mode}

private theorem execution_identity (result : AdmissionExecution.Result mode before packet lifecycle prepared)
    (phase : before.phase = .data session) :
    ∃ after, (AdmissionExecution.state result).phase = .data after ∧ Identity session after := by
  rcases AdmissionExecution.Result.legacy_or_stutter result with legacy | ⟨recovery, stutter⟩
  · obtain ⟨after, afterPhase, identity⟩ :=
      CampusTCPGapProgressGateway.result_identity (AdmissionExecution.Result.asLegacy result legacy) phase
    have same := congrArg Admission.State.phase (AdmissionExecution.Result.asLegacy_state result legacy)
    exact ⟨after, same.symm.trans afterPhase, identity⟩
  · subst mode
    refine ⟨session, ?_, CampusTCPGapProgressStart.Identity.refl _⟩
    exact (AdmissionStartupRecovery.Result.phase result).trans
      ((AdmissionStartupRecovery.nextPhase_stutter stutter result.admitted).trans phase)

theorem Current.processing_tracker (current : Current start cut)
    (processing : CampusTCPService.Processing context (beforeService input cut.report.final gateway) source zone mode) :
    processing.outcome.state = (beforeService input cut.report.final gateway).tracker := by
  have attached : processing.prepared.attachment.entry = current.session.entry := by
    rcases AdmissionExecution.Result.legacy_or_stutter processing.admitted with legacy | ⟨_, stutter⟩
    · rw [current.phase] at legacy
      exact legacy.1
    · have selected := stutter.entry
      rw [current.phase] at selected
      exact (Option.some.inj selected).symm
  have existing := CampusTCPRoundAdmission.Processing.existing_data processing current.session current.phase
  rw [processing.existing_state existing]
  cases direction : processing.prepared.attachment.direction with
  | original =>
    obtain ⟨_, _, _, _, unchanged⟩ := ConntrackLifecycle.prepare_existing_original _ _ processing.prepared
      processing.attached existing direction
    exact unchanged
  | reply =>
    have changed := ConntrackLifecycle.prepare_reply _ _ processing.prepared processing.attached direction
    rw [changed.2.2, attached]
    apply markReply_fixed
    intro record member same
    rw [current.confirmed_binding record member same]

theorem Current.processing_fields (current : Current start cut)
    (processing : CampusTCPService.Processing context (beforeService input cut.report.final gateway) source zone mode) :
    ∃ after, processing.nextAdmission.phase = .data after ∧ Identity start.session after ∧
      processing.nextAdmission.observations = (beforeService input cut.report.final gateway).admission.observations ++
        [Admission.observe source.asInput
          (CampusTCPService.packetInput (beforeService input cut.report.final gateway) source zone).lifecycle
          processing.prepared] ∧
      processing.outcome.state = (beforeService input cut.report.final gateway).tracker := by
  obtain ⟨after, phase, identity⟩ := execution_identity processing.admitted current.phase
  rw [CampusTCPRoundAdmission.Processing.committed_data processing current.session current.phase]
  exact ⟨after, phase, current.identity.trans identity, AdmissionExecution.Result.ledger processing.admitted, current.processing_tracker processing⟩

theorem Current.after_processing (current : Current start cut)
    (processing : CampusTCPService.Processing context (beforeService input cut.report.final gateway) source zone mode)
    (admission : (beforeService input next.report.final gateway).admission = processing.nextAdmission)
    (tracker : (beforeService input next.report.final gateway).tracker = processing.outcome.state) :
    Nonempty (Current start next) := by
  obtain ⟨after, phase, identity, observed, unchanged⟩ := current.processing_fields processing
  refine ⟨⟨after, ?_, identity, ?_, ?_, current.record, ?_, ?_, current.confirmed⟩⟩
  · rw [admission]
    exact phase
  · rw [admission, observed]
    exact current.observations.trans (List.prefix_append _ _)
  · rw [tracker]
    exact processing.outcome.valid
  · rw [tracker, unchanged]
    exact current.member
  · exact current.entry.trans (current.identity.entry.trans identity.entry.symm)

end Netlib.Check.CampusTCPTwoProgressGateway
