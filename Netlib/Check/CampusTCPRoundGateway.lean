import Netlib.Check.CampusTCPStartupAlignment
import Netlib.Check.CampusTCPRoundAdmission
import Netlib.Check.CampusTCPRoundEnvironment
import Netlib.Check.CampusTCPServiceEnabled

/-!
# Gateway guards in one lossless TCP round

Initial policy and ingress checks apply to the fixed NAT headers.
The actual tracker and admission state supply the packet guards.
-/

namespace Netlib.Check.CampusTCPRoundGateway

open Packet Protocol

namespace A
export TCP.Admission (Session DataProfile DataReady)
end A

structure Native (context : CampusTCPService.Context) (initial : CampusTCPService.Before)
    (ingress : CampusTCPService.I.InterfaceRef) (entry : NetfilterNAT.Entry)
    (direction : FlowNAT.Direction) (hop : String) where
  checks : CampusTCPService.Checks context initial ingress
  budget : checks.budget = 100000
  forwardComparison : checks.forward.passed = true
  guardComparison : checks.guard.passed = true
  ingressPermit : initial.guard.permits ingress.ifindex.val (entry.flow.input direction) = true
  forwarding : ConntrackLifecycle.ForwardConditions (initial.configuration.pipeline context.routing)
    (entry.flow.input direction) (ConntrackLifecycle.selectedAttachment ⟨entry, true⟩ direction) hop
  covered : context.application.any (·.accepts (entry.flow.input direction)) = true

theorem singleton_lookup (tracker : ConntrackLifecycle.State) (entry : NetfilterNAT.Entry)
    (valid : tracker.Valid) (records : tracker.records = [⟨entry, true⟩]) (direction : FlowNAT.Direction) :
    tracker.model.lookup (entry.flow.zone direction) (entry.flow.input direction) = some ⟨entry.flow, direction⟩ := by
  have member : entry.flow ∈ tracker.model.entries := by
    simp only [ConntrackLifecycle.State.model, records, List.map_cons, List.map_nil, List.mem_singleton]
  exact FlowNAT.Snapshot.lookup_complete tracker.model valid.1 ⟨entry.flow, direction⟩ member

theorem singleton_zone (tracker : ConntrackLifecycle.State) (entry : NetfilterNAT.Entry)
    (valid : tracker.Valid) (records : tracker.records = [⟨entry, true⟩]) (direction : FlowNAT.Direction) :
    entry.flow.zone direction < 65536 := by
  have member : (⟨entry, true⟩ : ConntrackLifecycle.Record) ∈ tracker.records := by rw [records]; simp
  have compatible := valid.2 _ member
  cases direction
  · exact compatible.1.2.2.1
  · exact compatible.1.2.2.2.1

def existing_ready
    (native : Native context initial ingress entry direction hop) (current : CampusTCPService.Before)
    (same : initial.environment = current.environment) (source : TCP.WireForwarding.Source) (zone : Nat)
    (header : source.packet.header = entry.flow.input direction) (zoneEq : entry.flow.zone direction = zone)
    (valid : current.tracker.Valid) (records : current.tracker.records = [⟨entry, true⟩])
    (session : TCP.Admission.Session) (entryEq : session.entry = entry)
    (phase : current.admission.phase = .data session)
    (data : TCP.Admission.DataReady session direction source.packet.segment)
    (ttl : 1 < source.packet.ip.packet.ttl.toNat) :
    CampusTCPService.ExistingDataReady context current source zone ingress ⟨entry.flow, direction⟩ session hop := by
  let checks := native.checks.reframe current same
  have configuration := congrArg CampusTCPService.Before.Environment.configuration same
  have guard := congrArg CampusTCPService.Before.Environment.guard same
  change initial.configuration = current.configuration at configuration
  change initial.guard = current.guard at guard
  have found : current.tracker.model.lookup zone source.packet.header = some ⟨entry.flow, direction⟩ := by
    simpa only [zoneEq, header] using singleton_lookup current.tracker entry valid records direction
  refine ⟨checks, ?_, ?_, ?_, phase, ?_, data, ttl, ?_, ?_, ?_⟩
  · exact (CampusTCPService.Checks.reframe_budget _ _ same).trans native.budget
  · rw [← guard, header]
    exact native.ingressPermit
  · refine ⟨valid, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [CampusTCPService.packetInput, TCP.WireForwarding.Input.lifecycle, ← zoneEq] using
        singleton_zone current.tracker entry valid records direction
    · have tcp : source.packet.header.protocol = Packet.Protocol.tcp := by
        simp only [TCP.DecodedIPv4.header]
      simp only [CampusTCPService.packetInput, TCP.WireForwarding.Input.lifecycle, Conntrack.transport, tcp,
        true_or, decide_true]
    · change (if (current.tracker.model.lookup zone source.packet.header).isNone then _ else none) = none
      rw [found]
      rfl
    · exact found
    · intro record member _
      simp only [records, List.mem_singleton] at member
      subst record
      change ConntrackLifecycle.ForwardConditions (current.configuration.pipeline context.routing)
        source.packet.header (ConntrackLifecycle.selectedAttachment ⟨entry, true⟩ direction) hop
      rw [← configuration, header]
      exact native.forwarding
  · intro record member _
    simp only [records, List.mem_singleton] at member
    subst record
    exact entryEq.symm
  · exact (CampusTCPService.Checks.reframe_forward_passed _ _ same).trans native.forwardComparison
  · exact (CampusTCPService.Checks.reframe_guard_passed _ _ same).trans native.guardComparison
  · simp only [CampusTCPService.coverage, header]
    exact native.covered

def original_ready
    (input : CampusTCPModel.Input) (complete : TCPHandshake.Completed input.active input.passive)
    (aligned : CampusTCPStartupAlignment.Alignment input complete entry session)
    (native : Native context initial ingress entry .original hop) (current : CampusTCPService.Before)
    (same : initial.environment = current.environment) (source : TCP.WireForwarding.Source)
    (header : source.packet.header = TCP.Output.reverse complete.certificate.activeSeed.core.inbound)
    (valid : current.tracker.Valid) (records : current.tracker.records = [⟨entry, true⟩])
    (phase : current.admission.phase = .data session)
    (sequence : source.packet.segment.sequence = input.active.iss.add 1)
    (acknowledgment : source.packet.segment.acknowledgment = input.passive.iss.add 1)
    (profile : TCP.Admission.DataProfile source.packet.segment) (nonempty : source.packet.segment.payload ≠ [])
    (mss : source.packet.segment.payload.length ≤ (TCP.Handshake.receiveOffer input.passive).limit)
    (window : source.packet.segment.payload.length ≤ input.passive.capacity)
    (epoch : source.packet.segment.payload.length + 2 < TCP.Seq.halfSpace)
    (ttl : 1 < source.packet.ip.packet.ttl.toNat) :
    CampusTCPService.ExistingDataReady context current source input.zone ingress ⟨entry.flow, .original⟩ session hop := by
  have ready := CampusTCPRoundAdmission.initial_fresh_ready session source.packet.segment
    aligned.originalCoverage aligned.originalAcknowledged aligned.replyCoverage aligned.replyAcknowledged
    (sequence.trans aligned.originalBase.symm) (acknowledgment.trans aligned.replyBase.symm)
    profile nonempty (by simpa only [aligned.serverMSS] using mss)
    (by simpa only [aligned.originalWindow] using window) epoch
  exact existing_ready native current same source input.zone (header.trans aligned.clientInput) aligned.originalZone
    valid records session aligned.entryEq phase (.inl ready) ttl

def reply_ready
    (input : CampusTCPModel.Input) (complete : TCPHandshake.Completed input.active input.passive)
    (aligned : CampusTCPStartupAlignment.Alignment input complete entry initialSession)
    (geometry : CampusTCPRoundAdmission.DataGeometry initialSession session data sourceIndex)
    (native : Native context initial ingress entry .reply hop) (current : CampusTCPService.Before)
    (same : initial.environment = current.environment) (source : TCP.WireForwarding.Source)
    (header : source.packet.header = TCP.Output.reverse complete.certificate.passiveSeed.core.inbound)
    (valid : current.tracker.Valid) (records : current.tracker.records = [⟨entry, true⟩])
    (phase : current.admission.phase = .data session)
    (sequence : source.packet.segment.sequence = input.passive.iss.add 1)
    (acknowledgment : source.packet.segment.acknowledgment = (input.active.iss.add 1).add data.payload.length)
    (profile : TCP.Admission.DataProfile source.packet.segment) (empty : source.packet.segment.payload = [])
    (ttl : 1 < source.packet.ip.packet.ttl.toNat) :
    CampusTCPService.ExistingDataReady context current source input.zone ingress ⟨entry.flow, .reply⟩ session hop := by
  have ready := geometry.reply_ack_ready source.packet.segment profile empty
    (sequence.trans aligned.replyBase.symm) (by simpa only [aligned.originalBase] using acknowledgment)
  exact existing_ready native current same source input.zone (header.trans aligned.serverInput) aligned.replyZone
    valid records session (geometry.entry.trans aligned.entryEq) phase (.inr ready) ttl

theorem Processing.singleton_data_records (processing : CampusTCPService.Processing context before source zone mode)
    (session : TCP.Admission.Session) (phase : before.admission.phase = .data session)
    (records : before.tracker.records = [⟨entry, true⟩]) :
    processing.outcome.state.records = [⟨entry, true⟩] := by
  have existing := CampusTCPRoundAdmission.Processing.existing_data processing session phase
  rw [processing.existing_state existing]
  cases direction : processing.prepared.attachment.direction with
  | original =>
    obtain ⟨record, member, selected, classified, unchanged⟩ :=
      ConntrackLifecycle.prepare_existing_original _ _ processing.prepared processing.attached existing direction
    rw [unchanged, records]
  | reply =>
    have changed := ConntrackLifecycle.prepare_reply _ _ processing.prepared processing.attached direction
    rw [changed.2.2]
    simp only [ConntrackLifecycle.State.markReply, records, List.map_cons, List.map_nil]
    unfold ConntrackLifecycle.State.markRecord
    split <;> rfl

theorem Evidence.singleton_data_records
    (evidence : CampusTCPService.Evidence context before source zone ingress mode)
    (processing : CampusTCPService.Processing context before source zone mode)
    (present : evidence.processing = some processing) (session : TCP.Admission.Session)
    (phase : before.admission.phase = .data session) (records : before.tracker.records = [⟨entry, true⟩]) :
    evidence.tracker.Valid ∧ evidence.tracker.records = [⟨entry, true⟩] := by
  rw [(evidence.processing_states processing present).1]
  exact ⟨processing.outcome.valid, Processing.singleton_data_records processing session phase records⟩

end Netlib.Check.CampusTCPRoundGateway
