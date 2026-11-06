import Netlib.Check.CampusTCPRoundGateway
import Netlib.Protocol.TCP.AdmissionRepeatEnabled

/-!
# Gateway range state through timed retries

The first actual admission supplies the retained coverage source.
Later admission can repeat that range after a zero-window ACK.
-/

namespace Netlib.Check.CampusTCPRecoveryRoundGateway

open Packet Protocol
open CampusTCPRoundGateway (Native singleton_lookup singleton_zone)

def repeated_ready
    (native : Native context initial ingress entry direction hop) (current : CampusTCPService.Before)
    (same : initial.environment = current.environment) (source : TCP.WireForwarding.Source) (zone : Nat)
    (header : source.packet.header = entry.flow.input direction) (zoneEq : entry.flow.zone direction = zone)
    (valid : current.tracker.Valid) (records : current.tracker.records = [⟨entry, true⟩])
    (session : TCP.Admission.Session) (entryEq : session.entry = entry)
    (phase : current.admission.phase = .data session)
    (data : TCP.Admission.RepeatedReady session direction source.packet.segment current.admission.observations)
    (ttl : 1 < source.packet.ip.packet.ttl.toNat) :
    CampusTCPService.ExistingRepeatedReady context current source zone ingress ⟨entry.flow, direction⟩ session hop := by
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

open TCP.Admission

structure Geometry (initial current : TCP.Admission.Session) (bytes : List UInt8) (source : Nat) : Prop where
  entry : current.entry = initial.entry
  originalBase : current.original.base = initial.original.base
  originalCoverage : current.original.coverage = CampusTCPRoundAdmission.rangeCoverage bytes source
  replyBase : current.reply.base = initial.reply.base
  replyCoverage : current.reply.coverage = Coverage.initial
  clientMSS : current.clientMSS = initial.clientMSS
  serverMSS : current.serverMSS = initial.serverMSS

theorem Geometry.original_observed (geometry : Geometry initial current bytes source) :
    current.original.observed = bytes.length := by
  simp only [Lane.observed, geometry.originalCoverage, CampusTCPRoundAdmission.rangeCoverage,
    Theory.SparseCoverage.State.frontier, Theory.SparseCoverage.frontierFrom, ↓reduceIte,
    Theory.SparseCoverage.Run.limit, Nat.zero_add]

theorem Geometry.original_highEnd (geometry : Geometry initial current bytes source) :
    current.original.highEnd = bytes.length := by
  simp only [Lane.highEnd, geometry.originalCoverage, CampusTCPRoundAdmission.rangeCoverage,
    Theory.SparseCoverage.State.highEnd, Theory.SparseCoverage.highEnd, Theory.SparseCoverage.Run.limit,
    Nat.zero_add, Nat.max_zero]

theorem Geometry.reply_observed (geometry : Geometry initial current bytes source) :
    current.reply.observed = 0 := by
  simp only [Lane.observed, geometry.replyCoverage, Theory.SparseCoverage.initial,
    Theory.SparseCoverage.State.frontier, Theory.SparseCoverage.frontierFrom]

theorem Geometry.reply_acknowledged (geometry : Geometry initial current bytes source) :
    current.reply.acknowledged = 0 := by
  have valid := current.replyValid.1
  rw [geometry.reply_observed] at valid
  omega

theorem Geometry.ack_ready (geometry : Geometry initial current bytes source) (ack : TCP.Segment)
    (profile : DataProfile ack) (empty : ack.payload = [])
    (sequence : ack.sequence = initial.reply.base)
    (acknowledgment : ack.acknowledgment = initial.original.base.add bytes.length) :
    AckReady current .reply ack := by
  have epoch := current.originalValid.2.1
  rw [geometry.original_highEnd] at epoch
  have bound : bytes.length < TCP.Seq.modulus := by unfold TCP.Seq.halfSpace TCP.Seq.modulus at *; omega
  have offset : ackOffset current.original ack = bytes.length := by
    rw [ackOffset, geometry.originalBase, acknowledgment, TCP.Seq.distance_add, Nat.mod_eq_of_lt bound]
  have stale := current.originalValid.1
  rw [geometry.original_observed] at stale
  refine ⟨profile, empty, ?_, ?_, ?_⟩
  · simp only [Session.sender, geometry.replyBase, sequence, TCP.Seq.distance_self, Nat.zero_le]
  · simpa only [Session.peer, offset, geometry.original_observed] using Nat.le_refl bytes.length
  · simp only [Session.peer, offset]
    omega

theorem Geometry.known (geometry : Geometry initial current bytes source) (segment : TCP.Segment)
    (nonempty : bytes ≠ []) (sequence : segment.sequence = current.original.base) (payload : segment.payload = bytes)
    (observations : List Seen) (seen : Seen) (selected : observations[source]? = some seen)
    (entry : seen.attachment.entry = current.entry) (direction : seen.attachment.direction = .original)
    (profile : DataProfile seen.segment) (seenSequence : seen.segment.sequence = current.original.base)
    (seenPayload : seen.segment.payload = bytes) :
    KnownRange current.original current.entry .original segment observations := by
  have valid := current.originalValid.2.2.2
  have covered : bytes.length ≤ coverageBound := by
    have old := valid.2.1
    rw [geometry.originalCoverage] at old
    have member : (⟨0, bytes, 0, source⟩ : Theory.SparseCoverage.Run Nat) ∈
        (CampusTCPRoundAdmission.rangeCoverage bytes source).runs := by simp [CampusTCPRoundAdmission.rangeCoverage]
    simpa only [Theory.SparseCoverage.Run.limit, Nat.zero_add] using (old _ member).2.1
  have positive : 0 < bytes.length := List.length_pos_iff.mpr nonempty
  have placed : placement current.original segment observations.length = .ok
      ⟨current.original.coverage, ⟨0, bytes, 0, source⟩, 0, 0⟩ := by
    simp only [placement, sequence, TCP.Seq.distance_self, payload, Theory.SparseCoverage.accept,
      valid, not_true_eq_false, ite_false, nonempty, Nat.zero_add, Nat.not_lt.mpr covered]
    simp [geometry.originalCoverage, CampusTCPRoundAdmission.rangeCoverage,
      Theory.SparseCoverage.place, Theory.SparseCoverage.current, Theory.SparseCoverage.Run.limit,
      Nat.not_le.mpr positive, Theory.SparseCoverage.commit]
  simp only [KnownRange, placed, selected, RangeFrom, sequence, seenSequence, TCP.Seq.distance_self,
    payload, seenPayload, entry, direction, profile, geometry.original_highEnd,
    Nat.zero_add, Nat.sub_self, List.drop_zero, List.take_length, Nat.le_refl, true_and]
  exact ⟨nonempty, trivial⟩

theorem Geometry.of_fresh (first : CampusTCPRoundAdmission.DataGeometry initial current data source)
    (payload : data.payload = bytes) (empty : initial.reply.coverage = Coverage.initial) :
    Geometry initial current bytes source :=
  ⟨first.entry, first.original_base, by simpa only [payload] using first.original_coverage,
    first.reply_base, first.reply_coverage.trans empty, first.clientMSS, first.serverMSS⟩

theorem Geometry.of_ack (geometry : Geometry initial current bytes source)
    (changed : CampusTCPRoundAdmission.AckGeometry current after ack) : Geometry initial after bytes source := by
  refine ⟨changed.entry.trans geometry.entry, ?_, ?_, ?_, ?_,
    changed.clientMSS.trans geometry.clientMSS, changed.serverMSS.trans geometry.serverMSS⟩
  · exact changed.original_base.trans geometry.originalBase
  · exact changed.original_coverage.trans geometry.originalCoverage
  · rw [changed.reply]
    exact geometry.replyBase
  · rw [changed.reply]
    exact geometry.replyCoverage

theorem Result.original_repeat_fields
    (result : TCP.Admission.Result before input lifecycle prepared) (session : TCP.Admission.Session)
    (phase : before.phase = .data session) (direction : prepared.attachment.direction = .original)
    (known : KnownRange session.original session.entry .original input.packet.segment before.observations) :
    ∃ after : TCP.Admission.Session, result.state.phase = .data after ∧ after.entry = session.entry ∧
      after.original = session.original ∧ after.reply = acknowledgedLane session.reply input.packet.segment ∧
      after.clientMSS = session.clientMSS ∧ after.serverMSS = session.serverMSS := by
  have notFresh := known.not_fresh (peer := session.reply) (peerMSS := session.serverMSS)
  cases before with
  | mk prior observations =>
    cases phase
    rw [result.phase]
    simp only [nextPhase]
    split
    · simp only [notFresh, dite_false]
      exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rename_i selected
      rw [direction] at selected
      cases selected

theorem Processing.original_repeat_geometry
    (processing : CampusTCPService.Processing context before packet zone)
    (current : TCP.Admission.Session) (phase : before.admission.phase = .data current)
    (direction : processing.prepared.attachment.direction = .original)
    (geometry : Geometry initial current bytes source)
    (known : KnownRange current.original current.entry .original packet.packet.segment before.admission.observations) :
    ∃ after : TCP.Admission.Session, processing.nextAdmission.phase = .data after ∧
      Geometry initial after bytes source := by
  obtain ⟨after, phaseAfter, entry, original, reply, clientMSS, serverMSS⟩ :=
    Result.original_repeat_fields processing.admitted current phase direction known
  refine ⟨after, ?_, entry.trans geometry.entry, ?_, ?_, ?_, ?_,
    clientMSS.trans geometry.clientMSS, serverMSS.trans geometry.serverMSS⟩
  · rw [CampusTCPRoundAdmission.Processing.committed_data processing current phase]
    exact phaseAfter
  · rw [original]
    exact geometry.originalBase
  · rw [original]
    exact geometry.originalCoverage
  · rw [reply, acknowledgedLane_base]
    exact geometry.replyBase
  · rw [reply, acknowledgedLane_coverage]
    exact geometry.replyCoverage

theorem Processing.reply_covering_geometry
    (processing : CampusTCPService.Processing context before packet zone)
    (current : TCP.Admission.Session) (phase : before.admission.phase = .data current)
    (direction : processing.prepared.attachment.direction = .reply)
    (geometry : Geometry initial current bytes source)
    (profile : DataProfile packet.packet.segment) (empty : packet.packet.segment.payload = [])
    (sequence : packet.packet.segment.sequence = initial.reply.base)
    (acknowledgment : packet.packet.segment.acknowledgment = initial.original.base.add bytes.length) :
    ∃ after : TCP.Admission.Session, processing.nextAdmission.phase = .data after ∧
      Geometry initial after bytes source ∧ after.original.acknowledged = bytes.length := by
  have ready := geometry.ack_ready packet.packet.segment profile empty sequence acknowledgment
  obtain ⟨after, phaseAfter, entry, original, reply, clientMSS, serverMSS⟩ :=
    CampusTCPRoundAdmission.Result.reply_fresh_fields processing.admitted current phase direction
      (ready.allowed before.admission.observations.length)
  have sameReply : after.reply = current.reply := by
    rw [reply]
    exact sentLane_empty _ _ _ current.replyValid empty
  have changed : CampusTCPRoundAdmission.AckGeometry current after packet.packet.segment :=
    ⟨entry, original, sameReply, clientMSS, serverMSS⟩
  refine ⟨after, ?_, geometry.of_ack changed, ?_⟩
  · rw [CampusTCPRoundAdmission.Processing.committed_data processing current phase]
    exact phaseAfter
  · rw [← geometry.original_observed]
    apply changed.original_full_ack
    simpa only [geometry.originalBase, geometry.original_observed] using acknowledgment

end Netlib.Check.CampusTCPRecoveryRoundGateway
