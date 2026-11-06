import Netlib.Check.CampusTCPService
import Netlib.Protocol.TCP.AdmissionEnabled

/-!
# Admission state in one lossless TCP round

The first data range starts at the actual lane base.
Its actual admission supplies the geometry for the reverse ACK.
-/

namespace Netlib.Check.CampusTCPRoundAdmission

open Packet Protocol TCP
open TCP.Admission

def rangeCoverage (bytes : List UInt8) (source : Nat) : Coverage.State Nat :=
  ⟨[⟨0, bytes, 0, source⟩], 1⟩

theorem sentLane_empty_base (sender : Lane) (segment : Segment) (source : Nat)
    (empty : sender.coverage = Coverage.initial) (sequence : segment.sequence = sender.base)
    (nonempty : segment.payload ≠ []) (bound : segment.payload.length ≤ coverageBound) :
    sentLane sender segment source = { sender with coverage := rangeCoverage segment.payload source } := by
  have valid : (Coverage.initial : Coverage.State Nat).Valid coverageBound :=
    Theory.SparseCoverage.initial_valid _
  simp only [sentLane, placement, empty, sequence, Seq.distance_self, Theory.SparseCoverage.accept,
    valid, not_true_eq_false, ite_false, nonempty, Nat.zero_add, Nat.not_lt.mpr bound]
  rfl

theorem Result.original_fresh_fields
    (result : Admission.Result before input lifecycle prepared) (session : Admission.Session)
    (phase : before.phase = .data session) (direction : prepared.attachment.direction = .original)
    (fresh : DataAllowed session.original session.reply input.packet.segment session.serverMSS before.observations.length) :
    ∃ after : Admission.Session, result.state.phase = .data after ∧ after.entry = session.entry ∧
      after.original = sentLane session.original input.packet.segment before.observations.length ∧
      after.reply = acknowledgedLane session.reply input.packet.segment ∧
      after.clientMSS = session.clientMSS ∧ after.serverMSS = session.serverMSS := by
  cases before with
  | mk prior observations =>
    cases phase
    rw [result.phase]
    simp only [nextPhase]
    split
    · simp only [fresh, dite_true]
      exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rename_i selected
      rw [direction] at selected
      cases selected

structure DataGeometry (prior after : Admission.Session) (segment : Segment) (source : Nat) : Prop where
  entry : after.entry = prior.entry
  original : after.original = { prior.original with coverage := rangeCoverage segment.payload source }
  reply : after.reply = acknowledgedLane prior.reply segment
  clientMSS : after.clientMSS = prior.clientMSS
  serverMSS : after.serverMSS = prior.serverMSS

theorem initial_fresh_ready (session : Admission.Session) (segment : Segment)
    (originalCoverage : session.original.coverage = Coverage.initial)
    (originalAck : session.original.acknowledged = 0)
    (replyCoverage : session.reply.coverage = Coverage.initial) (replyAck : session.reply.acknowledged = 0)
    (sequence : segment.sequence = session.original.base) (acknowledgment : segment.acknowledgment = session.reply.base)
    (profile : DataProfile segment) (nonempty : segment.payload ≠ [])
    (mss : segment.payload.length ≤ session.serverMSS.limit)
    (window : segment.payload.length ≤ session.original.peerWindow.val)
    (epoch : segment.payload.length + 2 < Seq.halfSpace) : FreshReady session .original segment := by
  refine ⟨profile, nonempty, mss, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Admission.Session.sender, sequence, Seq.distance_self, Nat.zero_add] using epoch
  · simp only [Admission.Session.sender, originalAck, sequence, Seq.distance_self, Nat.le_refl]
  · simpa only [Admission.Session.sender, originalAck, sequence, Seq.distance_self, Nat.zero_add] using window
  · simp only [Admission.Session.sender, originalCoverage, Theory.SparseCoverage.initial, List.not_mem_nil,
      false_implies, implies_true]
  · simp only [Admission.Session.peer, ackOffset, acknowledgment, Seq.distance_self, Lane.observed,
      replyCoverage, Theory.SparseCoverage.initial, Theory.SparseCoverage.State.frontier,
      Theory.SparseCoverage.frontierFrom, Nat.le_refl]
  · simp only [Admission.Session.peer, replyAck, ackOffset, acknowledgment, Seq.distance_self,
      Nat.zero_add, Nat.zero_le]

theorem Result.original_empty_geometry
    (result : Admission.Result before input lifecycle prepared) (session : Admission.Session)
    (phase : before.phase = .data session) (direction : prepared.attachment.direction = .original)
    (originalCoverage : session.original.coverage = Coverage.initial)
    (originalAck : session.original.acknowledged = 0)
    (replyCoverage : session.reply.coverage = Coverage.initial) (replyAck : session.reply.acknowledged = 0)
    (sequence : input.packet.segment.sequence = session.original.base)
    (acknowledgment : input.packet.segment.acknowledgment = session.reply.base)
    (profile : DataProfile input.packet.segment) (nonempty : input.packet.segment.payload ≠ [])
    (mss : input.packet.segment.payload.length ≤ session.serverMSS.limit)
    (window : input.packet.segment.payload.length ≤ session.original.peerWindow.val)
    (epoch : input.packet.segment.payload.length + 2 < Seq.halfSpace) :
    ∃ after : Admission.Session, result.state.phase = .data after ∧
      DataGeometry session after input.packet.segment before.observations.length := by
  have ready := initial_fresh_ready session input.packet.segment originalCoverage originalAck replyCoverage replyAck
    sequence acknowledgment profile nonempty mss window epoch
  have fresh := ready.allowed before.observations.length
  obtain ⟨after, phaseAfter, entry, original, reply, clientMSS, serverMSS⟩ :=
    Result.original_fresh_fields result session phase direction fresh
  have bound : input.packet.segment.payload.length ≤ coverageBound := by unfold coverageBound; omega
  refine ⟨after, phaseAfter, entry, ?_, reply, clientMSS, serverMSS⟩
  rw [original]
  exact sentLane_empty_base _ _ _ originalCoverage sequence nonempty bound

theorem DataGeometry.original_base (geometry : DataGeometry prior after segment source) :
    after.original.base = prior.original.base := by rw [geometry.original]

theorem DataGeometry.reply_base (geometry : DataGeometry prior after segment source) :
    after.reply.base = prior.reply.base := by rw [geometry.reply, acknowledgedLane_base]

theorem DataGeometry.original_coverage (geometry : DataGeometry prior after segment source) :
    after.original.coverage = rangeCoverage segment.payload source := by rw [geometry.original]

theorem DataGeometry.original_observed (geometry : DataGeometry prior after segment source) :
    after.original.observed = segment.payload.length := by
  simp only [Lane.observed, geometry.original_coverage, rangeCoverage, Theory.SparseCoverage.State.frontier,
    Theory.SparseCoverage.frontierFrom, ↓reduceIte, Theory.SparseCoverage.Run.limit, Nat.zero_add]

theorem DataGeometry.original_highEnd (geometry : DataGeometry prior after segment source) :
    after.original.highEnd = segment.payload.length := by
  simp only [Lane.highEnd, geometry.original_coverage, rangeCoverage, Theory.SparseCoverage.State.highEnd,
    Theory.SparseCoverage.highEnd, Theory.SparseCoverage.Run.limit, Nat.zero_add, Nat.max_zero]

theorem DataGeometry.original_acknowledged (geometry : DataGeometry prior after segment source) :
    after.original.acknowledged = prior.original.acknowledged := by rw [geometry.original]

theorem DataGeometry.reply_coverage (geometry : DataGeometry prior after segment source) :
    after.reply.coverage = prior.reply.coverage := by rw [geometry.reply, acknowledgedLane_coverage]

theorem DataGeometry.reply_acknowledged (geometry : DataGeometry prior after segment source)
    (acknowledgment : segment.acknowledgment = prior.reply.base) :
    after.reply.acknowledged = prior.reply.acknowledged := by
  rw [geometry.reply, acknowledgedLane_count]
  simp only [ackOffset, acknowledgment, Seq.distance_self, Nat.max_zero]

theorem DataGeometry.reply_ack_ready (geometry : DataGeometry prior after data source) (ack : Segment)
    (profile : DataProfile ack) (empty : ack.payload = [])
    (sequence : ack.sequence = prior.reply.base)
    (acknowledgment : ack.acknowledgment = prior.original.base.add data.payload.length) :
    AckReady after .reply ack := by
  have epoch := after.originalValid.2.1
  rw [geometry.original_highEnd] at epoch
  have bound : data.payload.length < Seq.modulus := by unfold Seq.halfSpace Seq.modulus at *; omega
  have offset : ackOffset after.original ack = data.payload.length := by
    rw [ackOffset, geometry.original_base, acknowledgment, Seq.distance_add, Nat.mod_eq_of_lt bound]
  have stale := after.originalValid.1
  rw [geometry.original_observed] at stale
  refine ⟨profile, empty, ?_, ?_, ?_⟩
  · simp only [Admission.Session.sender, geometry.reply_base, sequence, Seq.distance_self, Nat.zero_le]
  · simpa only [Admission.Session.peer, offset, geometry.original_observed] using Nat.le_refl data.payload.length
  · simp only [Admission.Session.peer, offset]
    omega

theorem Result.reply_fresh_fields
    (result : Admission.Result before input lifecycle prepared) (session : Admission.Session)
    (phase : before.phase = .data session) (direction : prepared.attachment.direction = .reply)
    (fresh : DataAllowed session.reply session.original input.packet.segment session.clientMSS before.observations.length) :
    ∃ after : Admission.Session, result.state.phase = .data after ∧ after.entry = session.entry ∧
      after.original = acknowledgedLane session.original input.packet.segment ∧
      after.reply = sentLane session.reply input.packet.segment before.observations.length ∧
      after.clientMSS = session.clientMSS ∧ after.serverMSS = session.serverMSS := by
  cases before with
  | mk prior observations =>
    cases phase
    rw [result.phase]
    simp only [nextPhase]
    split
    · rename_i selected
      rw [direction] at selected
      cases selected
    · simp only [fresh, dite_true]
      exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩

structure AckGeometry (prior after : Admission.Session) (segment : Segment) : Prop where
  entry : after.entry = prior.entry
  original : after.original = acknowledgedLane prior.original segment
  reply : after.reply = prior.reply
  clientMSS : after.clientMSS = prior.clientMSS
  serverMSS : after.serverMSS = prior.serverMSS

theorem Result.reply_covering_geometry
    (result : Admission.Result before input lifecycle prepared) (session : Admission.Session)
    (phase : before.phase = .data session) (direction : prepared.attachment.direction = .reply)
    (geometry : DataGeometry prior session data source)
    (profile : DataProfile input.packet.segment) (empty : input.packet.segment.payload = [])
    (sequence : input.packet.segment.sequence = prior.reply.base)
    (acknowledgment : input.packet.segment.acknowledgment = prior.original.base.add data.payload.length) :
    ∃ after : Admission.Session, result.state.phase = .data after ∧ AckGeometry session after input.packet.segment := by
  have ready := geometry.reply_ack_ready input.packet.segment profile empty sequence acknowledgment
  obtain ⟨after, phaseAfter, entry, original, reply, clientMSS, serverMSS⟩ :=
    Result.reply_fresh_fields result session phase direction (ready.allowed before.observations.length)
  refine ⟨after, phaseAfter, entry, original, ?_, clientMSS, serverMSS⟩
  rw [reply]
  exact sentLane_empty _ _ _ session.replyValid empty

theorem AckGeometry.original_base (geometry : AckGeometry prior after segment) :
    after.original.base = prior.original.base := by rw [geometry.original, acknowledgedLane_base]

theorem AckGeometry.original_coverage (geometry : AckGeometry prior after segment) :
    after.original.coverage = prior.original.coverage := by rw [geometry.original, acknowledgedLane_coverage]

theorem AckGeometry.original_observed (geometry : AckGeometry prior after segment) :
    after.original.observed = prior.original.observed := by rw [geometry.original, acknowledgedLane_observed]

theorem AckGeometry.original_highEnd (geometry : AckGeometry prior after segment) :
    after.original.highEnd = prior.original.highEnd := by rw [geometry.original, acknowledgedLane_highEnd]

theorem AckGeometry.original_full_ack (geometry : AckGeometry prior after segment)
    (acknowledgment : segment.acknowledgment = prior.original.base.add prior.original.observed) :
    after.original.acknowledged = prior.original.observed := by
  have epoch := prior.originalValid.2.1
  have covered := prior.original.coverage.frontier_le_highEnd
  change prior.original.observed ≤ prior.original.highEnd at covered
  have bound : prior.original.observed < Seq.modulus := by unfold Seq.halfSpace Seq.modulus at *; omega
  rw [geometry.original, acknowledgedLane_count]
  simp only [ackOffset, acknowledgment, Seq.distance_add, Nat.mod_eq_of_lt bound]
  exact Nat.max_eq_right prior.originalValid.1

theorem DataGeometry.covering_ack_retirement (dataGeometry : DataGeometry initial afterData data source)
    (ackGeometry : AckGeometry afterData afterAck ack)
    (acknowledgment : ack.acknowledgment = initial.original.base.add data.payload.length) :
    afterAck.original.acknowledged = data.payload.length ∧
      afterAck.original.coverage = rangeCoverage data.payload source ∧
      afterAck.original.observed = data.payload.length ∧ afterAck.original.highEnd = data.payload.length ∧
      afterAck.reply = afterData.reply ∧ afterAck.entry = initial.entry ∧
      afterAck.clientMSS = initial.clientMSS ∧ afterAck.serverMSS = initial.serverMSS := by
  have acknowledgmentAt : ack.acknowledgment = afterData.original.base.add afterData.original.observed := by
    simpa only [dataGeometry.original_base, dataGeometry.original_observed] using acknowledgment
  exact ⟨(ackGeometry.original_full_ack acknowledgmentAt).trans dataGeometry.original_observed,
    ackGeometry.original_coverage.trans dataGeometry.original_coverage,
    ackGeometry.original_observed.trans dataGeometry.original_observed,
    ackGeometry.original_highEnd.trans dataGeometry.original_highEnd,
    ackGeometry.reply, ackGeometry.entry.trans dataGeometry.entry,
    ackGeometry.clientMSS.trans dataGeometry.clientMSS, ackGeometry.serverMSS.trans dataGeometry.serverMSS⟩

theorem Processing.committed_data (processing : CampusTCPService.Processing context before source zone)
    (session : Admission.Session) (phase : before.admission.phase = .data session) :
    processing.nextAdmission = processing.admitted.state := by
  have allowed : Allowed (.data session) processing.prepared.attachment source.packet.segment before.admission.observations := by
    simpa only [phase, WireForwarding.Source.asInput] using processing.admitted.admitted
  have existing : processing.prepared.attachment.fresh = false := allowed.2.1
  exact (processing.admitted.existing_committed _ existing _ processing.committed).1

theorem Processing.original_empty_geometry (processing : CampusTCPService.Processing context before source zone)
    (session : Admission.Session) (phase : before.admission.phase = .data session)
    (direction : processing.prepared.attachment.direction = .original)
    (originalCoverage : session.original.coverage = Coverage.initial)
    (originalAck : session.original.acknowledged = 0)
    (replyCoverage : session.reply.coverage = Coverage.initial) (replyAck : session.reply.acknowledged = 0)
    (sequence : source.packet.segment.sequence = session.original.base)
    (acknowledgment : source.packet.segment.acknowledgment = session.reply.base)
    (profile : DataProfile source.packet.segment) (nonempty : source.packet.segment.payload ≠ [])
    (mss : source.packet.segment.payload.length ≤ session.serverMSS.limit)
    (window : source.packet.segment.payload.length ≤ session.original.peerWindow.val)
    (epoch : source.packet.segment.payload.length + 2 < Seq.halfSpace) :
    ∃ after : Admission.Session, processing.nextAdmission.phase = .data after ∧
      DataGeometry session after source.packet.segment before.admission.observations.length := by
  obtain ⟨after, phaseAfter, geometry⟩ := Result.original_empty_geometry processing.admitted session phase direction
    originalCoverage originalAck replyCoverage replyAck sequence acknowledgment profile nonempty mss window epoch
  exact ⟨after, by rw [Processing.committed_data processing session phase]; exact phaseAfter, geometry⟩

theorem Processing.reply_covering_geometry (processing : CampusTCPService.Processing context before source zone)
    (session : Admission.Session) (phase : before.admission.phase = .data session)
    (direction : processing.prepared.attachment.direction = .reply)
    (geometry : DataGeometry prior session data dataSource)
    (profile : DataProfile source.packet.segment) (empty : source.packet.segment.payload = [])
    (sequence : source.packet.segment.sequence = prior.reply.base)
    (acknowledgment : source.packet.segment.acknowledgment = prior.original.base.add data.payload.length) :
    ∃ after : Admission.Session, processing.nextAdmission.phase = .data after ∧
      AckGeometry session after source.packet.segment := by
  obtain ⟨after, phaseAfter, acknowledged⟩ := Result.reply_covering_geometry processing.admitted session phase direction
    geometry profile empty sequence acknowledgment
  exact ⟨after, by rw [Processing.committed_data processing session phase]; exact phaseAfter, acknowledged⟩

theorem Evidence.state_of_processing
    (evidence : CampusTCPService.Evidence context before source zone ingress)
    (processing : CampusTCPService.Processing context before source zone)
    (present : evidence.processing = some processing) :
    evidence.tracker = processing.outcome.state ∧ evidence.admission = processing.nextAdmission := by
  cases selected : evidence.operation with
  | earlyDrop denied => simp only [CampusTCPService.Evidence.processing, selected, reduceCtorEq] at present
  | processed permitted actual =>
    simp only [CampusTCPService.Evidence.processing, selected, Option.some.injEq] at present
    cases present
    exact ⟨by simp only [CampusTCPService.Evidence.tracker, selected],
      by simp only [CampusTCPService.Evidence.admission, selected]⟩

end Netlib.Check.CampusTCPRoundAdmission
