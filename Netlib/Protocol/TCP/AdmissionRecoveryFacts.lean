import Netlib.Protocol.TCP.AdmissionMSSFacts

/-!
# Actual sources in sparse TCP admission

A repeat retains the first observed source and adds no coverage.
A new disjoint range records the actual observation index.
ACK and window effects still use the current packet.
-/

namespace Netlib.Protocol.TCP.Admission

def Session.lane (session : Session) : Direction → Lane
  | .original => session.original
  | .reply => session.reply

theorem KnownRange.not_fresh (known : KnownRange sender entry direction segment observations) :
    ¬DataAllowed sender peer segment peerMSS observations.length := by
  intro allowed
  obtain ⟨result, accepted, duplicate, _, _, _⟩ := known.placement
  have nonempty := (Theory.SparseCoverage.accept_stages _ _ _ _ _ _ accepted).2.1
  have fresh := allowed.2.1
  simp only [FreshSequence, nonempty, ite_false, accepted] at fresh
  have positive : 0 < segment.payload.length := List.length_pos_iff.mpr nonempty
  omega

theorem Result.repeated_source (_result : Result before input lifecycle prepared)
    (_phase : before.phase = .data session)
    (known : KnownRange (session.lane prepared.attachment.direction) session.entry
      prepared.attachment.direction input.packet.segment before.observations) :
    ∃ seen ∈ before.observations, seen.attachment.entry = session.entry ∧
      seen.attachment.direction = prepared.attachment.direction ∧
      input.packet.segment.payload = (seen.segment.payload.drop
        (Seq.distance (session.lane prepared.attachment.direction).base input.packet.segment.sequence -
          Seq.distance (session.lane prepared.attachment.direction).base seen.segment.sequence)).take
        input.packet.segment.payload.length := by
  obtain ⟨seen, member, source⟩ := known.source
  exact ⟨seen, member, source.1, source.2.1, source.2.2.2.2.2.2.2⟩

theorem Result.repeated_source_index (_result : Result before input lifecycle prepared)
    (_phase : before.phase = .data session)
    (known : KnownRange (session.lane prepared.attachment.direction) session.entry
      prepared.attachment.direction input.packet.segment before.observations) :
    ∃ placed, placement (session.lane prepared.attachment.direction) input.packet.segment before.observations.length = .ok placed ∧
      placed.novel = 0 ∧ ∃ seen, before.observations[placed.source.metadata]? = some seen ∧
        RangeFrom (session.lane prepared.attachment.direction) session.entry prepared.attachment.direction
          input.packet.segment seen := known.placement

theorem nextPhase_repeated_original (session : Session) (attachment : ConntrackLifecycle.Attachment)
    (segment : Segment) {observations : List Seen}
    (allowed : Allowed (.data session) attachment segment observations)
    (direction : attachment.direction = .original)
    (known : KnownRange session.original session.entry .original segment observations) :
    ∃ after, nextPhase (.data session) attachment segment allowed = .data after ∧
      after.original = session.original ∧ after.reply.coverage = session.reply.coverage := by
  have fresh : ¬DataAllowed session.original session.reply segment session.serverMSS observations.length := known.not_fresh
  cases attachment with
  | mk entry selected classification freshFlag =>
    cases selected with
    | original =>
      simp only [nextPhase, fresh, dite_false]
      exact ⟨_, rfl, rfl, acknowledgedLane_coverage _ _⟩
    | reply => cases direction

theorem nextPhase_repeated_reply (session : Session) (attachment : ConntrackLifecycle.Attachment)
    (segment : Segment) {observations : List Seen}
    (allowed : Allowed (.data session) attachment segment observations)
    (direction : attachment.direction = .reply)
    (known : KnownRange session.reply session.entry .reply segment observations) :
    ∃ after, nextPhase (.data session) attachment segment allowed = .data after ∧
      after.reply = session.reply ∧ after.original.coverage = session.original.coverage := by
  have fresh : ¬DataAllowed session.reply session.original segment session.clientMSS observations.length := known.not_fresh
  cases attachment with
  | mk entry selected classification freshFlag =>
    cases selected with
    | original => cases direction
    | reply =>
      simp only [nextPhase, fresh, dite_false]
      exact ⟨_, rfl, rfl, acknowledgedLane_coverage _ _⟩

theorem Result.repeated_frontier (result : Result before input lifecycle prepared)
    (phase : before.phase = .data session)
    (known : KnownRange (session.lane prepared.attachment.direction) session.entry
      prepared.attachment.direction input.packet.segment before.observations) :
    ∃ after, result.state.phase = .data after ∧
      after.original.coverage = session.original.coverage ∧ after.reply.coverage = session.reply.coverage ∧
      result.state.observations = before.observations ++ [observe input lifecycle prepared] := by
  have allowed : Allowed (.data session) prepared.attachment input.packet.segment before.observations := phase ▸ result.admitted
  cases direction : prepared.attachment.direction with
  | original =>
    obtain ⟨after, computed, sender, peer⟩ := nextPhase_repeated_original session prepared.attachment
      input.packet.segment allowed direction (by simpa only [Session.lane, direction] using known)
    exact ⟨after, by rw [result.phase]; simpa only [phase] using computed,
      congrArg Lane.coverage sender, peer, result.ledger⟩
  | reply =>
    obtain ⟨after, computed, sender, peer⟩ := nextPhase_repeated_reply session prepared.attachment
      input.packet.segment allowed direction (by simpa only [Session.lane, direction] using known)
    exact ⟨after, by rw [result.phase]; simpa only [phase] using computed,
      peer, congrArg Lane.coverage sender, result.ledger⟩

def CoverageChange (sender after : Lane) (segment : Segment) (source : Nat) : Prop :=
  after.coverage = sender.coverage ∨
    ∃ placed, placement sender segment source = .ok placed ∧ after.coverage = placed.state

theorem sentLane_change (sender : Lane) (segment : Segment) (source : Nat) :
    CoverageChange sender (sentLane sender segment source) segment source := by
  unfold sentLane
  split
  · rename_i placed accepted
    exact .inr ⟨placed, accepted, rfl⟩
  · exact .inl rfl

theorem Result.coverage_transition (result : Result before input lifecycle prepared)
    (phase : before.phase = .data session) :
    ∃ after, result.state.phase = .data after ∧
      ((prepared.attachment.direction = .original ∧ after.reply.coverage = session.reply.coverage ∧
          CoverageChange session.original after.original input.packet.segment before.observations.length) ∨
        (prepared.attachment.direction = .reply ∧ after.original.coverage = session.original.coverage ∧
          CoverageChange session.reply after.reply input.packet.segment before.observations.length)) := by
  have allowed : Allowed (.data session) prepared.attachment input.packet.segment before.observations := phase ▸ result.admitted
  have computed : result.state.phase = nextPhase (.data session) prepared.attachment input.packet.segment allowed := by
    simpa only [phase] using result.phase
  rw [computed, nextPhase.eq_4]
  split
  · rename_i direction
    split
    · refine ⟨_, rfl, .inl ⟨direction, acknowledgedLane_coverage _ _, sentLane_change _ _ _⟩⟩
    · refine ⟨_, rfl, .inl ⟨direction, acknowledgedLane_coverage _ _, .inl rfl⟩⟩
  · rename_i direction
    split
    · refine ⟨_, rfl, .inr ⟨direction, acknowledgedLane_coverage _ _, sentLane_change _ _ _⟩⟩
    · refine ⟨_, rfl, .inr ⟨direction, acknowledgedLane_coverage _ _, .inl rfl⟩⟩

theorem placement_source (accepted : placement sender segment source = .ok placed) :
    placed.source ∈ placed.state.runs ∧
      Theory.SparseCoverage.Slice placed.source (Seq.distance sender.base segment.sequence) segment.payload placed.offset ∧
      ((placed.novel = 0 ∧ placed.state = sender.coverage ∧ placed.source ∈ sender.coverage.runs) ∨
        (placed.novel = segment.payload.length ∧ placed.source =
          Theory.SparseCoverage.current sender.coverage (Seq.distance sender.base segment.sequence) segment.payload source ∧
          placed.offset = 0 ∧ placed.state.nextID = sender.coverage.nextID + 1)) := by
  obtain ⟨member, slice⟩ := Theory.SparseCoverage.accept_source _ _ _ _ _ _ accepted
  exact ⟨member, slice, Theory.SparseCoverage.accept_cases _ _ _ _ _ _ accepted⟩

end Netlib.Protocol.TCP.Admission
