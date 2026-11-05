import Netlib.Protocol.TCP.AdmissionMSSFacts

/-!
# Repeated ranges in actual TCP admission history

A repeated range comes from an earlier stored observation for the same entry and direction.
It adds one observation while the unique sender frontier stays equal.
The peer ACK and window still use the current checked segment.
-/

namespace Netlib.Protocol.TCP.Admission

theorem Result.repeated_source (result : Result before input lifecycle prepared)
    (phase : before.phase = .data session)
    (old : input.packet.segment.sequence ≠
      (match prepared.attachment.direction with | .original => session.original | .reply => session.reply).next) :
    ∃ seen ∈ before.observations, seen.attachment.entry = session.entry ∧
      seen.attachment.direction = prepared.attachment.direction ∧
      input.packet.segment.payload = (seen.segment.payload.drop
        (Seq.distance
          (match prepared.attachment.direction with | .original => session.original | .reply => session.reply).base
          input.packet.segment.sequence -
          Seq.distance
          (match prepared.attachment.direction with | .original => session.original | .reply => session.reply).base
          seen.segment.sequence)).take input.packet.segment.payload.length := by
  have allowed : Allowed (.data session) prepared.attachment input.packet.segment before.observations :=
    phase ▸ result.admitted
  cases direction : prepared.attachment.direction with
  | original =>
    have selected : DataAllowed session.original session.reply input.packet.segment session.serverMSS ∨
        RepeatedAllowed session.original session.reply session.entry .original input.packet.segment
          session.serverMSS before.observations := by
      simpa only [Allowed, direction] using allowed.2.2
    rcases selected with fresh | repeated
    · exact False.elim (old (by simpa only [direction] using fresh.2.1))
    · simpa only [direction] using repeated.source
  | reply =>
    have selected : DataAllowed session.reply session.original input.packet.segment session.clientMSS ∨
        RepeatedAllowed session.reply session.original session.entry .reply input.packet.segment
          session.clientMSS before.observations := by
      simpa only [Allowed, direction] using allowed.2.2
    rcases selected with fresh | repeated
    · exact False.elim (old (by simpa only [direction] using fresh.2.1))
    · simpa only [direction] using repeated.source

theorem nextPhase_repeated_original (session : Session) (attachment : ConntrackLifecycle.Attachment)
    (segment : Segment) {observations : List Seen}
    (allowed : Allowed (.data session) attachment segment observations)
    (direction : attachment.direction = .original) (old : segment.sequence ≠ session.original.next) :
    ∃ after, nextPhase (.data session) attachment segment allowed = .data after ∧
      after.original = session.original ∧ after.reply.observed = session.reply.observed := by
  have fresh : ¬DataAllowed session.original session.reply segment session.serverMSS :=
    fun selected => old selected.2.1
  cases attachment with
  | mk entry selected classification freshFlag =>
    cases selected with
    | original =>
      simp only [nextPhase, fresh, dite_false]
      exact ⟨_, rfl, rfl, acknowledgedLane_observed _ _⟩
    | reply => cases direction

theorem nextPhase_repeated_reply (session : Session) (attachment : ConntrackLifecycle.Attachment)
    (segment : Segment) {observations : List Seen}
    (allowed : Allowed (.data session) attachment segment observations)
    (direction : attachment.direction = .reply) (old : segment.sequence ≠ session.reply.next) :
    ∃ after, nextPhase (.data session) attachment segment allowed = .data after ∧
      after.reply = session.reply ∧ after.original.observed = session.original.observed := by
  have fresh : ¬DataAllowed session.reply session.original segment session.clientMSS :=
    fun selected => old selected.2.1
  cases attachment with
  | mk entry selected classification freshFlag =>
    cases selected with
    | original => cases direction
    | reply =>
      simp only [nextPhase, fresh, dite_false]
      exact ⟨_, rfl, rfl, acknowledgedLane_observed _ _⟩

theorem Result.repeated_frontier (result : Result before input lifecycle prepared)
    (phase : before.phase = .data session)
    (old : input.packet.segment.sequence ≠
      (match prepared.attachment.direction with | .original => session.original | .reply => session.reply).next) :
    ∃ after, result.state.phase = .data after ∧
      after.original.observed = session.original.observed ∧ after.reply.observed = session.reply.observed ∧
      result.state.observations = before.observations ++ [observe input lifecycle prepared] := by
  have allowed : Allowed (.data session) prepared.attachment input.packet.segment before.observations :=
    phase ▸ result.admitted
  cases direction : prepared.attachment.direction with
  | original =>
    obtain ⟨after, computed, sender, peer⟩ := nextPhase_repeated_original session prepared.attachment
      input.packet.segment allowed direction (by simpa only [direction] using old)
    exact ⟨after, by rw [result.phase]; simpa only [phase] using computed,
      congrArg Lane.observed sender, peer, result.ledger⟩
  | reply =>
    obtain ⟨after, computed, sender, peer⟩ := nextPhase_repeated_reply session prepared.attachment
      input.packet.segment allowed direction (by simpa only [direction] using old)
    exact ⟨after, by rw [result.phase]; simpa only [phase] using computed,
      peer, congrArg Lane.observed sender, result.ledger⟩

end Netlib.Protocol.TCP.Admission
