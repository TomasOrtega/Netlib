import Netlib.Protocol.TCP.Admission

/-!
# MSS learned by actual gateway admission

SYN and SYN,ACK supply separate receive offers.
The final ACK and later data preserve those offers.
Each admitted payload uses the receiver's offer for its actual direction.
-/

namespace Netlib.Protocol.TCP.Admission

open Packet

theorem Result.learned_syn (result : Result before input lifecycle prepared) (empty : before.phase = .empty) :
    ∃ offer, MSS.readStartup input.packet.segment.options = .ok offer ∧
      result.state.phase = .syn prepared.attachment.entry input.packet.segment.sequence input.packet.segment.window offer := by
  cases before with
  | mk phase observations =>
    change phase = .empty at empty
    subst phase
    let selected := MSS.selectStartup input.packet.segment.options (by simpa [Startup] using result.admitted.2.2.2.1)
    exact ⟨selected.val, selected.property, result.phase⟩

theorem Result.learned_synAck (result : Result before input lifecycle prepared)
    (pending : before.phase = .syn entry clientISS clientWindow clientMSS) :
    ∃ offer, MSS.readStartup input.packet.segment.options = .ok offer ∧
      result.state.phase = .synAck entry clientISS clientWindow input.packet.segment.sequence
        input.packet.segment.window clientMSS offer := by
  cases before with
  | mk phase observations =>
    change phase = .syn entry clientISS clientWindow clientMSS at pending
    subst phase
    let selected := MSS.selectStartup input.packet.segment.options (by simpa [Startup] using result.admitted.2.2.2.1.2.1)
    exact ⟨selected.val, selected.property, result.phase⟩

theorem Result.established_mss (result : Result before input lifecycle prepared)
    (pending : before.phase = .synAck entry clientISS clientWindow serverISS serverWindow clientMSS serverMSS) :
    ∃ session, result.state.phase = .data session ∧ session.clientMSS = clientMSS ∧ session.serverMSS = serverMSS := by
  cases before with
  | mk phase observations =>
    change phase = .synAck entry clientISS clientWindow serverISS serverWindow clientMSS serverMSS at pending
    subst phase
    rw [result.phase, nextPhase.eq_3]
    exact ⟨_, rfl, rfl, rfl⟩

theorem nextPhase_data_mss (session : Session) (attachment : ConntrackLifecycle.Attachment) (segment : Segment)
    {observations : List Seen} (allowed : Allowed (.data session) attachment segment observations) :
    ∃ after, nextPhase (.data session) attachment segment allowed = .data after ∧
      after.clientMSS = session.clientMSS ∧ after.serverMSS = session.serverMSS := by
  rw [nextPhase.eq_4]
  split <;> split <;> exact ⟨_, rfl, rfl, rfl⟩

theorem Result.preserves_mss (result : Result before input lifecycle prepared) (phase : before.phase = .data session) :
    ∃ after, result.state.phase = .data after ∧
      after.clientMSS = session.clientMSS ∧ after.serverMSS = session.serverMSS := by
  have allowed : Allowed (.data session) prepared.attachment input.packet.segment before.observations := phase ▸ result.admitted
  obtain ⟨after, computed, client, server⟩ := nextPhase_data_mss session prepared.attachment input.packet.segment allowed
  refine ⟨after, ?_, client, server⟩
  rw [result.phase]
  simpa only [phase] using computed

theorem nextPhase_data_bases (session : Session) (attachment : ConntrackLifecycle.Attachment) (segment : Segment)
    {observations : List Seen} (allowed : Allowed (.data session) attachment segment observations) :
    ∃ after, nextPhase (.data session) attachment segment allowed = .data after ∧
      after.entry = session.entry ∧ after.original.base = session.original.base ∧ after.reply.base = session.reply.base := by
  rw [nextPhase.eq_4]
  split <;> split <;> exact ⟨_, rfl, rfl, by simp only [sentLane_base, acknowledgedLane_base],
    by simp only [sentLane_base, acknowledgedLane_base]⟩

theorem Result.data_fields (result : Result before input lifecycle prepared) (phase : before.phase = .data session) :
    ∃ after, result.state.phase = .data after ∧ after.entry = session.entry ∧
      after.original.base = session.original.base ∧ after.reply.base = session.reply.base := by
  have allowed : Allowed (.data session) prepared.attachment input.packet.segment before.observations := phase ▸ result.admitted
  obtain ⟨after, computed, entry, original, reply⟩ := nextPhase_data_bases session prepared.attachment input.packet.segment allowed
  refine ⟨after, ?_, entry, original, reply⟩
  rw [result.phase]
  simpa only [phase] using computed

theorem Result.data_payload_bound (result : Result before input lifecycle prepared) (phase : before.phase = .data session) :
    input.packet.segment.payload.length ≤ (session.peerMSS prepared.attachment.direction).limit := by
  have allowed : Allowed (.data session) prepared.attachment input.packet.segment before.observations := phase ▸ result.admitted
  cases direction : prepared.attachment.direction with
  | original =>
    have selected : DataAllowed session.original session.reply input.packet.segment session.serverMSS before.observations.length ∨
        RepeatedAllowed session.original session.reply session.entry .original input.packet.segment session.serverMSS before.observations := by
      simpa only [Allowed, direction] using allowed.2.2
    exact selected.elim (fun fresh => fresh.2.2.1) (fun repeated => repeated.2.2.2.2.1)
  | reply =>
    have selected : DataAllowed session.reply session.original input.packet.segment session.clientMSS before.observations.length ∨
        RepeatedAllowed session.reply session.original session.entry .reply input.packet.segment session.clientMSS before.observations := by
      simpa only [Allowed, direction] using allowed.2.2
    exact selected.elim (fun fresh => fresh.2.2.1) (fun repeated => repeated.2.2.2.2.1)

theorem Result.committed_mss (result : Result before input lifecycle prepared) (phase : before.phase = .data session)
    (accepted : commit result tracker = .ok after) :
    after = result.state ∧
      (∃ next, after.phase = .data next ∧ next.clientMSS = session.clientMSS ∧ next.serverMSS = session.serverMSS) ∧
      input.packet.segment.payload.length ≤ (session.peerMSS prepared.attachment.direction).limit := by
  have allowed : Allowed (.data session) prepared.attachment input.packet.segment before.observations := phase ▸ result.admitted
  have fresh : prepared.attachment.fresh = false := allowed.2.1
  obtain ⟨same, _, _⟩ := result.existing_committed tracker fresh after accepted
  exact ⟨same, same ▸ result.preserves_mss phase, result.data_payload_bound phase⟩

end Netlib.Protocol.TCP.Admission
