import Netlib.Protocol.TCP.AdmissionEnabled
import Netlib.Protocol.TCP.AdmissionExecutionControlFacts
import Netlib.Protocol.TCP.Handshake

/-!
# Empty-byte geometry during recovered startup

The lane fields omit window markers. Empty ACK service applies the actual
window update while keeping byte coverage and acknowledgment offsets empty.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupGeometry

open Protocol Protocol.TCP Admission

structure LaneGeometry (lane : Lane) (base : Seq) (capacity : Nat) : Prop where
  baseEq : lane.base = base
  coverage : lane.coverage = Coverage.initial
  acknowledged : lane.acknowledged = 0
  window : lane.peerWindow.val = capacity

structure Geometry (active passive : Handshake.Local) (session : Admission.Session) : Prop where
  original : LaneGeometry session.original (active.iss.add 1) passive.capacity
  reply : LaneGeometry session.reply (passive.iss.add 1) active.capacity
  clientMSS : session.clientMSS = Handshake.receiveOffer active
  serverMSS : session.serverMSS = Handshake.receiveOffer passive

variable {active passive : Handshake.Local} {session : Admission.Session}

theorem LaneGeometry.initial (base : Seq) (window : InternetChecksum.Word) (sequence acknowledgment : Seq) :
    LaneGeometry (Lane.initial base window sequence acknowledgment) base window.val :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem LaneGeometry.observed (geometry : LaneGeometry lane base capacity) : lane.observed = 0 := by
  rw [Lane.observed, geometry.coverage]
  rfl

theorem LaneGeometry.highEnd (geometry : LaneGeometry lane base capacity) : lane.highEnd = 0 := by
  rw [Lane.highEnd, geometry.coverage]
  rfl

theorem LaneGeometry.sent_empty (geometry : LaneGeometry lane base capacity) (valid : lane.Valid)
    (empty : segment.payload = []) (source : Nat) : LaneGeometry (sentLane lane segment source) base capacity := by
  rw [Admission.sentLane_empty lane segment source valid empty]
  exact geometry

theorem LaneGeometry.acknowledgedLane (geometry : LaneGeometry lane base capacity)
    (bounded : ackOffset lane segment ≤ lane.observed) (incoming : segment.window.val = capacity) :
    LaneGeometry (Admission.acknowledgedLane lane segment) base capacity := by
  have offset : ackOffset lane segment = 0 := Nat.eq_zero_of_le_zero (by simpa only [geometry.observed] using bounded)
  refine ⟨(acknowledgedLane_base _ _).trans geometry.baseEq,
    (acknowledgedLane_coverage _ _).trans geometry.coverage, ?_, ?_⟩
  · unfold Admission.acknowledgedLane
    split <;> simp only [geometry.acknowledged, offset, Nat.max_self]
  · unfold Admission.acknowledgedLane
    split
    · exact incoming
    · exact geometry.window

private theorem original_ack_bound
    (allowed : DataAllowed session.original session.reply segment session.serverMSS count ∨
      RepeatedAllowed session.original session.reply session.entry .original segment session.serverMSS observations) :
    ackOffset session.reply segment ≤ session.reply.observed := by
  rcases allowed with fresh | repeated
  · exact fresh.2.2.2.1
  · exact repeated.2.2.2.2.2.1

private theorem reply_ack_bound
    (allowed : DataAllowed session.reply session.original segment session.clientMSS count ∨
      RepeatedAllowed session.reply session.original session.entry .reply segment session.clientMSS observations) :
    ackOffset session.original segment ≤ session.original.observed := by
  rcases allowed with fresh | repeated
  · exact fresh.2.2.2.1
  · exact repeated.2.2.2.2.2.1

theorem Geometry.next_empty (geometry : Geometry active passive session)
    (allowed : Admission.Allowed (.data session) attachment segment observations)
    (empty : segment.payload = [])
    (window : segment.window.val = match attachment.direction with | .original => active.capacity | .reply => passive.capacity) :
    ∃ after, Admission.nextPhase (.data session) attachment segment allowed = .data after ∧
      after.entry = session.entry ∧ Geometry active passive after := by
  cases attachment with
  | mk entry direction classification fresh =>
    cases direction with
    | original =>
      have bound := original_ack_bound allowed.2.2
      have peer := geometry.reply.acknowledgedLane bound window
      have sender := geometry.original.sent_empty session.originalValid empty observations.length
      simp only [Admission.nextPhase]
      split
      · exact ⟨_, rfl, rfl, sender, peer, geometry.clientMSS, geometry.serverMSS⟩
      · exact ⟨_, rfl, rfl, geometry.original, peer, geometry.clientMSS, geometry.serverMSS⟩
    | reply =>
      have bound := reply_ack_bound allowed.2.2
      have peer := geometry.original.acknowledgedLane bound window
      have sender := geometry.reply.sent_empty session.replyValid empty observations.length
      simp only [Admission.nextPhase]
      split
      · exact ⟨_, rfl, rfl, peer, sender, geometry.clientMSS, geometry.serverMSS⟩
      · exact ⟨_, rfl, rfl, peer, geometry.reply, geometry.clientMSS, geometry.serverMSS⟩

theorem Geometry.legacy_empty (geometry : Geometry active passive session)
    (result : Admission.Result before input lifecycle prepared) (phase : before.phase = .data session)
    (empty : input.packet.segment.payload = [])
    (window : input.packet.segment.window.val =
      match prepared.attachment.direction with | .original => active.capacity | .reply => passive.capacity) :
    ∃ after, result.state.phase = .data after ∧ after.entry = session.entry ∧ Geometry active passive after := by
  have admitted : Admission.Allowed (.data session) prepared.attachment input.packet.segment before.observations :=
    phase ▸ result.admitted
  obtain ⟨after, next, entry, geometry⟩ := geometry.next_empty admitted empty window
  refine ⟨after, ?_, entry, geometry⟩
  have computed := result.phase
  simp only [phase] at computed
  exact computed.trans next

theorem Geometry.admitted_empty (geometry : Geometry active passive session)
    (result : AdmissionExecution.Result mode before input lifecycle prepared) (phase : before.phase = .data session)
    (empty : input.packet.segment.payload = [])
    (window : input.packet.segment.window.val =
      match prepared.attachment.direction with | .original => active.capacity | .reply => passive.capacity) :
    ∃ after, (AdmissionExecution.Result.state result).phase = .data after ∧
      after.entry = session.entry ∧ Geometry active passive after := by
  rcases AdmissionExecution.Result.legacy_or_stutter result with legacy | ⟨modeEq, stutter⟩
  · obtain ⟨after, selected, entry, shape⟩ := geometry.legacy_empty
      (AdmissionExecution.Result.asLegacy result legacy) phase empty window
    exact ⟨after, by simpa only [AdmissionExecution.Result.asLegacy_state] using selected, entry, shape⟩
  · subst mode
    have unchanged := AdmissionStartupRecovery.nextPhase_stutter stutter result.admitted
    exact ⟨session, result.phase.trans (unchanged.trans phase), rfl, geometry⟩

end Netlib.Check.CampusTCPRecoveryStartupGeometry
