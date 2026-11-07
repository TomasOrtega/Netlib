import Netlib.Check.CampusTCPRecoveryStartupCurrentFloors
import Netlib.Check.CampusTCPRecoveryStartupPhase

/-!
# Startup admission from current fields

Exact observed templates enable duplicates. Empty ACKs use the current lane
geometry and retain the normal window update.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupAdmissionGuards

open Protocol Protocol.TCP
open CampusTCPRecoveryStartupPhase (Coordinates sideDirection)
open CampusTCPRecoveryStartupCurrentFloors (requiredLevel)

namespace C
export TCPHandshakeRecovery (Side Kind PacketShape)
end C

variable {active passive : Handshake.Local} {packet : Admission.Input}
variable {phase : Admission.Phase} {attachment : ConntrackLifecycle.Attachment} {entry : NetfilterNAT.Entry}
variable {observations : List Admission.Seen}

private theorem startup (shape : C.PacketShape active passive actor kind packet) :
    Admission.Startup packet.packet.segment kind.flags := by
  refine ⟨shape.profile.1, ?_, shape.payload⟩
  cases kind with
  | syn => simp only [TCPHandshakeRecovery.Kind.flags, TCPHandshakeRecovery.Kind.options, shape.options,
      Handshake.options_selected]; rfl
  | synAck => simp only [TCPHandshakeRecovery.Kind.flags, TCPHandshakeRecovery.Kind.options, shape.options,
      Handshake.options_selected]; rfl
  | finalAck | synReplyAck => exact shape.options

private theorem data_ack (geometry : CampusTCPRecoveryStartupGeometry.Geometry active passive session)
    (shape : C.PacketShape active passive actor kind packet) (ackKind : kind = .finalAck ∨ kind = .synReplyAck)
    (entryEq : attachment.entry = session.entry) (existing : attachment.fresh = false)
    (role : attachment.direction = sideDirection actor) :
    Admission.Allowed (.data session) attachment packet.packet.segment observations := by
  apply Admission.DataReady.allowed session attachment _ observations entryEq existing
  apply Or.inr
  refine ⟨?_, shape.payload, ?_, ?_, ?_⟩
  · rcases ackKind with rfl | rfl <;> exact ⟨Or.inl shape.profile.1, shape.options⟩
  · rw [role, shape.actorEq]
    rcases ackKind with rfl | rfl
    · change Seq.distance session.original.base packet.packet.segment.sequence ≤ session.original.highEnd
      rw [geometry.original.baseEq, shape.sequence, TCPHandshakeRecovery.Kind.sequence, Seq.distance_self]
      exact Nat.zero_le _
    · change Seq.distance session.reply.base packet.packet.segment.sequence ≤ session.reply.highEnd
      rw [geometry.reply.baseEq, shape.sequence, TCPHandshakeRecovery.Kind.sequence, Seq.distance_self]
      exact Nat.zero_le _
  · rw [role, shape.actorEq]
    rcases ackKind with rfl | rfl
    · change Seq.distance session.reply.base packet.packet.segment.acknowledgment ≤ session.reply.observed
      rw [geometry.reply.baseEq, shape.acknowledgment, TCPHandshakeRecovery.Kind.acknowledgment, Seq.distance_self]
      exact Nat.zero_le _
    · change Seq.distance session.original.base packet.packet.segment.acknowledgment ≤ session.original.observed
      rw [geometry.original.baseEq, shape.acknowledgment, TCPHandshakeRecovery.Kind.acknowledgment, Seq.distance_self]
      exact Nat.zero_le _
  · rw [role, shape.actorEq]
    rcases ackKind with rfl | rfl
    · change session.reply.acknowledged ≤ _
      rw [geometry.reply.acknowledged]
      exact Nat.zero_le _
    · change session.original.acknowledged ≤ _
      rw [geometry.original.acknowledged]
      exact Nat.zero_le _

theorem syn_allowed (coordinates : Coordinates active passive phase)
    (shape : C.PacketShape active passive actor .syn packet)
    (selected : phase.entry = some entry) (entryEq : attachment.entry = entry) (existing : attachment.fresh = false)
    (role : attachment.direction = sideDirection actor)
    (known : AdmissionStartupRecovery.KnownControl observations entry .original packet.packet.segment) :
    AdmissionStartupRecovery.Allowed phase attachment packet.packet.segment observations := by
  have direction : attachment.direction = .original := by simpa only [shape.actorEq, TCPHandshakeRecovery.Kind.actor, sideDirection] using role
  have profile := startup shape
  cases phase with
  | empty => cases selected
  | syn old iss window mss =>
    cases selected
    apply Or.inr
    refine ⟨entryEq, existing, Or.inl ⟨direction, ⟨profile, ?_, ?_, known⟩, ?_⟩⟩
    · exact shape.sequence.trans coordinates.sequence.symm
    · rw [shape.options, TCPHandshakeRecovery.Kind.options, coordinates.offer]
      exact Handshake.options_selected active
    · exact Fin.eq_of_val_eq (shape.capacity.trans coordinates.capacity.symm)
  | synAck old clientISS clientWindow serverISS serverWindow clientMSS serverMSS =>
    cases selected
    apply Or.inr
    refine ⟨entryEq, existing, Or.inl ⟨direction, ⟨profile, ?_, ?_, known⟩, ?_⟩⟩
    · exact shape.sequence.trans coordinates.client.sequence.symm
    · rw [shape.options, TCPHandshakeRecovery.Kind.options, coordinates.client.offer]
      exact Handshake.options_selected active
    · exact Fin.eq_of_val_eq (shape.capacity.trans coordinates.client.capacity.symm)
  | data session =>
    cases selected
    apply Or.inr
    refine ⟨entryEq, existing, Or.inl ⟨direction, ⟨profile, ?_, ?_, known⟩⟩⟩
    · rw [Admission.Lane.controlOrigin, coordinates.original.baseEq, Admission.control_inverse]
      exact shape.sequence
    · rw [shape.options, TCPHandshakeRecovery.Kind.options, coordinates.clientMSS]
      exact Handshake.options_selected active

theorem synAck_allowed (coordinates : Coordinates active passive phase)
    (shape : C.PacketShape active passive actor .synAck packet)
    (selected : phase.entry = some entry) (entryEq : attachment.entry = entry) (existing : attachment.fresh = false)
    (role : attachment.direction = sideDirection actor)
    (known : 2 ≤ CampusTCPRecoveryStartupTransport.phaseRank phase →
      AdmissionStartupRecovery.KnownControl observations entry .reply packet.packet.segment) :
    AdmissionStartupRecovery.Allowed phase attachment packet.packet.segment observations := by
  have direction : attachment.direction = .reply := by simpa only [shape.actorEq, TCPHandshakeRecovery.Kind.actor, sideDirection] using role
  have profile := startup shape
  cases phase with
  | empty => cases selected
  | syn old iss window mss =>
    cases selected
    exact Or.inl ⟨entryEq, existing, direction, profile, shape.acknowledgment.trans (congrArg (fun value : Seq => value.add 1) coordinates.sequence).symm⟩
  | synAck old clientISS clientWindow serverISS serverWindow clientMSS serverMSS =>
    cases selected
    apply Or.inr
    refine ⟨entryEq, existing, Or.inr ⟨direction, Or.inl ⟨⟨profile, ?_, ?_, ?_, known (by simp only [CampusTCPRecoveryStartupTransport.phaseRank]; decide)⟩, ?_⟩⟩⟩
    · exact shape.sequence.trans coordinates.server.sequence.symm
    · exact shape.acknowledgment.trans (congrArg (fun value : Seq => value.add 1) coordinates.client.sequence).symm
    · rw [shape.options, TCPHandshakeRecovery.Kind.options, coordinates.server.offer]
      exact Handshake.options_selected passive
    · exact Fin.eq_of_val_eq (shape.capacity.trans coordinates.server.capacity.symm)
  | data session =>
    cases selected
    apply Or.inr
    refine ⟨entryEq, existing, Or.inr ⟨direction, ⟨profile, ?_, ?_, ?_, known (by simp only [CampusTCPRecoveryStartupTransport.phaseRank]; decide)⟩⟩⟩
    · rw [Admission.Lane.controlOrigin, coordinates.reply.baseEq, Admission.control_inverse]
      exact shape.sequence
    · rw [Admission.Lane.controlOrigin, coordinates.original.baseEq, Admission.control_inverse]
      exact shape.acknowledgment
    · rw [shape.options, TCPHandshakeRecovery.Kind.options, coordinates.serverMSS]
      exact Handshake.options_selected passive

theorem finalAck_allowed (coordinates : Coordinates active passive phase)
    (shape : C.PacketShape active passive actor .finalAck packet)
    (selected : phase.entry = some entry) (entryEq : attachment.entry = entry) (existing : attachment.fresh = false)
    (role : attachment.direction = sideDirection actor) (floor : 2 ≤ CampusTCPRecoveryStartupTransport.phaseRank phase) :
    AdmissionStartupRecovery.Allowed phase attachment packet.packet.segment observations := by
  have direction : attachment.direction = .original := by simpa only [shape.actorEq, TCPHandshakeRecovery.Kind.actor, sideDirection] using role
  cases phase with
  | empty => simp only [CampusTCPRecoveryStartupTransport.phaseRank] at floor; omega
  | syn old iss window mss => simp only [CampusTCPRecoveryStartupTransport.phaseRank] at floor; omega
  | synAck old clientISS clientWindow serverISS serverWindow clientMSS serverMSS =>
    cases selected
    exact Or.inl ⟨entryEq, existing, direction, startup shape,
      shape.sequence.trans (congrArg (fun value : Seq => value.add 1) coordinates.client.sequence).symm,
      shape.acknowledgment.trans (congrArg (fun value : Seq => value.add 1) coordinates.server.sequence).symm⟩
  | data session =>
    cases selected
    exact Or.inl (data_ack coordinates shape (Or.inl rfl) entryEq existing role)

theorem replyAck_allowed (coordinates : Coordinates active passive phase)
    (shape : C.PacketShape active passive actor .synReplyAck packet)
    (selected : phase.entry = some entry) (entryEq : attachment.entry = entry) (existing : attachment.fresh = false)
    (role : attachment.direction = sideDirection actor) :
    AdmissionStartupRecovery.Allowed phase attachment packet.packet.segment observations := by
  have direction : attachment.direction = .reply := by simpa only [shape.actorEq, TCPHandshakeRecovery.Kind.actor, sideDirection] using role
  cases phase with
  | empty => cases selected
  | syn old iss window mss =>
    cases selected
    exact AdmissionStartupRecovery.Allowed.bare_syn entryEq existing direction (startup shape)
      (shape.acknowledgment.trans (congrArg (fun value : Seq => value.add 1) coordinates.sequence).symm)
  | synAck old clientISS clientWindow serverISS serverWindow clientMSS serverMSS =>
    cases selected
    exact AdmissionStartupRecovery.Allowed.bare_synAck entryEq existing direction (startup shape)
      (shape.acknowledgment.trans (congrArg (fun value : Seq => value.add 1) coordinates.client.sequence).symm)
      (shape.sequence.trans (congrArg (fun value : Seq => value.add 1) coordinates.server.sequence).symm)
      (Fin.eq_of_val_eq (shape.capacity.trans coordinates.server.capacity.symm))
  | data session =>
    cases selected
    exact Or.inl (data_ack coordinates shape (Or.inr rfl) entryEq existing role)

theorem existing_allowed (coordinates : Coordinates active passive phase)
    (shape : C.PacketShape active passive actor kind packet)
    (selected : phase.entry = some entry) (entryEq : attachment.entry = entry) (existing : attachment.fresh = false)
    (role : attachment.direction = sideDirection actor)
    (floor : requiredLevel kind ≤ CampusTCPRecoveryStartupTransport.phaseRank phase)
    (syn : kind = .syn → AdmissionStartupRecovery.KnownControl observations entry .original packet.packet.segment)
    (synAck : kind = .synAck → 2 ≤ CampusTCPRecoveryStartupTransport.phaseRank phase →
      AdmissionStartupRecovery.KnownControl observations entry .reply packet.packet.segment) :
    AdmissionStartupRecovery.Allowed phase attachment packet.packet.segment observations := by
  cases kind with
  | syn => exact syn_allowed coordinates shape selected entryEq existing role (syn rfl)
  | synAck => exact synAck_allowed coordinates shape selected entryEq existing role (synAck rfl)
  | finalAck => exact finalAck_allowed coordinates shape selected entryEq existing role floor
  | synReplyAck => exact replyAck_allowed coordinates shape selected entryEq existing role

end Netlib.Check.CampusTCPRecoveryStartupAdmissionGuards
