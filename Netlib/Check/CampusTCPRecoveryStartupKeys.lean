import Netlib.Check.CampusTCPRecoveryStartupPhase
import Netlib.Check.CampusTCPStartupBasis

/-!
# Startup directions and exact endpoint keys

SYN controls determine their directions from real admission. Once their
actual endpoint keys are known, key distinctness determines each ACK role.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupKeys

open Packet Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupPhase (sideDirection)

namespace C
export TCPHandshakeRecovery (Side)
end C

private theorem not_data (flags : segment.flags = expected) (notAck : expected ≠ 16) (notPush : expected ≠ 24) :
    ¬ Admission.DataProfile segment := by
  rintro ⟨actual | actual, _⟩
  · exact notAck (flags.symm.trans actual)
  · exact notPush (flags.symm.trans actual)

theorem syn_original (result : AdmissionExecution.Result mode before packet lifecycle prepared)
    (flags : packet.packet.segment.flags = 2) : prepared.attachment.direction = .original := by
  rcases AdmissionExecution.Result.legacy_or_stutter result with legacy | ⟨_, stutter⟩
  · cases phase : before.phase with
    | empty =>
      simp only [Admission.Allowed, phase] at legacy
      exact legacy.2.1
    | syn entry iss window mss =>
      simp only [Admission.Allowed, phase] at legacy
      have control : packet.packet.segment.flags = 18 := by simpa only [Admission.Allowed, phase] using legacy.2.2.2.1.1
      exact False.elim ((by decide : (2 : UInt8) ≠ 18) (flags.symm.trans control))
    | synAck entry clientISS clientWindow serverISS serverWindow clientMSS serverMSS =>
      simp only [Admission.Allowed, phase] at legacy
      have control : packet.packet.segment.flags = 16 := by simpa only [Admission.Allowed, phase] using legacy.2.2.2.1.1
      exact False.elim ((by decide : (2 : UInt8) ≠ 16) (flags.symm.trans control))
    | data session =>
      simp only [Admission.Allowed, phase] at legacy
      have allowed := legacy.2.2
      cases direction : prepared.attachment.direction <;> simp only [direction] at allowed
      all_goals rcases allowed with admitted | admitted
      all_goals exact False.elim (not_data flags (by decide) (by decide) (by exact admitted.1))
  · cases phase : before.phase with
    | empty => rw [phase] at stutter; cases stutter
    | syn entry iss window mss =>
      rw [phase] at stutter
      rcases stutter.2.2 with ⟨direction, _⟩ | ⟨_, bare⟩
      · exact direction
      · exact False.elim ((by decide : (2 : UInt8) ≠ 16) (flags.symm.trans bare.1.1))
    | synAck entry clientISS clientWindow serverISS serverWindow clientMSS serverMSS =>
      rw [phase] at stutter
      rcases stutter.2.2 with ⟨direction, _⟩ | ⟨_, ⟨control, _⟩ | ⟨bare, _⟩⟩
      · exact direction
      · exact False.elim ((by decide : (2 : UInt8) ≠ 18) (flags.symm.trans control.1.1))
      · exact False.elim ((by decide : (2 : UInt8) ≠ 16) (flags.symm.trans bare.1.1))
    | data session =>
      rw [phase] at stutter
      rcases stutter.2.2 with ⟨direction, _⟩ | ⟨_, control⟩
      · exact direction
      · exact False.elim ((by decide : (2 : UInt8) ≠ 18) (flags.symm.trans control.1.1))

theorem synAck_reply (result : AdmissionExecution.Result mode before packet lifecycle prepared)
    (flags : packet.packet.segment.flags = 18) : prepared.attachment.direction = .reply := by
  rcases AdmissionExecution.Result.legacy_or_stutter result with legacy | ⟨_, stutter⟩
  · cases phase : before.phase with
    | empty =>
      simp only [Admission.Allowed, phase] at legacy
      have control : packet.packet.segment.flags = 2 := by simpa only [Admission.Allowed, phase] using legacy.2.2.1
      exact False.elim ((by decide : (18 : UInt8) ≠ 2) (flags.symm.trans control))
    | syn entry iss window mss =>
      simp only [Admission.Allowed, phase] at legacy
      exact legacy.2.2.1
    | synAck entry clientISS clientWindow serverISS serverWindow clientMSS serverMSS =>
      simp only [Admission.Allowed, phase] at legacy
      have control : packet.packet.segment.flags = 16 := by simpa only [Admission.Allowed, phase] using legacy.2.2.2.1.1
      exact False.elim ((by decide : (18 : UInt8) ≠ 16) (flags.symm.trans control))
    | data session =>
      simp only [Admission.Allowed, phase] at legacy
      have allowed := legacy.2.2
      cases direction : prepared.attachment.direction <;> simp only [direction] at allowed
      all_goals rcases allowed with admitted | admitted
      all_goals exact False.elim (not_data flags (by decide) (by decide) (by exact admitted.1))
  · cases phase : before.phase with
    | empty => rw [phase] at stutter; cases stutter
    | syn entry iss window mss =>
      rw [phase] at stutter
      rcases stutter.2.2 with ⟨_, control, _⟩ | ⟨_, bare⟩
      · exact False.elim ((by decide : (18 : UInt8) ≠ 2) (flags.symm.trans control.1.1))
      · exact False.elim ((by decide : (18 : UInt8) ≠ 16) (flags.symm.trans bare.1.1))
    | synAck entry clientISS clientWindow serverISS serverWindow clientMSS serverMSS =>
      rw [phase] at stutter
      rcases stutter.2.2 with ⟨_, control, _⟩ | ⟨direction, _⟩
      · exact False.elim ((by decide : (18 : UInt8) ≠ 2) (flags.symm.trans control.1.1))
      · exact direction
    | data session =>
      rw [phase] at stutter
      rcases stutter.2.2 with ⟨_, control⟩ | ⟨direction, _⟩
      · exact False.elim ((by decide : (18 : UInt8) ≠ 2) (flags.symm.trans control.1.1))
      · exact direction

def sideHeader (complete : H.Completed active passive) : C.Side → Header
  | .active => Output.reverse complete.certificate.activeSeed.core.inbound
  | .passive => Output.reverse complete.certificate.passiveSeed.core.inbound

structure TupleKeys (input : Input) (complete : H.Completed input.active input.passive) (entry : NetfilterNAT.Entry) : Prop where
  originalZone : entry.flow.originalZone = input.zone
  replyZone : entry.flow.replyZone = input.zone
  original : entry.flow.input .original = sideHeader complete .active
  reply : entry.flow.input .reply = sideHeader complete .passive

variable {input : Input} {complete : H.Completed input.active input.passive} {entry : NetfilterNAT.Entry}
variable {packet : EstablishedReceive.Input} {actor : C.Side} {selectedDirection : FlowNAT.Direction} {session : Admission.Session}

theorem TupleKeys.key (keys : TupleKeys input complete entry) (actor : C.Side) :
    entry.flow.key (sideDirection actor) = (input.zone, sideHeader complete actor) := by
  cases actor
  · exact Prod.ext keys.originalZone keys.original
  · exact Prod.ext keys.replyZone keys.reply

theorem direction_of_key (compatible : entry.Compatible)
    (same : entry.flow.key actual = entry.flow.key expected) : actual = expected := by
  obtain ⟨_, _, _, _, _, distinct⟩ := compatible.1
  cases actual <;> cases expected
  · rfl
  · exact False.elim (distinct same)
  · exact False.elim (distinct same.symm)
  · rfl

theorem TupleKeys.direction (keys : TupleKeys input complete entry) (compatible : entry.Compatible)
    (selected : entry.flow.key selectedDirection = (input.zone, packet.packet.header))
    (header : packet.packet.header = sideHeader complete actor) : selectedDirection = sideDirection actor := by
  apply direction_of_key compatible
  rw [selected, header, keys.key actor]

theorem TupleKeys.static (keys : TupleKeys input complete entry)
    (geometry : CampusTCPRecoveryStartupGeometry.Geometry input.active input.passive session) (selected : session.entry = entry) :
    CampusTCPStartupBasis.StaticAlignment input complete entry session := by
  refine ⟨selected, geometry.clientMSS, geometry.serverMSS, keys.originalZone, keys.replyZone,
    keys.original.symm, keys.reply.symm, ?_, ?_⟩
  · change complete.certificate.activeSeed.core.inbound = (entry.flow.input .original).reverse
    rw [keys.original]
    exact (Header.reverse_reverse _).symm
  · change complete.certificate.passiveSeed.core.inbound = (entry.flow.input .reply).reverse
    rw [keys.reply]
    exact (Header.reverse_reverse _).symm

end Netlib.Check.CampusTCPRecoveryStartupKeys
