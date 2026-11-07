import Netlib.Protocol.TCP.AdmissionExecution
import Netlib.Protocol.TCP.AdmissionMSSFacts

/-!
# Advancing controls in either admission mode

Current phase, flags, and direction distinguish advancing controls from stutters.
Legacy witnesses retain the actual result state.
-/

namespace Netlib.Protocol.TCP.AdmissionExecution

open Admission

theorem Result.legacy_empty (result : Result mode before input lifecycle prepared) (empty : before.phase = .empty) :
    Admission.Allowed before.phase prepared.attachment input.packet.segment before.observations := by
  rcases Result.legacy_or_stutter result with legacy | ⟨_, stutter⟩
  · exact legacy
  · rw [empty] at stutter
    cases stutter

theorem Result.legacy_synAck_control (result : Result mode before input lifecycle prepared)
    (pending : before.phase = .syn entry clientISS clientWindow clientMSS)
    (flags : input.packet.segment.flags = 18) :
    Admission.Allowed before.phase prepared.attachment input.packet.segment before.observations := by
  rcases Result.legacy_or_stutter result with legacy | ⟨_, stutter⟩
  · exact legacy
  · rw [pending] at stutter
    rcases stutter.2.2 with ⟨_, syn, _⟩ | ⟨_, reply⟩
    · exact False.elim ((by decide : (18 : UInt8) ≠ 2) (flags.symm.trans syn.1.1))
    · exact False.elim ((by decide : (18 : UInt8) ≠ 16) (flags.symm.trans reply.1.1))

theorem Result.legacy_finalAck_control (result : Result mode before input lifecycle prepared)
    (pending : before.phase = .synAck entry clientISS clientWindow serverISS serverWindow clientMSS serverMSS)
    (original : prepared.attachment.direction = .original) (flags : input.packet.segment.flags = 16) :
    Admission.Allowed before.phase prepared.attachment input.packet.segment before.observations := by
  rcases Result.legacy_or_stutter result with legacy | ⟨_, stutter⟩
  · exact legacy
  · rw [pending] at stutter
    rcases stutter.2.2 with ⟨_, syn, _⟩ | ⟨reply, _⟩
    · exact False.elim ((by decide : (16 : UInt8) ≠ 2) (flags.symm.trans syn.1.1))
    · have impossible := original.symm.trans reply
      cases impossible

theorem Result.ordinary_legacy (result : Result mode before input lifecycle prepared) (ordinary : mode = .ordinary) :
    Admission.Allowed before.phase prepared.attachment input.packet.segment before.observations := by
  subst mode
  exact result.admitted

theorem Result.learned_syn (result : Result mode before input lifecycle prepared) (empty : before.phase = .empty) :
    ∃ offer, MSS.readStartup input.packet.segment.options = .ok offer ∧
      (Result.state result).phase = .syn prepared.attachment.entry input.packet.segment.sequence input.packet.segment.window offer := by
  have learned := Admission.Result.learned_syn (Result.asLegacy result (result.legacy_empty empty)) empty
  simpa only [Result.asLegacy_state] using learned

theorem Result.learned_synAck_control (result : Result mode before input lifecycle prepared)
    (pending : before.phase = .syn entry clientISS clientWindow clientMSS)
    (flags : input.packet.segment.flags = 18) :
    ∃ offer, MSS.readStartup input.packet.segment.options = .ok offer ∧
      (Result.state result).phase = .synAck entry clientISS clientWindow input.packet.segment.sequence
        input.packet.segment.window clientMSS offer := by
  have learned := Admission.Result.learned_synAck (Result.asLegacy result (result.legacy_synAck_control pending flags)) pending
  simpa only [Result.asLegacy_state] using learned

end Netlib.Protocol.TCP.AdmissionExecution
