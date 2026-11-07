import Netlib.Protocol.TCP.Handshake

/-!
# Startup operations from current local and packet fields

Valid local limits and the actual received tuple, profile, and cursors supply
the checked operation. No future startup result is an input.
-/

namespace Netlib.Protocol.TCP.Handshake

theorem activeOpen_enabled (config : Local) (remote : Socket) (valid : config.Valid) :
    ∃ pending, activeOpen config remote true = .ok pending := by
  obtain ⟨output, generated⟩ := ControlOutput.emitWithMSS_exists (outbound config remote) config.iss
    (Seq.ofNat 0) 2 config.capacity (advertised config) rfl (by decide) valid.1 (fun _ => Or.inl rfl)
  simp only [activeOpen, valid, dite_true, ite_true]
  split
  · rename_i reason failed
    rw [generated] at failed
    cases failed
  · exact ⟨_, rfl⟩

theorem listenSyn_enabled (config : Local) (packet : Input) (valid : config.Valid)
    (tuple : destination config packet) (profile : Profile packet 2) :
    ∃ pending, listenSyn config packet true = .ok pending := by
  obtain ⟨peer, selected⟩ := profile.selection (by decide : (2 : UInt8) ≠ 16)
  obtain ⟨output, generated⟩ := ControlOutput.emitWithMSS_exists (Output.reverse packet.packet.header) config.iss
    (packet.packet.segment.sequence.add 1) 18 config.capacity (advertised config) rfl (by decide) valid.1 (fun _ => Or.inr rfl)
  simp only [listenSyn, valid, tuple, profile, dite_true, ite_true]
  split
  · rename_i reason failed
    rw [selected] at failed
    cases failed
  · split
    · rename_i reason failed
      rw [generated] at failed
      cases failed
    · exact ⟨_, rfl⟩

theorem synSentSynAck_enabled (pending : SynSent) (packet : Input) (accepted : ActiveAccepted pending packet) :
    ∃ ready, synSentSynAck pending packet true = .ok ready := by
  obtain ⟨peer, selected⟩ := accepted.2.1.selection (by decide : (18 : UInt8) ≠ 16)
  obtain ⟨output, generated⟩ := Output.emit_exists (activeSeed pending packet peer).core []
    (activeSeed_valid pending packet peer).1 (by decide)
  simp only [synSentSynAck, accepted.1, accepted.2.1, accepted.2.2, dite_true, ite_true]
  split
  · rename_i reason failed
    rw [selected] at failed
    cases failed
  · rename_i actualPeer actualSelected
    have same : actualPeer = peer := Except.ok.inj (actualSelected.symm.trans selected)
    subst actualPeer
    split
    · rename_i reason failed
      rw [generated] at failed
      cases failed
    · exact ⟨_, rfl⟩

theorem synReceivedAck_enabled (pending : SynReceived) (packet : Input) (accepted : PassiveAccepted pending packet) :
    ∃ ready, synReceivedAck pending packet = .ok ready := by
  simp only [synReceivedAck, accepted.1, accepted.2.1, accepted.2.2.1, accepted.2.2.2]
  exact ⟨_, rfl⟩

end Netlib.Protocol.TCP.Handshake
