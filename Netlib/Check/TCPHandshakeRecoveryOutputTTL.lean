import Netlib.Check.TCPHandshakeRecovery

/-!
# Source TTLs in startup recovery

Fresh controls start with TTL 64. Retries retain their actual source packet.
-/

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

def OutputTTL (state : State active passive) : Prop :=
  ∀ output ∈ state.emissions, 1 < output.packet.packet.ip.packet.ttl.toNat

theorem OutputTTL.initial : OutputTTL (State.initial : State active passive) := by
  intro output member
  cases member

theorem OutputTTL.frame (prior : OutputTTL before) (emissions : after.emissions = before.emissions) : OutputTTL after := by
  intro output member
  rw [emissions] at member
  exact prior output member

theorem OutputTTL.publish (prior : OutputTTL state) (output : Emission)
    (ttl : 1 < output.packet.packet.ip.packet.ttl.toNat) : OutputTTL (publish state output).state := by
  intro selected member
  rcases List.mem_append.mp member with old | fresh
  · exact prior selected old
  · exact List.mem_singleton.mp fresh ▸ ttl

theorem OutputTTL.source (prior : OutputTTL state) (found : state.source index = some output) :
    1 < output.packet.packet.ip.packet.ttl.toNat := prior output (List.mem_of_find?_eq_some found)

theorem SynSent.output_ttl (pending : Handshake.SynSent) : pending.output.packet.ip.packet.ttl.toNat = 64 := by
  rw [(ControlOutput.emitWithMSS_fields _ _ _ _ _ _ _ pending.generated).2.2.2.2.2]
  rfl

theorem SynReceived.output_ttl (pending : Handshake.SynReceived) : pending.output.packet.ip.packet.ttl.toNat = 64 := by
  rw [(ControlOutput.emitWithMSS_fields _ _ _ _ _ _ _ pending.generated).2.2.2.2.2]
  rfl

theorem ActiveEstablished.output_ttl (ready : Handshake.ActiveEstablished pending packet) : ready.output.packet.ip.packet.ttl.toNat = 64 := by
  rw [(Output.emit_fields _ _ _ ready.outputGenerated).2.2.2]
  rfl

end Netlib.Check.TCPHandshakeRecovery
