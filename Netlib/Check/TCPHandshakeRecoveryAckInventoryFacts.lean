import Netlib.Check.TCPHandshakeRecoveryInvariant
import Netlib.Check.TCPHandshakeRecoveryAckTemplates

/-!
# Exact ACK templates from the actual startup trace

Repeated responses keep their own occurrence indices and canonical bytes.
-/

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

variable {active passive : H.Local} {before final : State active passive}
variable {actual : Step active passive} {events : List Event} {steps : List (Step active passive)}
variable {first second output : Emission}

theorem AckInventory.step (inventory : AckInventory actual.before) (prior : PhaseInvariant actual.before) :
    AckInventory actual.result.state := evaluate_ack_inventory prior inventory actual.computed

theorem Trace.ack_inventory (trace : Trace before events steps final) (prior : PhaseInvariant before)
    (inventory : AckInventory before) : AckInventory final := by
  induction trace with
  | done => exact inventory
  | next actual tail ih => exact ih (actual.phase_invariant prior) (inventory.step prior)

theorem Reachable.ack_inventory (reachable : Reachable final) : AckInventory final :=
  reachable.trace.ack_inventory PhaseInvariant.initial AckInventory.initial

theorem AckInventory.same_template (inventory : AckInventory before)
    (firstMember : first ∈ before.emissions) (secondMember : second ∈ before.emissions)
    (ack : AckKind first.kind) (kind : first.kind = second.kind) : first.packet = second.packet := by
  have left := inventory.templates first firstMember ack
  have right := inventory.templates second secondMember (kind ▸ ack)
  rw [kind] at left
  exact Option.some.inj (left.symm.trans right)

theorem Reachable.same_ack_template (reachable : Reachable final)
    (firstMember : first ∈ final.emissions) (secondMember : second ∈ final.emissions)
    (ack : AckKind first.kind) (kind : first.kind = second.kind) : first.packet = second.packet :=
  reachable.ack_inventory.same_template firstMember secondMember ack kind

theorem AckInventory.acknowledged_finalAck (inventory : AckInventory before)
    {acknowledged : O.Acknowledged active passive} {client : PreData acknowledged.ready.seed}
    (phase : before.phase = .acknowledged acknowledged client) (member : output ∈ before.emissions)
    (kind : output.kind = .finalAck) : output.packet = acknowledged.ready.output := by
  have template := inventory.templates output member (Or.inl kind)
  rw [phase, kind, Phase.ackTemplate] at template
  exact (Option.some.inj template).symm

theorem AckInventory.acknowledged_synReplyAck (inventory : AckInventory before)
    {acknowledged : O.Acknowledged active passive} {client : PreData acknowledged.ready.seed}
    (phase : before.phase = .acknowledged acknowledged client) (member : output ∈ before.emissions)
    (kind : output.kind = .synReplyAck) :
    output.packet = (HandshakeDuplicate.syn_received_ack acknowledged.answered.pending).output := by
  have template := inventory.templates output member (Or.inr kind)
  rw [phase, kind, Phase.ackTemplate] at template
  exact (Option.some.inj template).symm

theorem Reachable.acknowledged_finalAck_template (reachable : Reachable final)
    {acknowledged : O.Acknowledged active passive} {client : PreData acknowledged.ready.seed}
    (phase : final.phase = .acknowledged acknowledged client) (member : output ∈ final.emissions)
    (kind : output.kind = .finalAck) : output.packet = acknowledged.ready.output :=
  reachable.ack_inventory.acknowledged_finalAck phase member kind

theorem Reachable.acknowledged_synReplyAck_template (reachable : Reachable final)
    {acknowledged : O.Acknowledged active passive} {client : PreData acknowledged.ready.seed}
    (phase : final.phase = .acknowledged acknowledged client) (member : output ∈ final.emissions)
    (kind : output.kind = .synReplyAck) :
    output.packet = (HandshakeDuplicate.syn_received_ack acknowledged.answered.pending).output :=
  reachable.ack_inventory.acknowledged_synReplyAck phase member kind

theorem Reachable.complete_finalAck_template (reachable : Reachable final)
    {complete : O.Completed active passive}
    {client : PreData complete.certificate.activeSeed} {server : PreData complete.certificate.passiveSeed}
    (phase : final.phase = .complete complete client server) (member : output ∈ final.emissions)
    (kind : output.kind = .finalAck) : output.packet = complete.certificate.active.output :=
  reachable.ack_inventory.complete_finalAck phase member kind

theorem Reachable.complete_synReplyAck_template (reachable : Reachable final)
    {complete : O.Completed active passive}
    {client : PreData complete.certificate.activeSeed} {server : PreData complete.certificate.passiveSeed}
    (phase : final.phase = .complete complete client server) (member : output ∈ final.emissions)
    (kind : output.kind = .synReplyAck) :
    output.packet = (HandshakeDuplicate.syn_received_ack complete.certificate.passivePending).output :=
  reachable.ack_inventory.complete_synReplyAck phase member kind

end Netlib.Check.TCPHandshakeRecovery
