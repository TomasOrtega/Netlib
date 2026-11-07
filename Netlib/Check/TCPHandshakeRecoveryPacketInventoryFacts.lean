import Netlib.Check.TCPHandshakeRecoveryInvariant
import Netlib.Check.TCPHandshakeRecoveryPacketInventory

/-!
# Exact packet inventory from the actual recovery trace

The inventory includes every actual emission, with its original index and cause.
Complete headers use the checked seeds; retries keep the whole control input.
-/

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

variable {active passive : H.Local}
variable {complete : O.Completed active passive}
variable {client : PreData complete.certificate.activeSeed} {server : PreData complete.certificate.passiveSeed}
variable {before final : State active passive} {actual : Step active passive}
variable {events : List Event} {steps : List (Step active passive)} {output first second : Emission}

theorem PacketInventory.step (inventory : PacketInventory actual.before) (prior : PhaseInvariant actual.before) :
    PacketInventory actual.result.state := evaluate_packet_inventory prior inventory actual.computed

theorem Trace.packet_inventory (trace : Trace before events steps final) (prior : PhaseInvariant before)
    (inventory : PacketInventory before) : PacketInventory final := by
  induction trace with
  | done => exact inventory
  | next actual tail ih => exact ih (actual.phase_invariant prior) (inventory.step prior)

theorem Reachable.packet_inventory (reachable : Reachable final) : PacketInventory final :=
  reachable.trace.packet_inventory PhaseInvariant.initial PacketInventory.initial

theorem Reachable.complete_active_header (reachable : Reachable final)
    (phase : final.phase = .complete complete client server) (member : output ∈ final.emissions)
    (actor : output.actor = .active) :
    output.packet.packet.header = Output.reverse complete.certificate.activeSeed.core.inbound :=
  reachable.packet_inventory.complete_active_header phase member actor

theorem Reachable.complete_passive_header (reachable : Reachable final)
    (phase : final.phase = .complete complete client server) (member : output ∈ final.emissions)
    (actor : output.actor = .passive) :
    output.packet.packet.header = Output.reverse complete.certificate.passiveSeed.core.inbound :=
  reachable.packet_inventory.complete_passive_header phase member actor

theorem Reachable.complete_syn_template (reachable : Reachable final)
    (phase : final.phase = .complete complete client server) (member : output ∈ final.emissions)
    (kind : output.kind = .syn) : output.packet = complete.certificate.activePending.output :=
  reachable.packet_inventory.complete_syn phase member kind

theorem Reachable.complete_synAck_template (reachable : Reachable final)
    (phase : final.phase = .complete complete client server) (member : output ∈ final.emissions)
    (kind : output.kind = .synAck) : output.packet = complete.certificate.passivePending.output :=
  reachable.packet_inventory.complete_synAck phase member kind

theorem PacketInventory.same_header (inventory : PacketInventory before)
    (firstMember : first ∈ before.emissions) (secondMember : second ∈ before.emissions)
    (actor : first.actor = second.actor) : first.packet.packet.header = second.packet.packet.header := by
  have left := inventory.headers first firstMember
  have right := inventory.headers second secondMember
  rw [actor] at left
  exact Option.some.inj (left.symm.trans right)

theorem PacketInventory.same_template (inventory : PacketInventory before)
    (firstMember : first ∈ before.emissions) (secondMember : second ∈ before.emissions)
    (control : TemplateKind first.kind) (kind : first.kind = second.kind) : first.packet = second.packet := by
  have left := inventory.templates first firstMember control
  have right := inventory.templates second secondMember (kind ▸ control)
  rw [kind] at left
  exact Option.some.inj (left.symm.trans right)

theorem Reachable.same_control_template (reachable : Reachable final)
    (firstMember : first ∈ final.emissions) (secondMember : second ∈ final.emissions)
    (control : TemplateKind first.kind) (kind : first.kind = second.kind) : first.packet = second.packet :=
  reachable.packet_inventory.same_template firstMember secondMember control kind

structure ControlTemplateOrigin (steps : List (Step active passive)) (output : Emission) (template : H.Input) where
  occurrence : EmissionOrigin steps output
  same : output.packet = template

theorem Reachable.complete_syn_origin (reachable : Reachable final)
    (phase : final.phase = .complete complete client server) (member : output ∈ final.emissions)
    (kind : output.kind = .syn) :
    Nonempty (ControlTemplateOrigin reachable.steps output complete.certificate.activePending.output) := by
  obtain ⟨origin⟩ := reachable.trace.output_origin member
  exact ⟨⟨origin, reachable.complete_syn_template phase member kind⟩⟩

theorem Reachable.complete_synAck_origin (reachable : Reachable final)
    (phase : final.phase = .complete complete client server) (member : output ∈ final.emissions)
    (kind : output.kind = .synAck) :
    Nonempty (ControlTemplateOrigin reachable.steps output complete.certificate.passivePending.output) := by
  obtain ⟨origin⟩ := reachable.trace.output_origin member
  exact ⟨⟨origin, reachable.complete_synAck_template phase member kind⟩⟩

end Netlib.Check.TCPHandshakeRecovery
