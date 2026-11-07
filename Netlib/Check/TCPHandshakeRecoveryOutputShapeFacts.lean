import Netlib.Check.TCPHandshakeRecoveryInvariant
import Netlib.Check.TCPHandshakeRecoveryOutputShape

/-!
# Shapes of actual recovery occurrences

The inventory follows the same checked trace without changing occurrence indices.
Rewritten receipts retain the control fields of their actual source.
-/

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

variable {active passive : H.Local}
variable {before final : State active passive} {actual : Step active passive} {output : Emission}
variable {events : List Event} {steps : List (Step active passive)}

theorem Step.output_shape (actual : Step active passive) (prior : PhaseInvariant actual.before)
    (inventory : OutputInventory actual.before) (recorded : actual.result.output = some output) :
    OutputShape active passive output := evaluate_output_shape prior inventory actual.computed recorded

theorem OutputInventory.step (inventory : OutputInventory actual.before) (prior : PhaseInvariant actual.before) :
    OutputInventory actual.result.state := by
  intro output member
  rw [actual.records.emissions] at member
  rcases List.mem_append.mp member with old | fresh
  · exact inventory output old
  · have recorded : actual.result.output = some output := by simpa only [Option.mem_toList] using fresh
    exact actual.output_shape prior inventory recorded

theorem Trace.output_inventory (trace : Trace before events steps final) (prior : PhaseInvariant before)
    (inventory : OutputInventory before) : OutputInventory final := by
  induction trace with
  | done => exact inventory
  | next actual tail ih => exact ih (actual.phase_invariant prior) (inventory.step prior)

theorem Reachable.output_inventory (reachable : Reachable final) : OutputInventory final :=
  reachable.trace.output_inventory PhaseInvariant.initial OutputInventory.initial

theorem Reachable.output_shape (reachable : Reachable final) (member : output ∈ final.emissions) :
    OutputShape active passive output := reachable.output_inventory output member

theorem Reachable.source_shape (reachable : Reachable final) (found : final.source source = some output) :
    OutputShape active passive output := reachable.output_inventory.source_shape found

structure ShapedOutputOrigin (steps : List (Step active passive)) (output : Emission) where
  origin : EmissionOrigin steps output
  shape : OutputShape active passive output

theorem Reachable.shaped_output_origin (reachable : Reachable final) (member : output ∈ final.emissions) :
    Nonempty (ShapedOutputOrigin reachable.steps output) := by
  obtain ⟨origin⟩ := reachable.trace.output_origin member
  exact ⟨⟨origin, reachable.output_shape member⟩⟩

theorem PacketShape.path (shape : PacketShape active passive actor kind source)
    (path : ApplicationTrace.BytePath source target) : PacketShape active passive actor kind target := by
  have fields := path.fields
  have control := path.control_fields
  refine ⟨shape.actorEq, ?_, fields.2.trans shape.sequence, control.1.trans shape.acknowledgment,
    (congrArg (fun window : Protocol.InternetChecksum.Word => window.val) control.2.2.1).trans shape.capacity, control.2.2.2.trans shape.options⟩
  refine ⟨control.2.1.trans shape.profile.1, ?_, fields.1.trans shape.payload⟩
  unfold Handshake.optionProfile
  rw [control.2.2.2]
  exact shape.profile.2.1

theorem Reachable.receipt_shape (reachable : Reachable final) (member : receipt ∈ final.receipts) :
    PacketShape active passive receipt.source.actor receipt.source.kind receipt.delivery.input :=
  (reachable.output_shape (reachable.history.source_member receipt member)).path receipt.delivery.path

end Netlib.Check.TCPHandshakeRecovery
