import Netlib.Check.TCPHandshakeRecoveryInvariant
import Netlib.Check.TCPHandshakeRecoveryPhaseOrder

/-!
# Ordered milestones from the actual recovery trace

Every retained occurrence remains bounded by the actual last event.
-/

namespace Netlib.Check.TCPHandshakeRecovery

variable {active passive : H.Local} {before final : State active passive}
variable {actual : Step active passive} {events : List Event} {steps : List (Step active passive)}

theorem PhaseOrder.step (prior : PhaseOrder actual.before) : PhaseOrder actual.result.state :=
  evaluate_phase_order prior actual.computed

theorem Trace.phase_order (trace : Trace before events steps final) (prior : PhaseOrder before) :
    PhaseOrder final := by
  induction trace with
  | done => exact prior
  | next actual tail ih => exact ih prior.step

theorem Reachable.phase_order (reachable : Reachable final) : PhaseOrder final :=
  reachable.trace.phase_order PhaseOrder.initial

theorem Trace.last_origin (trace : Trace before events steps final) (last : final.last = some index) :
    before.last = some index ∨ ∃ actual ∈ steps, actual.index = index := by
  induction trace with
  | done => exact Or.inl last
  | next actual tail ih =>
    rcases ih last with prior | ⟨selected, member, stamp⟩
    · exact Or.inr ⟨actual, List.mem_cons_self, Option.some.inj (actual.last.symm.trans prior)⟩
    · exact Or.inr ⟨selected, List.mem_cons_of_mem actual member, stamp⟩

theorem Reachable.last_origin (reachable : Reachable final) (last : final.last = some index) :
    ∃ actual ∈ reachable.steps, actual.index = index := by
  rcases reachable.trace.last_origin last with initial | actual
  · cases initial
  · exact actual

theorem Reachable.emission_before_last (reachable : Reachable final) (member : output ∈ final.emissions) :
    ∃ last, final.last = some last ∧ output.index ≤ last :=
  reachable.history.emissionPast output member

theorem Reachable.receipt_before_last (reachable : Reachable final) (member : receipt ∈ final.receipts) :
    ∃ last, final.last = some last ∧ receipt.index ≤ last :=
  reachable.history.receiptPast receipt member

end Netlib.Check.TCPHandshakeRecovery
