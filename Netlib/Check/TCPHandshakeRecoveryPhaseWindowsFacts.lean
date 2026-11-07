import Netlib.Check.TCPHandshakeRecoveryInvariant
import Netlib.Check.TCPHandshakeRecoveryOutputShapeFacts
import Netlib.Check.TCPHandshakeRecoveryPhaseWindows

/-!
# Peer windows from the actual recovery trace

The current endpoint windows retain peer capacity through every startup ACK.
Window sequence markers remain the actual values selected by each receive.
-/

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

variable {active passive : H.Local}
variable {before final : State active passive} {actual : Step active passive}
variable {events : List Event} {steps : List (Step active passive)}

theorem PhaseWindows.step (prior : PhaseWindows actual.before) (invariant : PhaseInvariant actual.before)
    (inventory : OutputInventory actual.before) : PhaseWindows actual.result.state :=
  evaluate_phase_windows invariant inventory prior actual.computed

theorem Trace.phase_windows (trace : Trace before events steps final) (invariant : PhaseInvariant before)
    (inventory : OutputInventory before) (prior : PhaseWindows before) : PhaseWindows final := by
  induction trace with
  | done => exact prior
  | next actual tail ih => exact ih (actual.phase_invariant invariant) (inventory.step invariant) (prior.step invariant inventory)

theorem Reachable.phase_windows (reachable : Reachable final) : PhaseWindows final :=
  reachable.trace.phase_windows PhaseInvariant.initial OutputInventory.initial PhaseWindows.initial

theorem Reachable.acknowledged_window (reachable : Reachable final) {acknowledged : O.Acknowledged active passive}
    {client : PreData acknowledged.ready.seed} (phase : final.phase = .acknowledged acknowledged client) :
    client.current.sendWindow = passive.capacity := by
  simpa only [PhaseWindows, phase] using reachable.phase_windows

theorem Reachable.complete_windows (reachable : Reachable final) {complete : O.Completed active passive}
    {client : PreData complete.certificate.activeSeed} {server : PreData complete.certificate.passiveSeed}
    (phase : final.phase = .complete complete client server) :
    client.current.sendWindow = passive.capacity ∧ server.current.sendWindow = active.capacity := by
  simpa only [PhaseWindows, phase] using reachable.phase_windows

end Netlib.Check.TCPHandshakeRecovery
