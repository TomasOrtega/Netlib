import Netlib.Check.TCPHandshakeRecoveryFacts
import Netlib.Check.TCPHandshakeRecoveryAvailability

/-!
# Retained output phases from the actual startup trace

Every occurrence keeps the phase floor of its actual emission.
-/

namespace Netlib.Check.TCPHandshakeRecovery

variable {active passive : H.Local} {initial final : State active passive}
variable {events : List Event} {steps : List (Step active passive)}
variable {actual : Step active passive} {output : Emission}

theorem Step.phase_level (actual : Step active passive) :
    phaseLevel actual.before.phase ≤ phaseLevel actual.result.state.phase :=
  evaluate_phase_level actual.computed

theorem Trace.phase_level (trace : Trace initial events steps final) : phaseLevel initial.phase ≤ phaseLevel final.phase := by
  induction trace with
  | done => exact Nat.le_refl _
  | next actual tail ih => exact Nat.le_trans actual.phase_level ih

theorem Availability.step (prior : Availability actual.before) : Availability actual.result.state :=
  evaluate_availability prior actual.computed

theorem Trace.availability (trace : Trace initial events steps final) (prior : Availability initial) : Availability final := by
  induction trace with
  | done => exact prior
  | next actual tail ih => exact ih prior.step

theorem Reachable.availability (reachable : Reachable final) : Availability final :=
  reachable.trace.availability Availability.initial

theorem Reachable.output_phase (reachable : Reachable final) (member : output ∈ final.emissions) :
    output.kind.phaseFloor ≤ phaseLevel final.phase := reachable.availability output member

end Netlib.Check.TCPHandshakeRecovery
