import Netlib.Check.TCPHandshakeRecoveryFacts
import Netlib.Check.TCPHandshakeRecoveryOutputTTL

/-!
# Actual startup source TTLs

The current inventory comes from the same recorded recovery trace.
-/

namespace Netlib.Check.TCPHandshakeRecovery

variable {active passive : H.Local} {initial final : State active passive}
variable {events : List Event} {steps : List (Step active passive)} {actual : Step active passive}

theorem OutputTTL.step (prior : OutputTTL actual.before) : OutputTTL actual.result.state :=
  evaluate_output_ttl prior actual.computed

theorem Trace.output_ttl (trace : Trace initial events steps final) (prior : OutputTTL initial) : OutputTTL final := by
  induction trace with
  | done => exact prior
  | next actual tail ih => exact ih prior.step

theorem Reachable.output_ttl (reachable : Reachable final) (member : output ∈ final.emissions) :
    1 < output.packet.packet.ip.packet.ttl.toNat :=
  reachable.trace.output_ttl OutputTTL.initial output member

end Netlib.Check.TCPHandshakeRecovery
