import Netlib.Check.TCPHandshakeRecoveryFacts
import Netlib.Check.TCPHandshakeRecoveryClockBounds

/-!
# Clocks along the actual startup recovery trace

The bound counts the stored operations and their preceding-state guards.
-/

namespace Netlib.Check.TCPHandshakeRecovery

variable {active passive : Protocol.TCP.Handshake.Local}
variable {initial final : State active passive} {events : List Event} {steps : List (Step active passive)}

theorem Step.clock_effect (actual : Step active passive) : ClockEffect actual.before actual.event actual.result.state :=
  evaluate_clock_effect actual.computed

theorem Step.clock_le (actual : Step active passive) (guard : ClockGuard actual.before actual.event quantum) (actor : Side) :
    (actual.result.state.timer actor).now ≤ (actual.before.timer actor).now + quantum :=
  actual.clock_effect.bound guard actor

theorem Trace.clock_le (trace : Trace initial events steps final)
    (guards : ∀ actual ∈ steps, ClockGuard actual.before actual.event quantum) (actor : Side) :
    (final.timer actor).now ≤ (initial.timer actor).now + quantum * steps.length := by
  induction trace with
  | done => simp
  | next actual tail ih =>
    have first := actual.clock_le (guards actual List.mem_cons_self) actor
    have rest := ih (fun selected member => guards selected (List.mem_cons_of_mem actual member))
    simp only [List.length_cons, Nat.mul_succ]
    omega

theorem Trace.initial_clock_le (trace : Trace .initial events steps final)
    (guards : ∀ actual ∈ steps, ClockGuard actual.before actual.event quantum) (actor : Side) :
    (final.timer actor).now ≤ quantum * steps.length := by
  have bounded := trace.clock_le guards actor
  have initial : ((State.initial : State active passive).timer actor).now = 0 := by cases actor <;> rfl
  simpa only [initial, Nat.zero_add] using bounded

end Netlib.Check.TCPHandshakeRecovery
