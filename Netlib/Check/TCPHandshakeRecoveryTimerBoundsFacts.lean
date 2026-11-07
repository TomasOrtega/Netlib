import Netlib.Check.TCPHandshakeRecoveryFacts
import Netlib.Check.TCPHandshakeRecoveryTimerBounds

/-!
# Timer bounds from the actual startup trace

Each bound uses the timer's current clock and recorded RTT estimate.
No packet-loss count or supplied RTO cap is needed.
-/

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

variable {active passive : H.Local}
variable {before final : State active passive} {actual : Step active passive}
variable {events : List Event} {steps : List (Step active passive)}
variable {flight : HandshakeTimer.Flight} {data : HandshakeTimer.Data}

theorem TimersBounded.step (prior : TimersBounded actual.before) : TimersBounded actual.result.state :=
  evaluate_timer_bounds prior actual.computed

theorem Trace.timers_bounded (trace : Trace before events steps final) (prior : TimersBounded before) :
    TimersBounded final := by
  induction trace with
  | done => exact prior
  | next actual tail ih => exact ih prior.step

theorem Reachable.timers_bounded (reachable : Reachable final) : TimersBounded final :=
  reachable.trace.timers_bounded TimersBounded.initial

theorem Reachable.timer_elapsed (reachable : Reachable final) (actor : Side) :
    (final.timer actor).Elapsed := (reachable.timers_bounded actor).1

theorem Reachable.timer_interval (reachable : Reachable final) (actor : Side) :
    (final.timer actor).rto ≤ HandshakeTimer.clockEnvelope (final.timer actor).now :=
  reachable.timers_bounded.interval actor

theorem Reachable.timer_estimator (reachable : Reachable final) (actor : Side) :
    (final.timer actor).estimator = none ∨ ∃ sample, sample ≤ (final.timer actor).now ∧
      (final.timer actor).estimator = some (RTO.observe none sample) :=
  reachable.timers_bounded.estimator actor

theorem Reachable.pending_initial_rto (reachable : Reachable final) (actor : Side)
    (pending : (final.timer actor).status = .pending flight) : flight.initialRTO = 1000 := by
  have fields := (reachable.timers_bounded actor).2
  simp only [pending] at fields
  exact fields.1

theorem Reachable.pending_interval_elapsed (reachable : Reachable final) (actor : Side)
    (pending : (final.timer actor).status = .pending flight) :
    (final.timer actor).rto ≤ 1000 + ((final.timer actor).now - flight.firstAt) := by
  have interval := HandshakeTimer.pending_interval_elapsed (final.timer_valid actor) (reachable.timer_elapsed actor) pending
  rw [reachable.pending_initial_rto actor pending] at interval
  exact interval

theorem Reachable.pending_deadline_remaining (_reachable : Reachable final) (actor : Side)
    (pending : (final.timer actor).status = .pending flight) :
    flight.deadline - (final.timer actor).now ≤ (final.timer actor).rto :=
  HandshakeTimer.pending_deadline_remaining (final.timer_valid actor) pending

theorem Reachable.handoff_bounds (reachable : Reachable final) (actor : Side)
    (selected : HandshakeTimer.handoff (final.timer actor) = some data) :
    data.now = (final.timer actor).now ∧
      data.rto ≤ max 3000 (HandshakeTimer.clockEnvelope data.now) ∧
      (data.estimator = none ∨ ∃ sample, sample ≤ data.now ∧ data.estimator = some (RTO.observe none sample)) :=
  reachable.timers_bounded.handoff actor selected

end Netlib.Check.TCPHandshakeRecovery
