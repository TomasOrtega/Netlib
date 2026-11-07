import Netlib.Check.TCPHandshakeRecovery
import Netlib.Protocol.TCP.HandshakeTimerBounds

/-!
# Startup timer bounds in the joint endpoint state

Both timers retain their own clocks and actual RTT estimates.
Their handoff intervals follow from recorded timer operations.
-/

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

def TimersBounded (state : State active passive) : Prop :=
  ∀ actor, (state.timer actor).BoundedStartup

theorem TimersBounded.initial : TimersBounded (State.initial : State active passive) := by
  intro actor
  cases actor <;> exact HandshakeTimer.initial_bounded_startup 0

theorem TimersBounded.frame (prior : TimersBounded before)
    (activeTimer : after.activeTimer = before.activeTimer) (passiveTimer : after.passiveTimer = before.passiveTimer) :
    TimersBounded after := by
  intro actor
  cases actor
  · change after.activeTimer.BoundedStartup
    rw [activeTimer]
    exact prior .active
  · change after.passiveTimer.BoundedStartup
    rw [passiveTimer]
    exact prior .passive

theorem TimersBounded.withTimer (prior : TimersBounded state) (actor : Side)
    (timer : HandshakeTimer.State) (valid : timer.Valid) (bounded : timer.BoundedStartup) :
    TimersBounded (state.withTimer actor timer valid) := by
  intro selected
  cases actor <;> cases selected
  · exact bounded
  · exact prior .passive
  · exact prior .active
  · exact bounded

theorem TimersBounded.publish (prior : TimersBounded state) (output : Emission) :
    TimersBounded (publish state output).state := prior

theorem TimersBounded.retainReceipt (prior : TimersBounded effect.state) (receipt : Receipt) :
    TimersBounded (retainReceipt effect receipt).state := prior

theorem TimersBounded.interval (bounded : TimersBounded state) (actor : Side) :
    (state.timer actor).rto ≤ HandshakeTimer.clockEnvelope (state.timer actor).now :=
  HandshakeTimer.State.BoundedStartup.interval (state.timer_valid actor) (bounded actor)

theorem TimersBounded.estimator (bounded : TimersBounded state) (actor : Side) :
    (state.timer actor).estimator = none ∨
      ∃ sample, sample ≤ (state.timer actor).now ∧
        (state.timer actor).estimator = some (RTO.observe none sample) :=
  HandshakeTimer.State.BoundedStartup.estimator (state.timer_valid actor) (bounded actor)

theorem TimersBounded.handoff (bounded : TimersBounded state) (actor : Side)
    (selected : HandshakeTimer.handoff (state.timer actor) = some data) :
    data.now = (state.timer actor).now ∧
      data.rto ≤ max 3000 (HandshakeTimer.clockEnvelope data.now) ∧
      (data.estimator = none ∨ ∃ sample, sample ≤ data.now ∧ data.estimator = some (RTO.observe none sample)) := by
  obtain ⟨_, _, _, clock, interval, estimator, _⟩ := HandshakeTimer.handoff_closed selected
  refine ⟨clock, ?_, ?_⟩
  · rw [interval, clock]
    exact HandshakeTimer.State.BoundedStartup.data_interval (state.timer_valid actor) (bounded actor)
  · rw [estimator, clock]
    exact TimersBounded.estimator bounded actor

end Netlib.Check.TCPHandshakeRecovery
