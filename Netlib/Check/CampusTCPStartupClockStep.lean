import Netlib.Check.CampusTCPRecoveryReceipts
import Netlib.Check.CampusTCPStartupJobDrainComplete

/-!
# The exact timers of an actual campus startup clock step

The stored control step retains its campus time and selected actor.
Its peer timer and handshake phase stay equal to their preceding values.
-/

namespace Netlib.Check.CampusTCPStartupClockStep

open CampusTCPModel

namespace C
export TCPHandshakeRecovery (Step State)
end C

variable {input : Input} {current : C.State input.active input.passive}

structure Recorded (actual : Step input) (current : C.State input.active input.passive) (actor : Actor) (millis : Nat) where
  control : C.Step input.active input.passive
  recorded : actual.result.recovery = some control
  before : control.before = current
  stamp : control.index = actual.before.time
  event : control.event = .advanceClock actor.recoverySide millis
  after : actual.result.state.connection = .recovering control.result.state
  selected : control.result.state.timer actor.recoverySide = { current.timer actor.recoverySide with now := millis }
  peer : control.result.state.timer actor.other.recoverySide = current.timer actor.other.recoverySide
  phase : control.result.state.phase = current.phase

theorem Step.recorded_clock (actual : Step input) (connected : actual.before.connection = .recovering current)
    (event : actual.event = .startupClock actor millis) : Nonempty (Recorded actual current actor millis) := by
  obtain ⟨effect, custody, computed, final⟩ := actual.processed
  rw [event] at computed
  simp only [processCore, runRecovery, connected] at computed
  split at computed
  · cases computed
  · rename_i result evaluated
    have timers := TCPHandshakeRecovery.evaluate_clock_timers evaluated
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst effect
      refine ⟨⟨⟨current, actual.before.time, .advanceClock actor.recoverySide millis, result, evaluated⟩,
        ?_, rfl, rfl, rfl, ?_, timers.1, ?_, timers.2.2.1⟩⟩
      · rw [final]
      · rw [final]
      · cases actor <;> exact timers.2.1
    · rename_i emission emitted
      rw [timers.2.2.2] at emitted
      cases emitted

end Netlib.Check.CampusTCPStartupClockStep
