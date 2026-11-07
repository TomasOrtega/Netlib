import Netlib.Check.TCPHandshakeRecovery

/-!
# Clock inputs during startup recovery

Only an explicit clock event changes a startup timer's current time.
The guard bounds that event from its actual preceding state.
-/

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

def ClockGuard (state : State active passive) (event : Event) (quantum : Nat) : Prop :=
  match event with
  | .advanceClock actor millis => millis ≤ (state.timer actor).now + quantum
  | _ => True

def ClockFrame (before after : State active passive) : Prop :=
  ∀ actor, (after.timer actor).now = (before.timer actor).now

def ClockEffect (before : State active passive) (event : Event) (after : State active passive) : Prop :=
  match event with
  | .advanceClock actor millis =>
    (after.timer actor).now = millis ∧ (after.timer actor.other).now = (before.timer actor.other).now
  | _ => ClockFrame before after

theorem ClockFrame.refl (state : State active passive) : ClockFrame state state := fun _ => rfl

theorem ClockFrame.trans (first : ClockFrame before middle) (second : ClockFrame middle after) :
    ClockFrame before after := fun actor => (second actor).trans (first actor)

theorem ClockFrame.withTimer (state : State active passive) (actor : Side) (timer : T.State) (valid : timer.Valid)
    (same : timer.now = (state.timer actor).now) : ClockFrame state (state.withTimer actor timer valid) := by
  intro selected
  cases actor <;> cases selected <;> first | exact same | rfl

theorem ClockFrame.publish (prior : ClockFrame before state) (output : Emission) :
    ClockFrame before (publish state output).state := prior

theorem ClockFrame.retainReceipt (prior : ClockFrame before effect.state) (receipt : Receipt) :
    ClockFrame before (retainReceipt effect receipt).state := prior

theorem ClockEffect.bound (actual : ClockEffect before event after) (guard : ClockGuard before event quantum)
    (actor : Side) : (after.timer actor).now ≤ (before.timer actor).now + quantum := by
  cases event with
  | activeOpen remote policy | receive source bytes path policy | timeout selected generation policy =>
    rw [actual actor]
    omega
  | advanceClock selected millis =>
    cases selected <;> cases actor
    · exact actual.1 ▸ guard
    · rw [show (after.timer .passive).now = (before.timer .passive).now from actual.2]
      omega
    · rw [show (after.timer .active).now = (before.timer .active).now from actual.2]
      omega
    · exact actual.1 ▸ guard

end Netlib.Check.TCPHandshakeRecovery
