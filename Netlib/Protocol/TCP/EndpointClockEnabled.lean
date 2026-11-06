import Netlib.Protocol.TCP.EndpointAckEnabled
import Netlib.Protocol.TCP.EndpointReceiveFacts
import Netlib.Protocol.TCP.RecoveryEnabled

/-!
# Endpoint clock advances from current guards

The old ACK causes must permit the new local time.
An accepted advance changes only the recovery clock.
-/

namespace Netlib.Protocol.TCP.Endpoint

def AckTimeReady (state : State) (millis : Nat) : Prop :=
  ∀ reaction, state.ackReaction = some reaction → reaction.WithinTime millis

instance (state : State) (millis : Nat) : Decidable (AckTimeReady state millis) := by
  unfold AckTimeReady
  cases state.ackReaction <;>
    simp only [reduceCtorEq, false_implies, implies_true, Option.some.injEq, forall_eq'] <;> infer_instance

def clockState (state : State) (millis : Nat) : State :=
  { state with recovery := state.recovery.map (fun recovery => { recovery with now := millis }) }

structure ClockFrame (before after : State) : Prop where
  fixed : { before with recovery := none } = { after with recovery := none }
  recovery : after.recovery = before.recovery.map (fun recovery => { recovery with now := after.now })
  monotone : before.now ≤ after.now

variable {before middle after : State} {recovery : Recovery.State}

theorem ClockFrame.refl (state : State) : ClockFrame state state := by
  refine ⟨rfl, ?_, Nat.le_refl _⟩
  cases runtime : state.recovery <;> simp only [State.now, runtime, Option.map_none, Option.map_some, Option.getD_none, Option.getD_some]

theorem ClockFrame.trans (first : ClockFrame before middle) (second : ClockFrame middle after) :
    ClockFrame before after := by
  refine ⟨first.fixed.trans second.fixed, ?_, Nat.le_trans first.monotone second.monotone⟩
  rw [second.recovery, first.recovery]
  cases before.recovery <;> rfl

theorem ClockFrame.core (frame : ClockFrame before after) : after.core = before.core :=
  (congrArg State.core frame.fixed).symm

theorem ClockFrame.pending (frame : ClockFrame before after) : after.pending = before.pending :=
  (congrArg State.pending frame.fixed).symm

theorem ClockFrame.pendingLimit (frame : ClockFrame before after) : after.pendingLimit = before.pendingLimit :=
  (congrArg State.pendingLimit frame.fixed).symm

theorem ClockFrame.sendWindow (frame : ClockFrame before after) : after.sendWindow = before.sendWindow :=
  (congrArg State.sendWindow frame.fixed).symm

theorem ClockFrame.sendWL1 (frame : ClockFrame before after) : after.sendWL1 = before.sendWL1 :=
  (congrArg State.sendWL1 frame.fixed).symm

theorem ClockFrame.sendWL2 (frame : ClockFrame before after) : after.sendWL2 = before.sendWL2 :=
  (congrArg State.sendWL2 frame.fixed).symm

theorem ClockFrame.effectiveMSS (frame : ClockFrame before after) : after.effectiveMSS = before.effectiveMSS :=
  (congrArg State.effectiveMSS frame.fixed).symm

theorem ClockFrame.ipSendLimit (frame : ClockFrame before after) : after.ipSendLimit = before.ipSendLimit :=
  (congrArg State.ipSendLimit frame.fixed).symm

theorem ClockFrame.lastAckWindow (frame : ClockFrame before after) : after.lastAckWindow = before.lastAckWindow :=
  (congrArg State.lastAckWindow frame.fixed).symm

theorem ClockFrame.localReceiveMSS (frame : ClockFrame before after) : after.localReceiveMSS = before.localReceiveMSS :=
  (congrArg State.localReceiveMSS frame.fixed).symm

theorem ClockFrame.ackReaction (frame : ClockFrame before after) : after.ackReaction = before.ackReaction :=
  (congrArg State.ackReaction frame.fixed).symm

theorem ClockFrame.receiveStore (frame : ClockFrame before after) : after.receiveStore = before.receiveStore :=
  (congrArg State.receiveStore frame.fixed).symm

theorem ClockFrame.runtime (frame : ClockFrame before after) (runtime : before.recovery = some recovery) :
    after.recovery = some { recovery with now := after.now } := by
  rw [frame.recovery, runtime]
  rfl

theorem ClockFrame.valid (frame : ClockFrame before after) (valid : before.Valid) : after.Valid := by
  simpa only [State.Valid, frame.core, frame.pending, frame.pendingLimit, frame.sendWindow,
    frame.effectiveMSS, frame.ipSendLimit] using valid

theorem ClockFrame.recovery_coherent (frame : ClockFrame before after) (coherent : RecoveryCoherent before) :
    RecoveryCoherent after := by
  cases runtime : before.recovery with
  | none => simp only [RecoveryCoherent, frame.recovery, runtime, Option.map_none]
  | some recovery =>
    rw [RecoveryCoherent, frame.runtime runtime]
    simpa only [RecoveryCoherent, runtime, Recovery.State.Valid, Recovery.flight, frame.core,
      frame.effectiveMSS, AckWindowKnown, frame.lastAckWindow] using coherent

theorem ClockFrame.storage_coherent (frame : ClockFrame before after) (coherent : StorageCoherent before) :
    StorageCoherent after := by
  simpa only [StorageCoherent, State.StorageValid, frame.receiveStore, frame.core, frame.ackReaction] using coherent

theorem ClockFrame.ack_prepared (frame : ClockFrame before after) (prepared : AckPrepared before)
    (timely : AckTimeReady before after.now) : AckPrepared after := by
  refine ⟨?_, ?_⟩
  · have same : after.recovery.isSome = before.recovery.isSome := by
      rw [frame.recovery]
      cases before.recovery <;> rfl
    simpa only [AckCoherent, frame.ackReaction, same, frame.core, frame.localReceiveMSS] using prepared.1
  · rw [frame.ackReaction]
    cases reaction : before.ackReaction with
    | none => trivial
    | some value =>
      have covered : value.Covered before.core.capacity before.core.window before.effectiveMSS := by
        have guards := prepared.2
        rw [reaction] at guards
        exact guards.2
      exact ⟨timely value reaction, by simpa only [frame.core, frame.effectiveMSS] using covered⟩

theorem ClockFrame.clocked (frame : ClockFrame before after) (runtime : before.recovery = some recovery)
    (clocked : recovery.Clocked) : ({ recovery with now := after.now } : Recovery.State).Clocked := by
  apply Recovery.advance_clocked recovery after.now clocked
  simpa only [State.now, runtime, Option.map_some, Option.getD_some] using frame.monotone

theorem ClockFrame.positive (_frame : ClockFrame before after) (_runtime : before.recovery = some recovery)
    (positive : recovery.Positive) : ({ recovery with now := after.now } : Recovery.State).Positive :=
  Recovery.advance_positive recovery after.now positive

theorem clockState_now (state : State) (millis : Nat) (runtime : state.recovery = some recovery) :
    (clockState state millis).now = millis := by
  simp only [clockState, State.now, runtime, Option.map_some, Option.getD_some]

theorem clockState_frame (state : State) (millis : Nat) (runtime : state.recovery = some recovery)
    (monotone : recovery.now ≤ millis) : ClockFrame state (clockState state millis) := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [clockState_now state millis runtime]
    rfl
  · rw [clockState_now state millis runtime]
    simpa only [State.now, runtime, Option.map_some, Option.getD_some] using monotone

theorem advanceClock_of_monotone (state : State) (millis : Nat) (valid : state.Valid)
    (coherent : RecoveryCoherent state) (runtime : state.recovery = some recovery)
    (monotone : recovery.now ≤ millis) (timely : AckTimeReady state millis) :
    advanceClock state millis = ⟨clockState state millis, .accepted .advanceClock, none, [], none⟩ := by
  simp only [advanceClock, valid, not_true_eq_false, ite_false, coherent, runtime,
    Recovery.advance_of_monotone recovery millis monotone]
  cases reaction : state.ackReaction with
  | none => simp only [reaction, clockState, runtime, Option.map_some]
  | some value =>
    simp only [AckReaction.checkTime_of_within value millis (timely value reaction),
      clockState, runtime, Option.map_some, reaction]

end Netlib.Protocol.TCP.Endpoint
