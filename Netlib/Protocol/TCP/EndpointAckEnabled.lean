import Netlib.Protocol.TCP.Endpoint
import Netlib.Protocol.TCP.AckReactionEnabled

/-!
# Endpoint ACK output from preceding guards

The output packet is constructed from the actual endpoint.
Readiness states time, coverage, credit, and deadline bounds without a successful output premise.
-/

namespace Netlib.Protocol.TCP.Endpoint

def AckPrepared (state : State) : Prop :=
  AckCoherent state ∧ match state.ackReaction with
    | none => True
    | some reaction => reaction.WithinTime state.now ∧
        reaction.Covered state.core.capacity state.core.window state.effectiveMSS

instance (state : State) : Decidable (AckPrepared state) := by
  unfold AckPrepared
  split <;> infer_instance

def ResponseAvailable (state : State) (dueOnly : Bool) : Prop :=
  match state.ackReaction with
  | none => dueOnly = false
  | some reaction => reaction.work.pending ≠ [] ∧
      (dueOnly = true → ∃ deadline, reaction.due = some deadline ∧ deadline ≤ state.now)

instance (state : State) (dueOnly : Bool) : Decidable (ResponseAvailable state dueOnly) := by
  unfold ResponseAvailable
  split <;> infer_instance

theorem ackReady_of_prepared (state : State) (prepared : AckPrepared state) : ackReady state = .ok () := by
  have coherent := prepared.1
  unfold ackReady
  simp only [coherent, not_true_eq_false, ite_false]
  cases selected : state.ackReaction with
  | none => rfl
  | some reaction =>
    have fields : reaction.WithinTime state.now ∧
        reaction.Covered state.core.capacity state.core.window state.effectiveMSS := by
      simpa only [AckPrepared, selected] using prepared.2
    exact AckReaction.outputReady_of_covered _ _ _ _ _ _ fields.1 fields.2

theorem responseReady_of_available (state : State) (dueOnly : Bool) (prepared : AckPrepared state)
    (available : ResponseAvailable state dueOnly) : responseReady state dueOnly = .ok () := by
  unfold responseReady
  cases selected : state.ackReaction with
  | none =>
    have off : dueOnly = false := by simpa only [ResponseAvailable, selected] using available
    rw [off]
    rfl
  | some reaction =>
    have fields : reaction.work.pending ≠ [] ∧
        (dueOnly = true → ∃ deadline, reaction.due = some deadline ∧ deadline ≤ state.now) := by
      simpa only [ResponseAvailable, selected] using available
    have work : reaction.WithinTime state.now ∧
        reaction.Covered state.core.capacity state.core.window state.effectiveMSS := by
      simpa only [selected] using prepared.2
    have times := work.1
    exact AckReaction.responseReady_of_credit _ _ _ times fields.1 fields.2

theorem pureAck_success_enabled (state : State) (dueOnly : Bool) (valid : state.Valid)
    (prepared : AckPrepared state) (available : ResponseAvailable state dueOnly) :
    ∃ output, pureAck state true dueOnly =
      ⟨outputState state, .accepted (if dueOnly then .dispatchAck else .emitAck), some output, [], none⟩ ∧
      emit state [] = .ok output := by
  obtain ⟨output, encoded⟩ := emit_exists state [] valid prepared.1 (by decide)
  refine ⟨output, ?_, encoded⟩
  simp only [pureAck, valid, not_true_eq_false, ite_false, Bool.not_true, Bool.false_eq_true,
    responseReady_of_available state dueOnly prepared available, ackReady_of_prepared state prepared, encoded]

theorem emitAck_success_enabled (state : State) (valid : state.Valid)
    (prepared : AckPrepared state) (available : ResponseAvailable state false) :
    ∃ output, emitAck state true = ⟨outputState state, .accepted .emitAck, some output, [], none⟩ ∧
      emit state [] = .ok output :=
  pureAck_success_enabled state false valid prepared available

theorem dispatchAck_success_enabled (state : State) (valid : state.Valid)
    (prepared : AckPrepared state) (available : ResponseAvailable state true) :
    ∃ output, dispatchAck state true = ⟨outputState state, .accepted .dispatchAck, some output, [], none⟩ ∧
      emit state [] = .ok output :=
  pureAck_success_enabled state true valid prepared available

theorem send_success_enabled (state : State) (count : Nat) (valid : state.Valid)
    (ready : SendReady state count) (prepared : AckPrepared state) :
    ∃ output, send state count true =
      ⟨sendState state count, .accepted (.send count), some output, [], none⟩ :=
  send_success state count valid ready (ackReady_of_prepared state prepared)

theorem outputState_ackPrepared (state : State) (prepared : AckPrepared state) : AckPrepared (outputState state) := by
  cases selected : state.ackReaction with
  | none => simpa only [AckPrepared, AckCoherent, outputState, selected, Option.map_none] using prepared
  | some reaction =>
    have coherent : state.recovery.isSome = true ∧
        reaction.Coherent state.core.receiveNext state.core.window state.localReceiveMSS.limit := by
      simpa only [AckCoherent, selected] using prepared.1
    refine ⟨?_, ?_⟩
    · simp only [AckCoherent, outputState, selected, Option.map_some]
      exact ⟨coherent.1, AckReaction.outputState_coherent _ _ _ _ _ _ _ coherent.2⟩
    · simp only [outputState, selected, Option.map_some]
      change (AckReaction.outputState reaction state.now state.core.receiveNext state.core.capacity
        state.core.window state.effectiveMSS).WithinTime (outputState state).now ∧
        (AckReaction.outputState reaction state.now state.core.receiveNext state.core.capacity
          state.core.window state.effectiveMSS).Covered state.core.capacity state.core.window state.effectiveMSS
      exact ⟨AckReaction.outputState_within _ _ _ _ _ _ _, AckReaction.outputState_covered _ _ _ _ _ _⟩

theorem writeState_ackPrepared (state : State) (bytes : List UInt8) (prepared : AckPrepared state) :
    AckPrepared (writeState state bytes) := prepared

theorem readState_ackPrepared (state : State) (count : Nat) (valid : state.Valid)
    (fits : count ≤ state.core.received.length) (prepared : AckPrepared state) : AckPrepared (readState state count) := by
  cases selected : state.ackReaction with
  | none => simp only [AckPrepared, AckCoherent, readState, selected, Option.map_none, and_self]
  | some reaction =>
    have coherent : state.recovery.isSome = true ∧
        reaction.Coherent state.core.receiveNext state.core.window state.localReceiveMSS.limit := by
      simpa only [AckCoherent, selected] using prepared.1
    have guards : reaction.WithinTime state.now ∧
        reaction.Covered state.core.capacity state.core.window state.effectiveMSS := by
      simpa only [selected] using prepared.2
    have growth : state.core.window ≤ (readState state count).core.window := by
      rw [readState_window state count valid fits]
      omega
    refine ⟨?_, ?_⟩
    · simp only [AckCoherent, readState, selected, Option.map_some]
      exact ⟨coherent.1, AckReaction.read_coherent _ _ _ _ _ _ _ _ coherent.2 growth⟩
    · simp only [readState, selected, Option.map_some]
      exact ⟨AckReaction.read_within _ _ _ _ _ _ _ guards.1,
        AckReaction.read_covered _ _ _ _ _ _ _ guards.2 coherent.2.1 growth⟩

theorem sendState_ackPrepared (state : State) (count : Nat) (prepared : AckPrepared state) :
    AckPrepared (sendState state count) := by
  have frame : AckPrepared (sendState state count) = AckPrepared (outputState state) := by
    cases recovery : state.recovery <;>
      simp [AckPrepared, AckCoherent, sendState, outputState, State.now, EstablishedReceive.State.window, Recovery.sent, recovery]
  rw [frame]
  exact outputState_ackPrepared state prepared

theorem enableAck_success_prepared (state : State) (valid : state.Valid)
    (coherent : RecoveryCoherent state) (disabled : state.ackReaction = none)
    (recovery : state.recovery.isSome = true) (received : state.core.received = [])
    (sent : state.core.sent = []) (initial : state.receiveStore = ReceiveStore.initial) :
    let after := { state with ackReaction := some (AckReaction.initial state.core.receiveNext
      state.core.capacity state.localReceiveMSS.limit) }
    enableAck state = ⟨after, .accepted .enableAck, none, [], none⟩ ∧ AckPrepared after := by
  dsimp only
  have on : state.recovery.isNone = false := by
    cases selected : state.recovery <;> simp_all
  constructor
  · simp only [enableAck, valid, not_true_eq_false, ite_false, coherent, disabled, Option.isSome_none,
      Bool.false_eq_true, on, received, sent, List.isEmpty_nil, Bool.not_true, Bool.false_or, initial, ne_eq]
  · have window : state.core.window = state.core.capacity := by
      simp only [EstablishedReceive.State.window, received, List.length_nil, Nat.sub_zero]
    constructor
    · simp only [AckCoherent]
      exact ⟨recovery, window ▸ AckReaction.initial_coherent _ _ _ state.localReceiveMSS.limit_positive⟩
    · refine ⟨AckReaction.initial_within _ _ _ _, ?_⟩
      change (AckReaction.initial state.core.receiveNext state.core.capacity state.localReceiveMSS.limit).Covered
        state.core.capacity state.core.window state.effectiveMSS
      rw [window]
      exact AckReaction.initial_covered _ _ _ _

end Netlib.Protocol.TCP.Endpoint
