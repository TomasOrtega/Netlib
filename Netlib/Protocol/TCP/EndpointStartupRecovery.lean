import Netlib.Protocol.TCP.Endpoint
import Netlib.Protocol.TCP.HandshakeTimer

/-!
# Established recovery from the actual startup timer

The handoff retains the startup clock, RTO, and estimator.
The data ledger starts empty with a congestion window of one effective MSS.
The operation retains endpoint buffers, ACK work, and receive storage.
-/

namespace Netlib.Protocol.TCP.Endpoint

def startupRecovery (smss : Nat) (data : HandshakeTimer.Data) : Recovery.State :=
  { Recovery.initial smss with now := data.now, rto := data.rto, estimator := data.estimator }

def startupRecoveryState (state : State) (data : HandshakeTimer.Data) : State :=
  { state with recovery := some (startupRecovery state.effectiveMSS data), lastAckWindow := some state.sendWindow }

def enableStartupRecovery (state : State) (data : HandshakeTimer.Data) : Result :=
  if ¬state.Valid then rejected state .invalidSeed
  else if state.recovery.isSome || !state.core.sent.isEmpty then recoveryBlocked state .ledger
  else if data.rto < 1000 then recoveryBlocked state .ledger
  else ⟨startupRecoveryState state data, .accepted .enableRecovery, none, [], none⟩

theorem startupRecovery_runtime (smss : Nat) (data : HandshakeTimer.Data) :
    (startupRecovery smss data).now = data.now ∧ (startupRecovery smss data).rto = data.rto ∧
      (startupRecovery smss data).estimator = data.estimator :=
  ⟨rfl, rfl, rfl⟩

theorem startupRecovery_window (smss : Nat) (data : HandshakeTimer.Data) :
    (startupRecovery smss data).smss = smss ∧ (startupRecovery smss data).cwnd = smss ∧
      (startupRecovery smss data).ssthresh = 65535 :=
  ⟨rfl, rfl, rfl⟩

theorem startupRecovery_empty (smss : Nat) (data : HandshakeTimer.Data) :
    (startupRecovery smss data).outstanding = [] ∧ (startupRecovery smss data).nextId = 0 ∧
      (startupRecovery smss data).frontier = 0 ∧ (startupRecovery smss data).lastSample = none ∧
      (startupRecovery smss data).deadline = none ∧ (startupRecovery smss data).lastTimedOut = none ∧
      (startupRecovery smss data).timeoutCount = 0 ∧ (startupRecovery smss data).duplicateAcks = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem startupRecovery_valid (smss : Nat) (data : HandshakeTimer.Data)
    (positive : 0 < smss) (minimum : 1000 ≤ data.rto) : (startupRecovery smss data).Valid := by
  exact ⟨positive, minimum, rfl, by simp only [Recovery.flight, startupRecovery, Recovery.initial,
    List.map_nil, List.sum_nil, Nat.zero_le]⟩

theorem startupRecoveryState_valid (state : State) (data : HandshakeTimer.Data) (valid : state.Valid) :
    (startupRecoveryState state data).Valid := valid

theorem startupRecoveryState_storage_valid (state : State) (data : HandshakeTimer.Data) (valid : state.StorageValid) :
    (startupRecoveryState state data).StorageValid := valid

theorem startupRecoveryState_coherent (state : State) (data : HandshakeTimer.Data)
    (valid : state.Valid) (empty : state.core.sent = []) (minimum : 1000 ≤ data.rto) :
    RecoveryCoherent (startupRecoveryState state data) := by
  refine ⟨startupRecovery_valid _ _ valid.2.2.2.2.1 minimum, rfl, ?_, ?_⟩
  · simp only [startupRecoveryState, startupRecovery, Recovery.initial, Recovery.flight, List.map_nil,
      List.sum_nil, empty, List.length_nil]
  · exact valid.2.2.2.1

theorem startupRecoveryState_frames (state : State) (data : HandshakeTimer.Data) :
    (startupRecoveryState state data).core = state.core ∧
      (startupRecoveryState state data).pending = state.pending ∧
      (startupRecoveryState state data).pendingLimit = state.pendingLimit ∧
      (startupRecoveryState state data).sendWindow = state.sendWindow ∧
      (startupRecoveryState state data).sendWL1 = state.sendWL1 ∧
      (startupRecoveryState state data).sendWL2 = state.sendWL2 ∧
      (startupRecoveryState state data).effectiveMSS = state.effectiveMSS ∧
      (startupRecoveryState state data).ipSendLimit = state.ipSendLimit ∧
      (startupRecoveryState state data).localReceiveMSS = state.localReceiveMSS ∧
      (startupRecoveryState state data).ackReaction = state.ackReaction ∧
      (startupRecoveryState state data).receiveStore = state.receiveStore :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem startupRecoveryState_fields (state : State) (data : HandshakeTimer.Data) :
    (startupRecoveryState state data).recovery = some (startupRecovery state.effectiveMSS data) ∧
      (startupRecoveryState state data).lastAckWindow = some state.sendWindow ∧
      (startupRecoveryState state data).now = data.now :=
  ⟨rfl, rfl, rfl⟩

theorem startupRecoveryState_ackCoherent (state : State) (data : HandshakeTimer.Data)
    (coherent : AckCoherent state) : AckCoherent (startupRecoveryState state data) := by
  cases reaction : state.ackReaction with
  | none => simp only [AckCoherent, startupRecoveryState, reaction]
  | some value =>
    simp only [AckCoherent, reaction] at coherent
    simp only [AckCoherent, startupRecoveryState, reaction]
    exact ⟨rfl, coherent.2⟩

theorem startupRecoveryState_storage (state : State) (data : HandshakeTimer.Data)
    (coherent : StorageCoherent state) : StorageCoherent (startupRecoveryState state data) := coherent

theorem enableStartupRecovery_invalid (state : State) (data : HandshakeTimer.Data) (invalid : ¬state.Valid) :
    enableStartupRecovery state data = rejected state .invalidSeed := by
  simp only [enableStartupRecovery, invalid, not_false_eq_true, ite_true]

theorem enableStartupRecovery_busy (state : State) (data : HandshakeTimer.Data)
    (valid : state.Valid) (busy : (state.recovery.isSome || !state.core.sent.isEmpty) = true) :
    enableStartupRecovery state data = rejected state (.recovery .ledger) := by
  simp only [enableStartupRecovery, valid, not_true_eq_false, ite_false, busy, ite_true]
  rfl

theorem enableStartupRecovery_small_rto (state : State) (data : HandshakeTimer.Data)
    (valid : state.Valid) (disabled : state.recovery = none) (empty : state.core.sent = [])
    (small : data.rto < 1000) :
    enableStartupRecovery state data = rejected state (.recovery .ledger) := by
  simp only [enableStartupRecovery, valid, not_true_eq_false, ite_false, disabled, Option.isSome_none,
    empty, List.isEmpty_nil, Bool.not_true, Bool.or_self, Bool.false_eq_true, small, ite_true]
  rfl

theorem enableStartupRecovery_of_ready (state : State) (data : HandshakeTimer.Data)
    (valid : state.Valid) (disabled : state.recovery = none) (empty : state.core.sent = [])
    (minimum : 1000 ≤ data.rto) :
    enableStartupRecovery state data =
      ⟨startupRecoveryState state data, .accepted .enableRecovery, none, [], none⟩ := by
  simp only [enableStartupRecovery, valid, not_true_eq_false, ite_false, disabled, Option.isSome_none,
    empty, List.isEmpty_nil, Bool.not_true, Bool.or_self, Bool.false_eq_true, Nat.not_lt.mpr minimum]

theorem enableStartupRecovery_accepted_iff (state : State) (data : HandshakeTimer.Data) :
    (enableStartupRecovery state data).decision = .accepted .enableRecovery ↔
      state.Valid ∧ state.recovery = none ∧ state.core.sent = [] ∧ 1000 ≤ data.rto := by
  constructor
  · intro accepted
    unfold enableStartupRecovery at accepted
    split at accepted
    · cases accepted
    · rename_i valid
      split at accepted
      · cases accepted
      · rename_i idle
        split at accepted
        · cases accepted
        · rename_i minimum
          refine ⟨Decidable.not_not.mp valid, ?_, ?_, by omega⟩
          · cases runtime : state.recovery with
            | none => rfl
            | some recovery =>
              simp only [runtime, Option.isSome_some, Bool.true_or] at idle
              exact False.elim (idle trivial)
          · cases sent : state.core.sent with
            | nil => rfl
            | cons byte rest =>
              simp only [sent, List.isEmpty_cons, Bool.not_false, Bool.or_true] at idle
              exact False.elim (idle trivial)
  · rintro ⟨valid, disabled, empty, minimum⟩
    rw [enableStartupRecovery_of_ready state data valid disabled empty minimum]

theorem enableStartupRecovery_valid (state : State) (data : HandshakeTimer.Data) (valid : state.Valid) :
    (enableStartupRecovery state data).state.Valid := by
  unfold enableStartupRecovery
  split
  · exact valid
  · split
    · exact valid
    · split
      · exact valid
      · exact startupRecoveryState_valid state data valid

theorem enableStartupRecovery_storage_valid (state : State) (data : HandshakeTimer.Data) (valid : state.StorageValid) :
    (enableStartupRecovery state data).state.StorageValid := by
  unfold enableStartupRecovery
  split
  · exact valid
  · split
    · exact valid
    · split
      · exact valid
      · exact startupRecoveryState_storage_valid state data valid

theorem enableStartupRecovery_coherent (state : State) (data : HandshakeTimer.Data)
    (accepted : (enableStartupRecovery state data).decision = .accepted .enableRecovery) :
    RecoveryCoherent (enableStartupRecovery state data).state := by
  obtain ⟨valid, disabled, empty, minimum⟩ := (enableStartupRecovery_accepted_iff state data).mp accepted
  rw [enableStartupRecovery_of_ready state data valid disabled empty minimum]
  exact startupRecoveryState_coherent state data valid empty minimum

theorem enableStartupRecovery_quiet (state : State) (data : HandshakeTimer.Data) :
    (enableStartupRecovery state data).output = none ∧ (enableStartupRecovery state data).read = [] ∧
      (enableStartupRecovery state data).ack = none := by
  unfold enableStartupRecovery
  split
  · exact ⟨rfl, rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl, rfl⟩

theorem startupRecovery_default (smss : Nat) :
    startupRecovery smss ⟨0, 1000, none, false⟩ = Recovery.initial smss := rfl

theorem enableStartupRecovery_default (state : State) :
    enableStartupRecovery state ⟨0, 1000, none, false⟩ = enableRecovery state := by
  simp only [enableStartupRecovery, show ¬(1000 : Nat) < 1000 from by decide, ite_false,
    startupRecoveryState, startupRecovery_default, enableRecovery]

end Netlib.Protocol.TCP.Endpoint
