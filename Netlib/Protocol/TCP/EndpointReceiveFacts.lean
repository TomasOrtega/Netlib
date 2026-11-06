import Netlib.Protocol.TCP.Endpoint
import Netlib.Protocol.TCP.ReceiveStoreHistory

/-!
# Receive effects and storage preservation on actual endpoint operations

Ordered release and new input have separate byte counts.
Each committed store step retains its actual receipt metadata.
-/

namespace Netlib.Protocol.TCP.Endpoint

theorem storage_valid_of_empty (state : State) (empty : state.receiveStore.held = []) : state.StorageValid := by
  simp [State.StorageValid, ReceiveStore.State.Valid, ReceiveStore.State.heldBytes, ReceiveStore.size, empty]

theorem writeState_storage_valid (state : State) (bytes : List UInt8) (valid : state.StorageValid) :
    (writeState state bytes).StorageValid := valid

theorem outputState_storage_valid (state : State) (valid : state.StorageValid) :
    (outputState state).StorageValid := valid

theorem sendState_storage_valid (state : State) (count : Nat) (valid : state.StorageValid) :
    (sendState state count).StorageValid := valid

theorem readState_storage_valid (state : State) (count : Nat) (valid : state.StorageValid) :
    (readState state count).StorageValid := by
  have room : state.core.window ≤ (readState state count).core.window := by
    simp only [readState, EstablishedReceive.State.window, List.length_drop]
    omega
  change state.receiveStore.Valid (state.receiveStore.frontier + (readState state count).core.window)
    (readState state count).core.window
  exact ReceiveStore.State.valid_mono state.receiveStore _ _ _ _ valid (Nat.add_le_add_left room _) room (by omega)

theorem write_storage_valid (state : State) (bytes : List UInt8) (valid : state.StorageValid) :
    (write state bytes).state.StorageValid := by
  unfold write
  repeat' first | (solve | exact valid) | split

theorem read_storage_valid (state : State) (count : Nat) (valid : state.StorageValid) :
    (read state count).state.StorageValid := by
  unfold read
  repeat' first | (solve | exact valid) | (solve | exact readState_storage_valid state count valid) | split

theorem send_storage_valid (state : State) (count : Nat) (policy : Bool) (valid : state.StorageValid) :
    (send state count policy).state.StorageValid := by
  unfold send
  repeat' first
    | (solve | exact valid)
    | (solve | exact sendState_storage_valid state count valid)
    | (solve | rw [recoveryBlocked_state]; exact valid)
    | (solve | rw [ackBlocked_state]; exact valid)
    | split

theorem pureAck_storage_valid (state : State) (policy dueOnly : Bool) (valid : state.StorageValid) :
    (pureAck state policy dueOnly).state.StorageValid := by
  unfold pureAck
  repeat' first
    | (solve | exact valid)
    | (solve | exact outputState_storage_valid state valid)
    | (solve | rw [ackBlocked_state]; exact valid)
    | split

theorem emitAck_storage_valid (state : State) (policy : Bool) (valid : state.StorageValid) :
    (emitAck state policy).state.StorageValid := pureAck_storage_valid state policy false valid

theorem dispatchAck_storage_valid (state : State) (policy : Bool) (valid : state.StorageValid) :
    (dispatchAck state policy).state.StorageValid := pureAck_storage_valid state policy true valid

theorem timeout_storage_valid (state : State) (policy : Bool) (valid : state.StorageValid) :
    (timeout state policy).state.StorageValid := by
  unfold timeout
  repeat' first
    | (solve | exact valid)
    | (solve | exact outputState_storage_valid state valid)
    | (solve | rw [recoveryBlocked_state]; exact valid)
    | (solve | rw [ackBlocked_state]; exact valid)
    | split

theorem enableRecovery_storage_valid (state : State) (valid : state.StorageValid) :
    (enableRecovery state).state.StorageValid := by
  unfold enableRecovery
  repeat' first | (solve | exact valid) | (solve | rw [recoveryBlocked_state]; exact valid) | split

theorem advanceClock_storage_valid (state : State) (millis : Nat) (valid : state.StorageValid) :
    (advanceClock state millis).state.StorageValid := by
  unfold advanceClock
  repeat' first
    | (solve | exact valid)
    | (solve | rw [recoveryBlocked_state]; exact valid)
    | (solve | rw [ackBlocked_state]; exact valid)
    | split

theorem enableAck_storage_valid (state : State) (valid : state.StorageValid) :
    (enableAck state).state.StorageValid := by
  unfold enableAck
  repeat' first
    | (solve | exact valid)
    | (solve | rw [recoveryBlocked_state]; exact valid)
    | (solve | rw [ackBlocked_state]; exact valid)
    | split

theorem windowState_receive_frame (before after : State) (segment : Segment) :
    (windowState before after segment).core = after.core ∧
      (windowState before after segment).pending = after.pending ∧
      (windowState before after segment).localReceiveMSS = after.localReceiveMSS ∧
      (windowState before after segment).receiveStore = after.receiveStore := by
  unfold windowState
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

@[simp] theorem windowState_core (before after : State) (segment : Segment) :
    (windowState before after segment).core = after.core := (windowState_receive_frame before after segment).1

@[simp] theorem windowState_pending (before after : State) (segment : Segment) :
    (windowState before after segment).pending = after.pending := (windowState_receive_frame before after segment).2.1

@[simp] theorem windowState_ownMSS (before after : State) (segment : Segment) :
    (windowState before after segment).localReceiveMSS = after.localReceiveMSS := (windowState_receive_frame before after segment).2.2.1

@[simp] theorem windowState_receiveStore (before after : State) (segment : Segment) :
    (windowState before after segment).receiveStore = after.receiveStore := (windowState_receive_frame before after segment).2.2.2

inductive HeaderChain : ERState → List ReceiveReassembly.HeaderEffect → ERState → Prop where
  | nil (state : ERState) : HeaderChain state [] state
  | cons (head : ReceiveReassembly.HeaderEffect) (tail : HeaderChain head.after headers final) :
      HeaderChain head.before (head :: headers) final

theorem applyRuns_header_chain (state : ERState) (runs : List ReceiveReassembly.Run)
    (result : ReceiveReassembly.Applied) (accepted : ReceiveReassembly.applyRuns state runs = .ok result) :
    HeaderChain state result.headers result.state := by
  induction runs generalizing state result with
  | nil =>
    simp only [ReceiveReassembly.applyRuns, Except.ok.injEq] at accepted
    subst result
    exact .nil state
  | cons head tail ih =>
    obtain ⟨first, rest, firstEq, restEq, same⟩ := ReceiveReassembly.applyRuns_cons state head tail result accepted
    have source := (ReceiveReassembly.applyRun_fields state head first firstEq).1
    have following := HeaderChain.cons first (ih first.after rest restEq)
    rw [source] at following
    rw [same]
    exact following


theorem applyHeader_fields (state : State) (header : ReceiveReassembly.HeaderEffect) (next : State)
    (accepted : applyHeader state header = .ok next) :
    state.core = header.before ∧ next.core = header.after ∧ next.pending = state.pending ∧
      next.localReceiveMSS = state.localReceiveMSS ∧ next.receiveStore = state.receiveStore := by
  unfold applyHeader at accepted
  split at accepted
  · cases accepted
  · rename_i matching
    cases stored : state.recovery with
    | none =>
      simp only [stored] at accepted
      cases accepted
      unfold windowState
      split <;> exact ⟨Decidable.not_not.mp matching, rfl, rfl, rfl, rfl⟩
    | some recovery =>
      simp only [stored] at accepted
      cases updated : Recovery.acknowledgeAt recovery header.acknowledged header.run.metadata.receivedAt with
      | error reason =>
        simp only [updated, Except.map] at accepted
        cases accepted
      | ok received =>
        simp only [updated, Except.map] at accepted
        cases accepted
        unfold windowState
        split <;> exact ⟨Decidable.not_not.mp matching, rfl, rfl, rfl, rfl⟩

theorem HeaderChain.applyHeaders_core (chain : HeaderChain before headers final) (state next : State)
    (core : state.core = before) (accepted : applyHeaders state headers = .ok next) : next.core = final := by
  induction chain generalizing state next with
  | nil initial =>
    simp only [applyHeaders.eq_1, Except.ok.injEq] at accepted
    subst next
    exact core
  | cons head tail ih =>
    cases applied : applyHeader state head with
    | error reason => simp only [applyHeaders.eq_2, applied] at accepted; cases accepted
    | ok after =>
      rw [applyHeaders.eq_2, applied] at accepted
      have changed := (applyHeader_fields state head after applied).2.1
      exact ih after next changed accepted

theorem applyHeaders_frame (state : State) (headers : List ReceiveReassembly.HeaderEffect) (next : State)
    (accepted : applyHeaders state headers = .ok next) :
    next.pending = state.pending ∧ next.localReceiveMSS = state.localReceiveMSS ∧ next.receiveStore = state.receiveStore := by
  induction headers generalizing state next with
  | nil =>
    simp only [applyHeaders.eq_1, Except.ok.injEq] at accepted
    subst next
    exact ⟨rfl, rfl, rfl⟩
  | cons head tail ih =>
    cases applied : applyHeader state head with
    | error reason => simp only [applyHeaders.eq_2, applied] at accepted; cases accepted
    | ok after =>
      rw [applyHeaders.eq_2, applied] at accepted
      have frame := applyHeader_fields state head after applied
      obtain ⟨pending, own, store⟩ := ih after next accepted
      exact ⟨pending.trans frame.2.2.1, own.trans frame.2.2.2.1, store.trans frame.2.2.2.2⟩

theorem processRuns_fields (state : State) (runs : List ReceiveReassembly.Run) (processed : ReceiveProcessed)
    (accepted : processRuns state runs = .ok processed) :
    ReceiveReassembly.applyRuns state.core runs = .ok processed.coreResult ∧
      applyHeaders state processed.coreResult.headers = .ok processed.received := by
  induction runs generalizing state processed with
  | nil =>
    simp only [processRuns.eq_1, Except.ok.injEq] at accepted
    subst processed
    exact ⟨rfl, rfl⟩
  | cons head tail ih =>
    cases firstEq : ReceiveReassembly.applyRun state.core head with
    | error failure => simp only [processRuns.eq_2, firstEq] at accepted; cases accepted
    | ok header =>
      cases headerEq : applyHeader state header with
      | error failure => simp only [processRuns.eq_2, firstEq, headerEq] at accepted; cases accepted
      | ok after =>
        cases restEq : processRuns after tail with
        | error failure => simp only [processRuns.eq_2, firstEq, headerEq, restEq] at accepted; cases accepted
        | ok rest =>
          simp only [processRuns.eq_2, firstEq, headerEq, restEq, Except.ok.injEq] at accepted
          subst processed
          obtain ⟨coreTail, headersTail⟩ := ih after rest restEq
          have core := (applyHeader_fields state header after headerEq).2.1
          rw [core] at coreTail
          constructor
          · simp only [ReceiveReassembly.applyRuns, firstEq, bind, Except.bind, coreTail, pure, Except.pure]
          · simp only [applyHeaders.eq_2, headerEq, headersTail]

def receiveRetired (result : Result) : Nat :=
  match result.decision with | .accepted (.receive count _) => count | _ => 0

structure ReceiveEffects (before : State) (effect : ReceiveEffect) : Prop where
  pending : effect.result.state.pending = before.pending
  sent : effect.result.state.core.sent = before.core.sent.drop (receiveRetired effect.result)
  received : effect.result.state.core.received = before.core.received ++ ReceiveStore.bytes effect.runs
  sendNext : effect.result.state.core.sendNext = before.core.sendNext
  receiveNext : effect.result.state.core.receiveNext = before.core.receiveNext.add (ReceiveStore.size effect.runs)
  sendUna : effect.result.state.core.sendUna = before.core.sendUna.add (receiveRetired effect.result)
  own : effect.result.state.localReceiveMSS = before.localReceiveMSS
  output : effect.result.output = none
  read : effect.result.read = []
  bounded : receiveRetired effect.result ≤ before.core.sent.length
  noRuns : effect.stored = none → effect.runs = []
  store : effect.stored = none → effect.result.state.receiveStore = before.receiveStore

theorem ReceiveEffects.withFailure (effects : ReceiveEffects state effect) (failure : Option ReceiveFailure) :
    ReceiveEffects state { effect with failure } :=
  ⟨effects.pending, effects.sent, effects.received, effects.sendNext, effects.receiveNext,
    effects.sendUna, effects.own, effects.output, effects.read, effects.bounded, effects.noRuns, effects.store⟩

private theorem rejected_receive_effects (state : State) (reason : Reject) :
    ReceiveEffects state (receivePlain (rejected state reason)) := by
  constructor <;> simp [receivePlain, rejected, receiveRetired, ReceiveStore.bytes, ReceiveStore.size]

private theorem recoveryBlocked_receive_effects (state : State) (reason : Recovery.Stop) :
    ReceiveEffects state (receivePlain (recoveryBlocked state reason)) := by
  unfold recoveryBlocked
  split
  · constructor <;> simp [receivePlain, receiveRetired, ReceiveStore.bytes, ReceiveStore.size]
  · exact rejected_receive_effects state _

private theorem ackBlocked_receive_effects (state : State) (reason : AckReaction.Stop) :
    ReceiveEffects state (receivePlain (ackBlocked state reason)) := by
  unfold ackBlocked
  split
  · constructor <;> simp [receivePlain, receiveRetired, ReceiveStore.bytes, ReceiveStore.size]
  · exact rejected_receive_effects state _

theorem receiveStopped_effects (state : State) (reason : EstablishedReceive.Block)
    (ack : Option EstablishedReceive.AckRequest) : ReceiveEffects state (receivePlain (receiveStopped state reason ack)) := by
  cases reason with
  | unsupported reason => constructor <;> simp [receivePlain, receiveStopped, receiveRetired, ReceiveStore.bytes, ReceiveStore.size]
  | reject reason =>
    cases issued : issueRequest state state.core ack 0 with
    | error stopped => simpa only [receiveStopped, issued] using ackBlocked_receive_effects state stopped
    | ok reaction => constructor <;> simp [receivePlain, receiveStopped, issued, receiveRetired, ReceiveStore.bytes, ReceiveStore.size]

private theorem receiveInOrder_empty_effects (state : State) (input : Input) (empty : input.packet.segment.payload = []) :
    ReceiveEffects state (receivePlain (receiveInOrder state input)) := by
  unfold receiveInOrder
  split
  · exact rejected_receive_effects state _
  · split
    · exact recoveryBlocked_receive_effects state _
    · split
      · exact ackBlocked_receive_effects state _
      · dsimp only
        cases selected : (receiveModel state input).decision with
        | blocked reason =>
          cases reason with
          | unsupported reason => constructor <;> simp [receivePlain, receiveRetired, ReceiveStore.bytes, ReceiveStore.size]
          | reject reason =>
            dsimp only
            cases issued : issueRequest state state.core (receiveModel state input).ack 0 with
            | error stopped => exact ackBlocked_receive_effects state stopped
            | ok reaction =>
              dsimp only
              constructor <;> simp [receivePlain, receiveRetired, ReceiveStore.bytes, ReceiveStore.size]
        | accepted count size =>
          dsimp only
          have effects := receiveModel_effects state input
          simp only [EstablishedReceive.Effects, selected] at effects
          obtain ⟨_, bounded, _, _, changed⟩ := effects
          cases updated : receiveRecovery state input.packet.segment count with
          | error stopped => exact recoveryBlocked_receive_effects state stopped
          | ok recovery =>
            dsimp only
            cases issued : issueRequest state (receiveModel state input).state (receiveModel state input).ack size with
            | error stopped => exact ackBlocked_receive_effects state stopped
            | ok reaction =>
              dsimp only
              constructor <;> first
                | exact bounded
                | simp [receivePlain, receiveRetired, ReceiveStore.bytes, ReceiveStore.size,
                    receiveState, changed, EstablishedReceive.commit, empty]

theorem prepare_acknowledgment_empty (state : State) (input : Input) (count : Nat)
    (selected : ReceiveReassembly.prepare state.core state.receiveStore input (offeredWindow state) state.now =
      .acknowledgment count) : input.packet.segment.payload = [] := by
  unfold ReceiveReassembly.prepare at selected
  cases gated : ReceiveReassembly.initialGate state.core input (offeredWindow state) with
  | blocked reason kind => simp only [gated] at selected; cases selected
  | next amount =>
    simp only [gated] at selected
    split at selected
    · rename_i empty
      simpa using empty
    · split at selected
      · cases selected
      · split at selected <;> cases selected


theorem receiveFailed_effects (state : State) (receiptID : Nat) (failure : ReceiveFailure) :
    ReceiveEffects state (receiveFailed state receiptID failure) := by
  cases failure with
  | header failure =>
    unfold receiveFailed
    dsimp only [ReceiveFailure.run]
    by_cases current : failure.run.receipt = receiptID
    · simp only [current, ite_true]
      exact (receiveStopped_effects state _ _).withFailure (some (.header failure))
    · simp only [current, ite_false]
      constructor <;> simp [receiveRetired, ReceiveStore.bytes, ReceiveStore.size]
  | recovery failure =>
    unfold receiveFailed
    dsimp only [ReceiveFailure.run]
    by_cases current : failure.header.run.receipt = receiptID
    · simp only [current, ite_true]
      exact (recoveryBlocked_receive_effects state _).withFailure (some (.recovery failure))
    · simp only [current, ite_false]
      constructor <;> simp [receiveRetired, ReceiveStore.bytes, ReceiveStore.size]

theorem receiveRaw_effects (state : State) (input : Input) : ReceiveEffects state (receiveRaw state input) := by
  unfold receiveRaw
  split
  · exact rejected_receive_effects state _
  · split
    · exact recoveryBlocked_receive_effects state _
    · split
      · exact ackBlocked_receive_effects state _
      · split
        · exact rejected_receive_effects state _
        · cases planned : ReceiveReassembly.prepare state.core state.receiveStore input (offeredWindow state) state.now with
          | blocked reason ack => exact receiveStopped_effects state reason ack
          | acknowledgment count => exact receiveInOrder_empty_effects state input (prepare_acknowledgment_empty state input count planned)
          | data stored =>
            dsimp only
            cases processedEq : processRuns state stored.released with
            | error failure => exact receiveFailed_effects state stored.receiptID failure
            | ok processed =>
              dsimp only
              split
              · constructor <;> simp [receivePlain, receiveRetired, ReceiveStore.bytes, ReceiveStore.size]
              · obtain ⟨applied, headers⟩ := processRuns_fields state stored.released processed processedEq
                have core := (applyRuns_header_chain state.core stored.released processed.coreResult applied).applyHeaders_core
                  state processed.received rfl headers
                obtain ⟨pending, own, _⟩ := applyHeaders_frame state processed.coreResult.headers processed.received headers
                obtain ⟨unread, cursor, sent, una, next, _, _, bound⟩ :=
                  ReceiveReassembly.applyRuns_effects state.core stored.released processed.coreResult applied
                refine ⟨pending, ?_, ?_, ?_, ?_, ?_, own, rfl, rfl, bound, ?_, ?_⟩
                · change processed.received.core.sent = state.core.sent.drop processed.coreResult.acknowledged
                  rw [core]
                  exact sent
                · change processed.received.core.received = state.core.received ++ ReceiveStore.bytes stored.released
                  rw [core]
                  exact unread
                · change processed.received.core.sendNext = state.core.sendNext
                  rw [core]
                  exact next
                · change processed.received.core.receiveNext = state.core.receiveNext.add (ReceiveStore.size stored.released)
                  rw [core]
                  exact cursor
                · change processed.received.core.sendUna = state.core.sendUna.add processed.coreResult.acknowledged
                  rw [core]
                  exact una
                · intro absent; cases absent
                · intro absent; cases absent

theorem receiveEffect_effects (state : State) (input : Input) : ReceiveEffects state (receiveEffect state input) := by
  unfold receiveEffect
  dsimp only
  split
  · exact receiveRaw_effects state input
  · exact rejected_receive_effects state _

theorem receive_effects (state : State) (input : Input) :
    (receive state input).state.pending = state.pending ∧
      (receive state input).state.core.sent = state.core.sent.drop (receiveRetired (receive state input)) ∧
      (receive state input).state.core.received = state.core.received ++ receivedBytes state input ∧
      (receive state input).state.core.sendNext = state.core.sendNext ∧
      (receive state input).state.core.receiveNext = state.core.receiveNext.add (receivedBytes state input).length ∧
      (receive state input).state.core.sendUna = state.core.sendUna.add (receiveRetired (receive state input)) ∧
      (receive state input).state.localReceiveMSS = state.localReceiveMSS ∧
      (receive state input).output = none ∧ (receive state input).read = [] := by
  have effects := receiveEffect_effects state input
  exact ⟨effects.pending, effects.sent, effects.received, effects.sendNext,
    by simpa only [receive, receivedBytes, receiveRuns, ReceiveStore.size_bytes] using effects.receiveNext,
    effects.sendUna, effects.own, effects.output, effects.read⟩

theorem receiveRetired_bound (state : State) (input : Input) :
    receiveRetired (receive state input) ≤ state.core.sent.length := (receiveEffect_effects state input).bounded

structure StoreCommit (before : State) (input : Input) (effect : ReceiveEffect)
    (stored : ReceiveStore.Result ReceiveReassembly.Receipt) : Prop where
  prepared : ReceiveReassembly.prepare before.core before.receiveStore input (offeredWindow before) before.now = .data stored
  present : effect.stored = some stored
  state : effect.result.state.receiveStore = stored.state
  runs : effect.runs = stored.released
  accepted : ∃ count, effect.result.decision = .accepted (.receive count stored.novel)

theorem receiveRaw_stored (state : State) (input : Input) (stored : ReceiveStore.Result ReceiveReassembly.Receipt)
    (selected : (receiveRaw state input).stored = some stored) : StoreCommit state input (receiveRaw state input) stored := by
  unfold receiveRaw at selected ⊢
  split at selected
  · cases selected
  · split at selected
    · cases selected
    · split at selected
      · cases selected
      · split at selected
        · cases selected
        · cases planned : ReceiveReassembly.prepare state.core state.receiveStore input (offeredWindow state) state.now with
          | blocked reason ack => simp only [planned, receivePlain] at selected; cases selected
          | acknowledgment count => simp only [planned, receivePlain] at selected; cases selected
          | data actual =>
            simp only [planned] at selected
            cases processed : processRuns state actual.released with
            | error failure =>
              simp only [processed, receiveFailed] at selected
              cases selected
            | ok completed =>
              simp only [processed] at selected
              split at selected
              · cases selected
              · cases selected
                simp_all only [ite_false]
                exact ⟨planned, rfl, rfl, rfl, ⟨completed.coreResult.acknowledged, rfl⟩⟩

theorem prepare_data_not_old (state : State) (input : Input) (stored : ReceiveStore.Result ReceiveReassembly.Receipt)
    (selected : ReceiveReassembly.prepare state.core state.receiveStore input (offeredWindow state) state.now = .data stored) :
    Seq.before input.packet.segment.sequence state.core.receiveNext = false := by
  unfold ReceiveReassembly.prepare at selected
  cases gated : ReceiveReassembly.initialGate state.core input (offeredWindow state) with
  | blocked reason kind => simp only [gated] at selected; cases selected
  | next amount =>
    simp only [gated] at selected
    split at selected
    · split at selected <;> cases selected
    · split at selected
      · cases selected
      · rename_i forward
        cases ordering : Seq.before input.packet.segment.sequence state.core.receiveNext <;> simp_all

theorem receiveEffect_stored (state : State) (input : Input) (stored : ReceiveStore.Result ReceiveReassembly.Receipt)
    (selected : (receiveEffect state input).stored = some stored) : StoreCommit state input (receiveEffect state input) stored := by
  unfold receiveEffect at selected ⊢
  dsimp only at selected ⊢
  split at selected
  · rename_i valid
    simp only [valid]
    exact receiveRaw_stored state input stored selected
  · cases selected



structure NoStore (before : State) (effect : ReceiveEffect) : Prop where
  runs : effect.runs = []
  state : effect.result.state.receiveStore = before.receiveStore

theorem receiveRaw_no_store (state : State) (input : Input) (absent : (receiveRaw state input).stored = none) :
    NoStore state (receiveRaw state input) :=
  ⟨(receiveRaw_effects state input).noRuns absent, (receiveRaw_effects state input).store absent⟩

theorem receiveEffect_no_store (state : State) (input : Input) (absent : (receiveEffect state input).stored = none) :
    NoStore state (receiveEffect state input) :=
  ⟨(receiveEffect_effects state input).noRuns absent, (receiveEffect_effects state input).store absent⟩

theorem receivedBytes_empty_of_not_accepted (state : State) (input : Input)
    (blocked : ∀ count size, (receive state input).decision ≠ .accepted (.receive count size)) :
    receivedBytes state input = [] := by
  cases stored : (receiveEffect state input).stored with
  | none =>
    have empty := (receiveEffect_no_store state input stored).runs
    simp only [receivedBytes, receiveRuns, empty, ReceiveStore.bytes, List.flatMap_nil]
  | some result =>
    obtain ⟨count, accepted⟩ := (receiveEffect_stored state input result stored).accepted
    exact False.elim (blocked count result.novel accepted)

theorem receiveStore_accept_initial (payload : List UInt8) (metadata : ReceiveReassembly.Receipt) (capacity : Nat)
    (nonempty : payload ≠ []) (fits : payload.length ≤ capacity) :
    ReceiveStore.accept ReceiveStore.initial 0 payload metadata capacity capacity = .ok
      ⟨⟨payload.length, 1, [], false⟩, 0, payload.length,
        [⟨0, payload, 0, metadata⟩], false⟩ := by
  simp [ReceiveStore.accept, ReceiveStore.initial, ReceiveStore.State.Valid, ReceiveStore.State.heldBytes,
    ReceiveStore.size, ReceiveStore.place, ReceiveStore.current, ReceiveStore.drain, ReceiveStore.Run.limit,
    nonempty, fits, Nat.not_lt.mpr fits]

theorem initialGate_of_ready (state : ERState) (input : Input)
    (ready : EstablishedReceive.Ready state input.packet.header input.packet.segment) :
    ReceiveReassembly.initialGate state input state.window = .next 0 := by
  simp only [ReceiveReassembly.initialGate, ready.1, not_true_eq_false, ite_false, ready.2.1,
    ne_eq, ready.2.2.2.1, ready.2.2.1, Bool.not_true, Bool.false_eq_true]

theorem prepare_initial_in_order (state : State) (input : Input)
    (ready : EstablishedReceive.Ready state.core input.packet.header input.packet.segment)
    (ackDisabled : state.ackReaction = none) (initial : state.receiveStore = ReceiveStore.initial)
    (nonempty : input.packet.segment.payload ≠ []) (fits : input.packet.segment.payload.length ≤ state.core.window)
    (sequence : input.packet.segment.sequence = state.core.receiveNext) :
    ReceiveReassembly.prepare state.core state.receiveStore input (offeredWindow state) state.now = .data
      ⟨⟨input.packet.segment.payload.length, 1, [], false⟩, 0, input.packet.segment.payload.length,
        [⟨0, input.packet.segment.payload, 0, ⟨input.packet.segment, input.packet.header, state.now⟩⟩], false⟩ := by
  have same : Seq.before state.core.receiveNext state.core.receiveNext = false := by
    simp [Seq.before, Seq.Before]
  simp only [ReceiveReassembly.prepare, offeredWindow, ackDisabled, initialGate_of_ready _ _ ready,
    List.isEmpty_eq_false_iff.mpr nonempty, Bool.false_eq_true, ite_false, same, initial, ReceiveReassembly.position,
    ReceiveStore.initial, sequence, Seq.distance_self, Nat.zero_add]
  have accepted := receiveStore_accept_initial input.packet.segment.payload
    ⟨input.packet.segment, input.packet.header, state.now⟩ state.core.window nonempty fits
  simp only [ReceiveStore.initial] at accepted
  rw [accepted]


theorem receive_of_empty_core (state : State) (input : Input) (coreAfter : ERState) (count size : Nat)
    (ack : Option EstablishedReceive.AckRequest) (valid : state.Valid)
    (disabled : state.recovery = none) (ackDisabled : state.ackReaction = none)
    (initial : state.receiveStore = ReceiveStore.initial) (empty : input.packet.segment.payload = [])
    (core : EstablishedReceive.receive state.core input = ⟨coreAfter, .accepted count size, ack⟩) :
    receive state input = ⟨receiveState state input coreAfter, .accepted (.receive count size), none, [], ack⟩ := by
  have selected : (EstablishedReceive.receive state.core input).decision = .accepted count size := by rw [core]
  have ready := EstablishedReceive.receive_accepted_ready state.core input count size selected
  have counted := (EstablishedReceive.receive_accepted state.core input count size selected).1
  have coreGate : EstablishedReceive.gateWithWindow state.core input.packet.header input.packet.segment state.core.window = .next count := by
    change EstablishedReceive.gate state.core input.packet.header input.packet.segment = _
    rw [EstablishedReceive.gate_of_ready _ _ _ ready, counted]
  have plan : ReceiveReassembly.prepare state.core state.receiveStore input (offeredWindow state) state.now = .acknowledgment count := by
    simp only [ReceiveReassembly.prepare, offeredWindow, ackDisabled, initialGate_of_ready _ _ ready,
      empty, List.isEmpty_nil, ite_true, coreGate]
  have old : receiveInOrder state input =
      ⟨receiveState state input coreAfter, .accepted (.receive count size), none, [], ack⟩ := by
    rw [receiveInOrder_without_recovery state input valid disabled ackDisabled, core]
  have finalValid : (receiveState state input coreAfter).Valid := receiveState_valid state input coreAfter valid
    (by simpa only [core] using EstablishedReceive.receive_valid state.core input valid.1)
  have finalStorage : (receiveState state input coreAfter).StorageValid := storage_valid_of_empty _ (by
    simp only [receiveState, windowState_receiveStore, initial, ReceiveStore.initial])
  have recoveryCoherent : RecoveryCoherent state := by simp only [RecoveryCoherent, disabled]
  have ackCoherent : AckCoherent state := by simp only [AckCoherent, ackDisabled]
  have storageCoherent : StorageCoherent state :=
    ⟨storage_valid_of_empty state (by rw [initial]; rfl), by simp only [ackDisabled]⟩
  have raw : receiveRaw state input = receivePlain
      ⟨receiveState state input coreAfter, .accepted (.receive count size), none, [], ack⟩ := by
    simp only [receiveRaw, valid, recoveryCoherent, ackCoherent, storageCoherent, not_true_eq_false, ite_false, plan, old]
  simp only [receive, receiveEffect, raw, receivePlain, finalValid, finalStorage, and_self, ite_true]



theorem applyRun_actual (state : ERState) (input : Input) (after : ERState) (count size : Nat)
    (ack : Option EstablishedReceive.AckRequest) (position receipt receivedAt : Nat)
    (core : EstablishedReceive.receive state input = ⟨after, .accepted count size, ack⟩) :
    ReceiveReassembly.applyRun state ⟨position, input.packet.segment.payload, receipt,
      ⟨input.packet.segment, input.packet.header, receivedAt⟩⟩ =
      .ok ⟨state, ⟨position, input.packet.segment.payload, receipt,
        ⟨input.packet.segment, input.packet.header, receivedAt⟩⟩, count, after⟩ := by
  change EstablishedReceive.evaluate state input.packet.header input.packet.segment = _ at core
  simp only [ReceiveReassembly.applyRun, ne_eq, not_true_eq_false, ite_false, core]


theorem processRuns_single_of_parts (state : State) (run : ReceiveReassembly.Run)
    (header : ReceiveReassembly.HeaderEffect) (after : State)
    (runEq : ReceiveReassembly.applyRun state.core run = .ok header)
    (headerEq : applyHeader state header = .ok after) :
    processRuns state [run] = .ok ⟨after, ⟨header.after, header.acknowledged, [header]⟩⟩ := by
  have core := (applyHeader_fields state header after headerEq).2.1
  simp only [processRuns.eq_2, runEq, headerEq, processRuns.eq_1, core, Nat.add_zero]


theorem applyHeader_actual (state : State) (input : Input) (after : ERState) (count position receipt : Nat)
    (disabled : state.recovery = none) :
    applyHeader state ⟨state.core, ⟨position, input.packet.segment.payload, receipt,
      ⟨input.packet.segment, input.packet.header, state.now⟩⟩, count, after⟩ = .ok (receiveState state input after) := by
  simp only [applyHeader, ne_eq, not_true_eq_false, ite_false, disabled]
  simp only [receiveState, disabled, Option.isSome_none, Bool.false_eq_true, ite_false]


def storedState (state : State) (store : ReceiveReassembly.Store) (reaction : Option AckReaction.State) : State :=
  { state with receiveStore := store, ackReaction := reaction }

@[simp] theorem storedState_core (state : State) (store : ReceiveReassembly.Store) (reaction : Option AckReaction.State) :
    (storedState state store reaction).core = state.core := rfl


theorem storedState_valid (state : State) (store : ReceiveReassembly.Store) (reaction : Option AckReaction.State)
    (valid : state.Valid) : (storedState state store reaction).Valid := valid

theorem receiveRaw_of_prepared (state : State) (input : Input) (stored : ReceiveStore.Result ReceiveReassembly.Receipt)
    (received : State) (coreResult : ReceiveReassembly.Applied)
    (valid : state.Valid) (recoveryCoherent : RecoveryCoherent state) (ackCoherent : AckCoherent state)
    (storageCoherent : StorageCoherent state) (ackDisabled : state.ackReaction = none)
    (plan : ReceiveReassembly.prepare state.core state.receiveStore input (offeredWindow state) state.now = .data stored)
    (processed : processRuns state stored.released = .ok ⟨received, coreResult⟩)
    (afterRecovery : RecoveryCoherent (storedState received stored.state none))
    (afterAck : AckCoherent (storedState received stored.state none))
    (afterStorage : StorageCoherent (storedState received stored.state none)) :
    receiveRaw state input =
      ⟨⟨storedState received stored.state none, .accepted (.receive coreResult.acknowledged stored.novel), none, [],
        some (ReceiveReassembly.request received.core received.core.window .data)⟩,
        stored.released, some stored, coreResult.headers, none⟩ := by
  simp only [receiveRaw, valid, recoveryCoherent, ackCoherent, storageCoherent, not_true_eq_false, ite_false,
    plan, processed, ackDisabled, Option.map_none]
  change (if ¬RecoveryCoherent (storedState received stored.state none) ∨
    ¬AckCoherent (storedState received stored.state none) ∨ ¬StorageCoherent (storedState received stored.state none)
    then _ else _) = _
  simp only [afterRecovery, afterAck, afterStorage, not_true_eq_false, or_self, ite_false]
  rfl


theorem receive_of_raw_valid (state : State) (input : Input) (effect : ReceiveEffect)
    (raw : receiveRaw state input = effect) (valid : effect.result.state.Valid)
    (storage : effect.result.state.StorageValid) : receive state input = effect.result := by
  simp only [receive, receiveEffect, raw, valid, storage, and_self, ite_true]

theorem receiveState_request (state : State) (input : Input) (after : ERState) :
    ReceiveReassembly.request (receiveState state input after).core
      (receiveState state input after).core.window .data = EstablishedReceive.request after .data := by
  unfold receiveState windowState
  split <;> rfl


theorem storedState_recovery_coherent (state : State) (store : ReceiveReassembly.Store) (reaction : Option AckReaction.State)
    (coherent : RecoveryCoherent state) : RecoveryCoherent (storedState state store reaction) := coherent

theorem recoveryCoherent_of_none (state : State) (disabled : state.recovery = none) : RecoveryCoherent state := by
  unfold RecoveryCoherent
  rw [disabled]
  trivial

theorem receive_of_in_order_core (state : State) (input : Input) (coreAfter : ERState) (count size : Nat)
    (ack : Option EstablishedReceive.AckRequest) (valid : state.Valid)
    (disabled : state.recovery = none) (ackDisabled : state.ackReaction = none)
    (initial : state.receiveStore = ReceiveStore.initial)
    (nonempty : input.packet.segment.payload ≠ []) (sequence : input.packet.segment.sequence = state.core.receiveNext)
    (core : EstablishedReceive.receive state.core input = ⟨coreAfter, .accepted count size, ack⟩) :
    receive state input =
      ⟨storedState (receiveState state input coreAfter) ⟨input.packet.segment.payload.length, 1, [], false⟩ none,
        .accepted (.receive count size), none, [], some (EstablishedReceive.request coreAfter .data)⟩ := by
  have selected : (EstablishedReceive.receive state.core input).decision = .accepted count size := by rw [core]
  have facts := EstablishedReceive.receive_accepted state.core input count size selected
  have ready := EstablishedReceive.receive_accepted_ready state.core input count size selected
  have afterValid : coreAfter.Valid := by simpa only [core] using EstablishedReceive.receive_valid state.core input valid.1
  let fresh : ReceiveStore.Result ReceiveReassembly.Receipt :=
    ⟨⟨input.packet.segment.payload.length, 1, [], false⟩, 0, input.packet.segment.payload.length,
      [⟨0, input.packet.segment.payload, 0, ⟨input.packet.segment, input.packet.header, state.now⟩⟩], false⟩
  let header : ReceiveReassembly.HeaderEffect := ⟨state.core, ⟨0, input.packet.segment.payload, 0,
    ⟨input.packet.segment, input.packet.header, state.now⟩⟩, count, coreAfter⟩
  have plan : ReceiveReassembly.prepare state.core state.receiveStore input (offeredWindow state) state.now = .data fresh :=
    prepare_initial_in_order state input ready ackDisabled initial nonempty facts.2.2.2.1 sequence
  have processed : processRuns state fresh.released =
      .ok ⟨receiveState state input coreAfter, ⟨coreAfter, count, [header]⟩⟩ :=
    processRuns_single_of_parts state _ header _ (applyRun_actual _ input _ count size ack 0 0 _ core)
      (applyHeader_actual state input coreAfter count 0 0 disabled)
  let after := storedState (receiveState state input coreAfter) fresh.state none
  have finalValid : after.Valid := storedState_valid (receiveState state input coreAfter) fresh.state none (receiveState_valid state input coreAfter valid afterValid)
  have finalStorage : after.StorageValid := storage_valid_of_empty after rfl
  have recoveryCoherent : RecoveryCoherent state := by simp only [RecoveryCoherent, disabled]
  have ackCoherent : AckCoherent state := by simp only [AckCoherent, ackDisabled]
  have storageCoherent : StorageCoherent state :=
    ⟨storage_valid_of_empty state (by rw [initial]; rfl), by simp only [ackDisabled]⟩
  have afterRecoveryCoherent : RecoveryCoherent after := storedState_recovery_coherent (receiveState state input coreAfter) fresh.state none
    (recoveryCoherent_of_none (receiveState state input coreAfter)
      ((receiveState_recovery state input coreAfter).trans disabled))
  have afterAckCoherent : AckCoherent after := trivial
  have afterStorageCoherent : StorageCoherent after := ⟨finalStorage, trivial⟩
  have raw := receiveRaw_of_prepared state input fresh (receiveState state input coreAfter) ⟨coreAfter, count, [header]⟩
    valid recoveryCoherent ackCoherent storageCoherent ackDisabled plan processed
    afterRecoveryCoherent afterAckCoherent afterStorageCoherent
  have received := receive_of_raw_valid state input _ raw finalValid finalStorage
  simp only [receiveState_request] at received
  rw [facts.2.2.1]
  exact received

end Netlib.Protocol.TCP.Endpoint
