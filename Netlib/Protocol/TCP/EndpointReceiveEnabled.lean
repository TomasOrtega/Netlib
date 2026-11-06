import Netlib.Protocol.TCP.EndpointReceiveFacts
import Netlib.Protocol.TCP.RecoveryEnabled
import Netlib.Protocol.TCP.AckReactionEnabled
import Netlib.Protocol.TCP.EndpointAckEnabled

/-!
# Receive actions from preceding endpoint conditions

The receive cursor, offered edge, receipt clock, and timing ledger are stored state.
The conclusions derive the actual receive computation and its released bytes.
-/

namespace Netlib.Protocol.TCP.ReceiveStore

theorem accept_frontier_empty (store : State Meta) (payload : List UInt8) (metadata : Meta)
    (window budget : Nat) (empty : store.held = []) (nonempty : payload ≠ [])
    (fits : payload.length ≤ window) (room : window ≤ budget) :
    accept store store.frontier payload metadata (store.frontier + window) budget = .ok
      ⟨⟨store.frontier + payload.length, store.nextID + 1, [], store.seenGap⟩,
        store.nextID, payload.length, [current store store.frontier payload metadata], false⟩ := by
  have oldValid : store.Valid (store.frontier + window) budget := by
    simp [State.Valid, empty, State.heldBytes, size, room]
  have afterValid : (⟨store.frontier + payload.length, store.nextID + 1, [], store.seenGap⟩ : State Meta).Valid
      (store.frontier + window) (budget - payload.length) := by
    simp [State.Valid, State.heldBytes, size]
    omega
  have physical : ¬budget < store.heldBytes + payload.length := by
    simp only [State.heldBytes, empty, size, List.map_nil, List.sum_nil, Nat.zero_add]
    omega
  simp only [accept, oldValid, not_true_eq_false, ite_false, nonempty, Nat.lt_irrefl,
    show ¬store.frontier + window < store.frontier + payload.length by omega,
    empty, place, Bool.false_eq_true, physical, current, drain, ite_true,
    Run.limit, decide_false, Bool.or_false]
  exact ite_eq_left afterValid

end Netlib.Protocol.TCP.ReceiveStore

namespace Netlib.Protocol.TCP.EstablishedReceive

theorem segmentLength_of_control_none (segment : Segment) (selected : control segment = none) :
    ReceiveWindow.segmentLength segment = segment.payload.length := by
  cases rst : Flags.rst segment.flags <;> cases syn : Flags.syn segment.flags <;>
    cases fin : Flags.fin segment.flags <;> simp [control, rst, syn, fin] at selected
  exact ReceiveWindow.segmentLength_no_control segment syn fin

theorem receive_in_order_of_forward (state : State) (input : Input) (valid : state.Valid)
    (tuple : input.packet.header = state.inbound) (control : control input.packet.segment = none)
    (ack : Flags.ack input.packet.segment.flags = true)
    (sequence : input.packet.segment.sequence = state.receiveNext)
    (fits : input.packet.segment.payload.length ≤ state.window)
    (forward : Seq.distance state.sendUna input.packet.segment.acknowledgment ≤ state.sent.length) :
    receive state input =
      ⟨commit state input.packet.segment.payload (Seq.distance state.sendUna input.packet.segment.acknowledgment),
        .accepted (Seq.distance state.sendUna input.packet.segment.acknowledgment) input.packet.segment.payload.length,
        if input.packet.segment.payload.isEmpty then none else
          some (request (commit state input.packet.segment.payload (Seq.distance state.sendUna input.packet.segment.acknowledgment)) .data)⟩ := by
  have accepts : ReceiveWindow.acceptsSegment state.receiveNext state.window input.packet.segment = true := by
    simp only [ReceiveWindow.acceptsSegment, sequence, segmentLength_of_control_none _ control]
    exact ReceiveWindow.in_order_fits _ _ _ fits
  rw [receive, evaluate_of_ready _ _ _ ⟨valid, tuple, accepts, control, ack⟩,
    acknowledgedCount_forward _ _ forward]
  exact finish_of_fits state input.packet.segment _ sequence fits

theorem commit_window (state : State) (payload : List UInt8) (count : Nat) :
    (commit state payload count).window = state.window - payload.length := by
  simp only [State.window, commit, List.length_append]
  omega

end Netlib.Protocol.TCP.EstablishedReceive

namespace Netlib.Protocol.TCP.Endpoint

def inOrderRun (state : State) (input : Input) : ReceiveReassembly.Run :=
  ReceiveStore.current state.receiveStore state.receiveStore.frontier input.packet.segment.payload
    ⟨input.packet.segment, input.packet.header, state.now⟩

def inOrderStore (state : State) (input : Input) : ReceiveStore.Result ReceiveReassembly.Receipt :=
  ⟨⟨state.receiveStore.frontier + input.packet.segment.payload.length, state.receiveStore.nextID + 1, [], state.receiveStore.seenGap⟩,
    state.receiveStore.nextID, input.packet.segment.payload.length, [inOrderRun state input], false⟩

theorem offeredWindow_le (state : State) (coherent : AckCoherent state) : offeredWindow state ≤ state.core.window := by
  cases reaction : state.ackReaction with
  | none => simp [offeredWindow, reaction]
  | some value =>
    simp only [AckCoherent, reaction] at coherent
    simpa only [offeredWindow, reaction, AckReaction.State.window] using coherent.2.1.2

theorem prepare_frontier_empty (state : State) (input : Input)
    (valid : state.Valid) (coherent : AckCoherent state) (empty : state.receiveStore.held = [])
    (tuple : input.packet.header = state.core.inbound) (control : EstablishedReceive.control input.packet.segment = none)
    (sequence : input.packet.segment.sequence = state.core.receiveNext)
    (nonempty : input.packet.segment.payload ≠ []) (fits : input.packet.segment.payload.length ≤ offeredWindow state) :
    ReceiveReassembly.prepare state.core state.receiveStore input (offeredWindow state) state.now = .data (inOrderStore state input) := by
  have accepts : ReceiveWindow.acceptsSegment state.core.receiveNext (offeredWindow state) input.packet.segment = true := by
    simp only [ReceiveWindow.acceptsSegment, sequence, EstablishedReceive.segmentLength_of_control_none _ control]
    exact ReceiveWindow.in_order_fits _ _ _ fits
  have gate : ReceiveReassembly.initialGate state.core input (offeredWindow state) = .next 0 := by
    simp only [ReceiveReassembly.initialGate, valid.1, not_true_eq_false, ite_false, tuple, ne_eq, control,
      accepts, Bool.not_true, Bool.false_eq_true]
  have sameOrder : Seq.before state.core.receiveNext state.core.receiveNext = false := by simp [Seq.before, Seq.Before]
  simp only [ReceiveReassembly.prepare, gate, List.isEmpty_eq_false_iff.mpr nonempty,
    Bool.false_eq_true, ite_false, ReceiveReassembly.position, sequence, sameOrder, Seq.distance_self, Nat.add_zero]
  rw [ReceiveStore.accept_frontier_empty state.receiveStore input.packet.segment.payload
    ⟨input.packet.segment, input.packet.header, state.now⟩ (offeredWindow state) state.core.window
    empty nonempty fits (offeredWindow_le state coherent)]
  rfl

def inOrderCount (state : State) (input : Input) : Nat :=
  Seq.distance state.core.sendUna input.packet.segment.acknowledgment

def inOrderCore (state : State) (input : Input) : ERState :=
  EstablishedReceive.commit state.core input.packet.segment.payload (inOrderCount state input)

def inOrderHeader (state : State) (input : Input) : ReceiveReassembly.HeaderEffect :=
  ⟨state.core, inOrderRun state input, inOrderCount state input, inOrderCore state input⟩

def inOrderReceivedWith (state : State) (input : Input) (after : Recovery.State) : State :=
  windowState state { state with
    core := inOrderCore state input
    recovery := some { after with duplicateAcks := 0 }
    lastAckWindow := some input.packet.segment.window.val } input.packet.segment

def inOrderAfterWith (state : State) (input : Input) (after : Recovery.State) (reaction : AckReaction.State) : State :=
  windowState state { state with
    core := inOrderCore state input
    recovery := some { after with duplicateAcks := 0 }
    lastAckWindow := some input.packet.segment.window.val
    receiveStore := (inOrderStore state input).state
    ackReaction := some (AckReaction.receiveRelease reaction state.now (state.core.receiveNext.add input.packet.segment.payload.length)
      input.packet.segment.payload.length input.packet.segment.payload.length false) } input.packet.segment

theorem inOrderCore_valid (state : State) (input : Input) (valid : state.Valid)
    (fits : input.packet.segment.payload.length ≤ state.core.window)
    (bounded : inOrderCount state input ≤ state.core.sent.length) : (inOrderCore state input).Valid :=
  EstablishedReceive.commit_valid _ _ _ valid.1 fits bounded

theorem applyHeader_inOrder_with (state : State) (input : Input) (recovery after : Recovery.State)
    (runtime : state.recovery = some recovery)
    (accepted : Recovery.acknowledgeAt recovery (inOrderCount state input) state.now = .ok after) :
    applyHeader state (inOrderHeader state input) =
      .ok (inOrderReceivedWith state input after) := by
  simp only [applyHeader, inOrderHeader, ne_eq, not_true_eq_false, ite_false, runtime,
    inOrderRun, ReceiveStore.current, accepted, Except.map, Option.isSome_some, ite_true]
  rfl

theorem inOrderReceivedWith_valid (state : State) (input : Input) (after : Recovery.State)
    (valid : state.Valid) (fits : input.packet.segment.payload.length ≤ state.core.window)
    (bounded : inOrderCount state input ≤ state.core.sent.length) : (inOrderReceivedWith state input after).Valid := by
  unfold inOrderReceivedWith
  apply windowState_valid
  exact ⟨inOrderCore_valid state input valid fits bounded, valid.2⟩

theorem windowState_recovery (before after : State) (segment : Segment) :
    (windowState before after segment).recovery = after.recovery := by
  unfold windowState
  split <;> rfl

theorem windowState_effectiveMSS (before after : State) (segment : Segment) :
    (windowState before after segment).effectiveMSS = after.effectiveMSS := by
  unfold windowState
  split <;> rfl

theorem windowState_lastAckWindow (before after : State) (segment : Segment) :
    (windowState before after segment).lastAckWindow = after.lastAckWindow := by
  unfold windowState
  split <;> rfl

theorem recoveryCoherent_of_runtime (state : State) (recovery : Recovery.State)
    (runtime : state.recovery = some recovery) (valid : recovery.Valid)
    (smss : recovery.smss = state.effectiveMSS) (flight : Recovery.flight recovery = state.core.sent.length)
    (known : AckWindowKnown state) : RecoveryCoherent state := by
  unfold RecoveryCoherent
  rw [runtime]
  exact ⟨valid, smss, flight, known⟩

theorem ackWindowKnown_of_field (state : State) (window : Fin 65536)
    (stored : state.lastAckWindow = some window.val) : AckWindowKnown state := by
  unfold AckWindowKnown
  rw [stored]
  exact Nat.le_of_lt_succ window.isLt

theorem inOrderReceivedWith_recovery (state : State) (input : Input) (after : Recovery.State)
    (valid : after.Valid) (smss : after.smss = state.effectiveMSS)
    (flight : Recovery.flight after = state.core.sent.length - inOrderCount state input) :
    RecoveryCoherent (inOrderReceivedWith state input after) := by
  let value : State := { state with
    core := inOrderCore state input
    recovery := some { after with duplicateAcks := 0 }
    lastAckWindow := some input.packet.segment.window.val }
  have resident : (inOrderReceivedWith state input after).recovery = some { after with duplicateAcks := 0 } :=
    windowState_recovery state value input.packet.segment
  have effective : (inOrderReceivedWith state input after).effectiveMSS = state.effectiveMSS :=
    windowState_effectiveMSS state value input.packet.segment
  have core : (inOrderReceivedWith state input after).core = inOrderCore state input :=
    windowState_core state value input.packet.segment
  have stored : (inOrderReceivedWith state input after).lastAckWindow = some input.packet.segment.window.val :=
    windowState_lastAckWindow state value input.packet.segment
  have bound : (inOrderCore state input).sent.length = state.core.sent.length - inOrderCount state input := by
    exact List.length_drop
  exact recoveryCoherent_of_runtime (inOrderReceivedWith state input after) { after with duplicateAcks := 0 } resident valid
    (smss.trans effective.symm) (flight.trans (bound.symm.trans (congrArg (fun value : ERState => value.sent.length) core).symm))
    (ackWindowKnown_of_field (inOrderReceivedWith state input after) input.packet.segment.window stored)

theorem windowState_recovery_coherent (before after : State) (segment : Segment) (coherent : RecoveryCoherent after) :
    RecoveryCoherent (windowState before after segment) := by
  unfold windowState
  split <;> exact coherent

theorem windowState_ack_coherent (before after : State) (segment : Segment) (coherent : AckCoherent after) :
    AckCoherent (windowState before after segment) := by
  unfold windowState
  split <;> exact coherent

theorem inOrderAfterWith_valid (state : State) (input : Input) (after : Recovery.State) (reaction : AckReaction.State)
    (valid : state.Valid) (fits : input.packet.segment.payload.length ≤ state.core.window)
    (bounded : inOrderCount state input ≤ state.core.sent.length) : (inOrderAfterWith state input after reaction).Valid := by
  apply windowState_valid
  exact ⟨inOrderCore_valid state input valid fits bounded, valid.2⟩

theorem inOrderAfterWith_recovery (state : State) (input : Input) (after : Recovery.State) (reaction : AckReaction.State)
    (valid : after.Valid) (smss : after.smss = state.effectiveMSS)
    (flight : Recovery.flight after = state.core.sent.length - inOrderCount state input) :
    RecoveryCoherent (inOrderAfterWith state input after reaction) := by
  apply windowState_recovery_coherent
  refine ⟨valid, smss, ?_, Nat.le_of_lt_succ input.packet.segment.window.isLt⟩
  exact flight.trans List.length_drop.symm

theorem reaction_coherent_transport (reaction : AckReaction.State)
    (leftCursor rightCursor : Seq) (leftFree rightFree leftMSS rightMSS : Nat)
    (cursor : leftCursor = rightCursor) (free : leftFree = rightFree) (mss : leftMSS = rightMSS)
    (coherent : reaction.Coherent rightCursor rightFree rightMSS) :
    reaction.Coherent leftCursor leftFree leftMSS := by
  cases cursor
  cases free
  cases mss
  exact coherent

theorem inOrderAfterWith_ack (state : State) (input : Input) (after : Recovery.State) (reaction : AckReaction.State)
    (stored : state.ackReaction = some reaction) (coherent : AckCoherent state)
    (fits : input.packet.segment.payload.length ≤ offeredWindow state) :
    AckCoherent (inOrderAfterWith state input after reaction) := by
  have old := coherent
  simp only [AckCoherent, stored] at old
  have fit : input.packet.segment.payload.length ≤ reaction.window := by simpa only [offeredWindow, stored] using fits
  have next := AckReaction.receiveRelease_coherent reaction state.now state.core.receiveNext
    input.packet.segment.payload.length input.packet.segment.payload.length false
    state.core.window state.localReceiveMSS.limit old.2 fit
  apply windowState_ack_coherent
  constructor
  · rfl
  · exact reaction_coherent_transport _ _ _ _ _ _ _ rfl
      (EstablishedReceive.commit_window state.core input.packet.segment.payload (inOrderCount state input)) rfl next

theorem store_valid_empty (store : ReceiveReassembly.Store) (window budget : Nat)
    (empty : store.held = []) (fits : window ≤ budget) : store.Valid (store.frontier + window) budget := by
  simp [ReceiveStore.State.Valid, empty, ReceiveStore.State.heldBytes, ReceiveStore.size, fits]

theorem windowState_storage_coherent (before after : State) (segment : Segment) (coherent : StorageCoherent after) :
    StorageCoherent (windowState before after segment) := by
  unfold windowState
  split <;> exact coherent

theorem inOrderAfterWith_storage (state : State) (input : Input) (after : Recovery.State) (reaction : AckReaction.State)
    (stored : state.ackReaction = some reaction) (ack : AckCoherent state) (storage : StorageCoherent state)
    (fits : input.packet.segment.payload.length ≤ offeredWindow state) :
    StorageCoherent (inOrderAfterWith state input after reaction) := by
  have oldAck := ack
  simp only [AckCoherent, stored] at oldAck
  have oldStorage := storage.2
  simp only [stored] at oldStorage
  have fit : input.packet.segment.payload.length ≤ reaction.window := by simpa only [offeredWindow, stored] using fits
  have next := AckReaction.receiveRelease_coherent reaction state.now state.core.receiveNext
    input.packet.segment.payload.length input.packet.segment.payload.length false
    state.core.window state.localReceiveMSS.limit oldAck.2 fit
  apply windowState_storage_coherent
  constructor
  · apply store_valid_empty _ _ _ rfl (Nat.le_refl _)
  · constructor
    · exact congrArg (fun position => position + input.packet.segment.payload.length) oldStorage.1
    · apply store_valid_empty _ _ _ rfl
      change _ ≤ (inOrderCore state input).window
      rw [inOrderCore, EstablishedReceive.commit_window]
      exact next.1.2

theorem storedState_windowState (before after : State) (segment : Segment)
    (store : ReceiveReassembly.Store) (reaction : Option AckReaction.State) :
    storedState (windowState before after segment) store reaction =
      windowState before (storedState after store reaction) segment := by
  unfold windowState storedState
  split <;> rfl

theorem inOrderAfterWith_eq_stored (state : State) (input : Input) (after : Recovery.State) (reaction : AckReaction.State) :
    storedState (inOrderReceivedWith state input after) (inOrderStore state input).state
      (some (AckReaction.receiveRelease reaction state.now (inOrderReceivedWith state input after).core.receiveNext
        input.packet.segment.payload.length input.packet.segment.payload.length false)) =
      inOrderAfterWith state input after reaction := by
  unfold inOrderReceivedWith inOrderAfterWith storedState windowState
  split <;> rfl

private theorem receiveRaw_of_active_prepared (state : State) (input : Input)
    (stored : ReceiveStore.Result ReceiveReassembly.Receipt) (received : State) (coreResult : ReceiveReassembly.Applied)
    (reaction : Option AckReaction.State) (after : State)
    (valid : state.Valid) (recovery : RecoveryCoherent state) (ack : AckCoherent state) (storage : StorageCoherent state)
    (plan : ReceiveReassembly.prepare state.core state.receiveStore input (offeredWindow state) state.now = .data stored)
    (processed : processRuns state stored.released = .ok ⟨received, coreResult⟩)
    (reacted : state.ackReaction.map (fun before => AckReaction.receiveRelease before state.now received.core.receiveNext
      stored.novel (ReceiveStore.size stored.released) (ReceiveReassembly.immediate state.core state.receiveStore input)) = reaction)
    (changed : storedState received stored.state reaction = after)
    (afterRecovery : RecoveryCoherent after) (afterAck : AckCoherent after) (afterStorage : StorageCoherent after) :
    receiveRaw state input =
      ⟨⟨after, .accepted (.receive coreResult.acknowledged stored.novel), none, [],
          some (ReceiveReassembly.request after.core (offeredWindow after) .data)⟩,
        stored.released, some stored, coreResult.headers, none⟩ := by
  have nextRecovery : RecoveryCoherent (storedState received stored.state reaction) := changed.symm ▸ afterRecovery
  have nextAck : AckCoherent (storedState received stored.state reaction) := changed.symm ▸ afterAck
  have nextStorage : StorageCoherent (storedState received stored.state reaction) := changed.symm ▸ afterStorage
  simp only [receiveRaw, valid, recovery, ack, storage, not_true_eq_false, ite_false, plan, processed, reacted]
  change (if ¬RecoveryCoherent (storedState received stored.state reaction) ∨
      ¬AckCoherent (storedState received stored.state reaction) ∨ ¬StorageCoherent (storedState received stored.state reaction)
    then _ else _) = _
  simp only [nextRecovery, nextAck, nextStorage, not_true_eq_false, or_self, ite_false]
  exact congrArg (fun value : State =>
    (⟨⟨value, .accepted (.receive coreResult.acknowledged stored.novel), none, [],
        some (ReceiveReassembly.request value.core (offeredWindow value) .data)⟩,
      stored.released, some stored, coreResult.headers, none⟩ : ReceiveEffect)) changed

theorem receiveRaw_inOrder_of_acknowledged (state : State) (input : Input) (recovery acknowledged : Recovery.State)
    (reaction : AckReaction.State) (valid : state.Valid) (recoveryCoherent : RecoveryCoherent state)
    (ackCoherent : AckCoherent state) (storageCoherent : StorageCoherent state)
    (runtime : state.recovery = some recovery) (ackRuntime : state.ackReaction = some reaction)
    (empty : state.receiveStore.held = []) (tuple : input.packet.header = state.core.inbound)
    (controls : EstablishedReceive.control input.packet.segment = none) (ack : Flags.ack input.packet.segment.flags = true)
    (sequence : input.packet.segment.sequence = state.core.receiveNext) (nonempty : input.packet.segment.payload ≠ [])
    (fits : input.packet.segment.payload.length ≤ offeredWindow state)
    (bounded : inOrderCount state input ≤ state.core.sent.length)
    (accepted : Recovery.acknowledgeAt recovery (inOrderCount state input) state.now = .ok acknowledged)
    (nextValid : acknowledged.Valid) (nextMSS : acknowledged.smss = state.effectiveMSS)
    (nextFlight : Recovery.flight acknowledged = state.core.sent.length - inOrderCount state input) :
    let after := inOrderAfterWith state input acknowledged reaction
    receiveRaw state input =
      ⟨⟨after, .accepted (.receive (inOrderCount state input) input.packet.segment.payload.length), none, [],
          some (ReceiveReassembly.request after.core (offeredWindow after) .data)⟩,
        [inOrderRun state input], some (inOrderStore state input), [inOrderHeader state input], none⟩ := by
  dsimp only
  let afterRecovery : Recovery.State := acknowledged
  let after := inOrderAfterWith state input afterRecovery reaction
  have fitsCore : input.packet.segment.payload.length ≤ state.core.window :=
    Nat.le_trans fits (offeredWindow_le state ackCoherent)
  have core := EstablishedReceive.receive_in_order_of_forward state.core input valid.1 tuple controls ack
    sequence fitsCore bounded
  have prepare := prepare_frontier_empty state input valid ackCoherent empty tuple controls sequence nonempty fits
  have header : ReceiveReassembly.applyRun state.core (inOrderRun state input) = .ok (inOrderHeader state input) :=
    applyRun_actual state.core input (inOrderCore state input) (inOrderCount state input)
      input.packet.segment.payload.length _ state.receiveStore.frontier state.receiveStore.nextID state.now core
  have apply := applyHeader_inOrder_with state input recovery acknowledged runtime accepted
  have processed := processRuns_single_of_parts state (inOrderRun state input) (inOrderHeader state input)
    (inOrderReceivedWith state input afterRecovery) header apply
  have finalRecovery : RecoveryCoherent after :=
    inOrderAfterWith_recovery state input afterRecovery reaction nextValid nextMSS nextFlight
  have finalAck : AckCoherent after := inOrderAfterWith_ack state input afterRecovery reaction ackRuntime ackCoherent fits
  have finalStorage : StorageCoherent after :=
    inOrderAfterWith_storage state input afterRecovery reaction ackRuntime ackCoherent storageCoherent fits
  have notImmediate : ReceiveReassembly.immediate state.core state.receiveStore input = false := by
    simp only [ReceiveReassembly.immediate, sequence, ne_eq, not_true_eq_false, decide_false, empty,
      List.isEmpty_nil, Bool.not_true, Bool.or_self]
  let reactionAfter := some (AckReaction.receiveRelease reaction state.now (inOrderReceivedWith state input afterRecovery).core.receiveNext
    input.packet.segment.payload.length input.packet.segment.payload.length false)
  have reacted : state.ackReaction.map (fun before => AckReaction.receiveRelease before state.now
      (inOrderReceivedWith state input afterRecovery).core.receiveNext
      (inOrderStore state input).novel (ReceiveStore.size (inOrderStore state input).released)
      (ReceiveReassembly.immediate state.core state.receiveStore input)) = reactionAfter := by
    simp only [ackRuntime, Option.map_some, notImmediate]
    rfl
  exact receiveRaw_of_active_prepared state input (inOrderStore state input)
    (inOrderReceivedWith state input afterRecovery)
    ⟨inOrderCore state input, inOrderCount state input, [inOrderHeader state input]⟩ reactionAfter after
    valid recoveryCoherent ackCoherent storageCoherent prepare processed reacted
    (inOrderAfterWith_eq_stored state input afterRecovery reaction) finalRecovery finalAck finalStorage

private theorem receiveEffect_of_raw_valid (state : State) (input : Input) (effect : ReceiveEffect)
    (raw : receiveRaw state input = effect) (valid : effect.result.state.Valid)
    (storage : effect.result.state.StorageValid) : receiveEffect state input = effect := by
  simp only [receiveEffect, raw, valid, storage, and_self, ite_true]

theorem receive_inOrder_enabled (state : State) (input : Input) (recovery : Recovery.State) (reaction : AckReaction.State)
    (valid : state.Valid) (recoveryCoherent : RecoveryCoherent state) (ackCoherent : AckCoherent state)
    (storageCoherent : StorageCoherent state) (runtime : state.recovery = some recovery)
    (ackRuntime : state.ackReaction = some reaction) (sent : recovery.SentBy recovery.now)
    (empty : state.receiveStore.held = []) (tuple : input.packet.header = state.core.inbound)
    (controls : EstablishedReceive.control input.packet.segment = none) (ack : Flags.ack input.packet.segment.flags = true)
    (sequence : input.packet.segment.sequence = state.core.receiveNext) (nonempty : input.packet.segment.payload ≠ [])
    (fits : input.packet.segment.payload.length ≤ offeredWindow state)
    (bounded : inOrderCount state input ≤ state.core.sent.length) :
    ∃ acknowledged after,
      Recovery.acknowledgeAt recovery (inOrderCount state input) state.now = .ok acknowledged ∧
      after = inOrderAfterWith state input acknowledged reaction ∧
      receive state input =
        ⟨after, .accepted (.receive (inOrderCount state input) input.packet.segment.payload.length), none, [],
          some (ReceiveReassembly.request after.core (offeredWindow after) .data)⟩ ∧
      receiveRuns state input = [inOrderRun state input] ∧ receivedBytes state input = input.packet.segment.payload ∧
      after.Valid ∧ RecoveryCoherent after ∧ AckCoherent after ∧ StorageCoherent after := by
  have old := recoveryCoherent
  simp only [RecoveryCoherent, runtime] at old
  have countBound : inOrderCount state input ≤ Recovery.flight recovery := by rw [old.2.2.1]; exact bounded
  obtain ⟨acknowledged, computed, nextValid, nextMSS, nextFlight, _⟩ :=
    Recovery.acknowledgeAt_current_success recovery (inOrderCount state input) old.1 countBound sent
  have timing : state.now = recovery.now := by simp [State.now, runtime]
  have accepted : Recovery.acknowledgeAt recovery (inOrderCount state input) state.now = .ok acknowledged := by
    rw [timing]
    exact computed
  have mss : acknowledged.smss = state.effectiveMSS := nextMSS.trans old.2.1
  have flight : Recovery.flight acknowledged = state.core.sent.length - inOrderCount state input := by
    rw [old.2.2.1] at nextFlight
    exact nextFlight
  have raw := receiveRaw_inOrder_of_acknowledged state input recovery acknowledged reaction valid recoveryCoherent
    ackCoherent storageCoherent runtime ackRuntime empty tuple controls ack sequence nonempty fits bounded
    accepted nextValid mss flight
  have afterValid : (inOrderAfterWith state input acknowledged reaction).Valid := inOrderAfterWith_valid state input acknowledged reaction valid
    (Nat.le_trans fits (offeredWindow_le state ackCoherent)) bounded
  have afterRecovery := inOrderAfterWith_recovery state input acknowledged reaction nextValid mss flight
  have afterAck := inOrderAfterWith_ack state input acknowledged reaction ackRuntime ackCoherent fits
  have afterStorage := inOrderAfterWith_storage state input acknowledged reaction ackRuntime ackCoherent storageCoherent fits
  generalize changed : inOrderAfterWith state input acknowledged reaction = after at raw afterValid afterRecovery afterAck afterStorage
  refine ⟨acknowledged, after, accepted, changed.symm, ?_⟩
  let completed : ReceiveEffect :=
    ⟨⟨after, .accepted (.receive (inOrderCount state input) input.packet.segment.payload.length), none, [],
        some (ReceiveReassembly.request after.core (offeredWindow after) .data)⟩,
      [inOrderRun state input], some (inOrderStore state input), [inOrderHeader state input], none⟩
  have rawComputed : receiveRaw state input = completed := raw
  have actual : receiveEffect state input = completed :=
    receiveEffect_of_raw_valid state input completed rawComputed afterValid afterStorage.1
  refine ⟨congrArg ReceiveEffect.result actual, congrArg ReceiveEffect.runs actual, ?_,
    afterValid, afterRecovery, afterAck, afterStorage⟩
  have released : (receiveEffect state input).runs = [inOrderRun state input] := congrArg ReceiveEffect.runs actual
  change ReceiveStore.bytes (receiveEffect state input).runs = _
  rw [released]
  simp only [ReceiveStore.bytes, List.flatMap_cons, List.flatMap_nil, List.append_nil, inOrderRun, ReceiveStore.current]

theorem windowState_ackReaction (before after : State) (segment : Segment) :
    (windowState before after segment).ackReaction = after.ackReaction := by
  unfold windowState
  split <;> rfl

theorem ackPrepared_of_fields (state : State) (reaction : AckReaction.State) (coherent : AckCoherent state)
    (stored : state.ackReaction = some reaction) (timely : reaction.WithinTime state.now)
    (covered : reaction.Covered state.core.capacity state.core.window state.effectiveMSS) : AckPrepared state := by
  refine ⟨coherent, ?_⟩
  rw [stored]
  exact ⟨timely, covered⟩

theorem reaction_covered_transport (reaction : AckReaction.State)
    (leftCapacity rightCapacity leftFree rightFree leftMSS rightMSS : Nat)
    (capacity : leftCapacity = rightCapacity) (free : leftFree = rightFree) (mss : leftMSS = rightMSS)
    (covered : reaction.Covered rightCapacity rightFree rightMSS) :
    reaction.Covered leftCapacity leftFree leftMSS := by
  cases capacity
  cases free
  cases mss
  exact covered

theorem inOrderAfterWith_prepared (state : State) (input : Input) (after : Recovery.State) (reaction : AckReaction.State)
    (stored : state.ackReaction = some reaction) (prepared : AckPrepared state)
    (fits : input.packet.segment.payload.length ≤ offeredWindow state) (clock : after.now = state.now) :
    AckPrepared (inOrderAfterWith state input after reaction) := by
  have oldAck := prepared.1
  simp only [AckCoherent, stored] at oldAck
  have oldWork := prepared.2
  simp only [stored] at oldWork
  have fit : input.packet.segment.payload.length ≤ reaction.window := by simpa only [offeredWindow, stored] using fits
  let changed := AckReaction.receiveRelease reaction state.now (state.core.receiveNext.add input.packet.segment.payload.length)
    input.packet.segment.payload.length input.packet.segment.payload.length false
  have timely : changed.WithinTime state.now := AckReaction.receiveRelease_within reaction state.now
    (state.core.receiveNext.add input.packet.segment.payload.length) input.packet.segment.payload.length
    input.packet.segment.payload.length false oldWork.1
  have covered : changed.Covered state.core.capacity (state.core.window - input.packet.segment.payload.length) state.effectiveMSS :=
    AckReaction.receiveRelease_covered reaction state.now (state.core.receiveNext.add input.packet.segment.payload.length)
      input.packet.segment.payload.length input.packet.segment.payload.length false state.core.capacity state.core.window
      state.effectiveMSS oldWork.2 oldAck.2.1 fit
  let value : State := { state with
    core := inOrderCore state input
    recovery := some { after with duplicateAcks := 0 }
    lastAckWindow := some input.packet.segment.window.val
    receiveStore := (inOrderStore state input).state
    ackReaction := some changed }
  have source : (inOrderAfterWith state input after reaction).ackReaction = some changed :=
    windowState_ackReaction state value input.packet.segment
  have core : (inOrderAfterWith state input after reaction).core = inOrderCore state input :=
    windowState_core state value input.packet.segment
  have effective : (inOrderAfterWith state input after reaction).effectiveMSS = state.effectiveMSS :=
    windowState_effectiveMSS state value input.packet.segment
  have runtime : (inOrderAfterWith state input after reaction).recovery = some { after with duplicateAcks := 0 } :=
    windowState_recovery state value input.packet.segment
  have now : (inOrderAfterWith state input after reaction).now = state.now := by
    simp only [State.now, runtime, Option.map_some, Option.getD_some]
    exact clock
  have capacity : (inOrderAfterWith state input after reaction).core.capacity = state.core.capacity :=
    (congrArg EstablishedReceive.State.capacity core).trans rfl
  have window : (inOrderAfterWith state input after reaction).core.window = state.core.window - input.packet.segment.payload.length :=
    (congrArg EstablishedReceive.State.window core).trans (EstablishedReceive.commit_window state.core input.packet.segment.payload (inOrderCount state input))
  exact ackPrepared_of_fields (inOrderAfterWith state input after reaction) changed
    (inOrderAfterWith_ack state input after reaction stored prepared.1 fits) source
    (now.symm ▸ timely) (reaction_covered_transport changed _ _ _ _ _ _ capacity window effective covered)

theorem receiveRelease_pending (reaction : AckReaction.State) (time : Nat) (cursor : Seq)
    (novel released : Nat) (immediate : Bool) :
    (AckReaction.receiveRelease reaction time cursor novel released immediate).work.pending ≠ [] := by
  simp only [AckReaction.receiveRelease, AckReaction.T.issue, Netlib.Theory.TimedReaction.issue]
  exact List.append_ne_nil_of_right_ne_nil reaction.work.pending (List.cons_ne_nil _ _)

theorem responseAvailable_of_pending (state : State) (reaction : AckReaction.State)
    (stored : state.ackReaction = some reaction) (pending : reaction.work.pending ≠ []) : ResponseAvailable state false := by
  unfold ResponseAvailable
  rw [stored]
  exact ⟨pending, by intro impossible; cases impossible⟩

theorem inOrderAfterWith_response (state : State) (input : Input) (after : Recovery.State) (reaction : AckReaction.State) :
    ResponseAvailable (inOrderAfterWith state input after reaction) false := by
  let changed := AckReaction.receiveRelease reaction state.now (state.core.receiveNext.add input.packet.segment.payload.length)
    input.packet.segment.payload.length input.packet.segment.payload.length false
  let value : State := { state with
    core := inOrderCore state input
    recovery := some { after with duplicateAcks := 0 }
    lastAckWindow := some input.packet.segment.window.val
    receiveStore := (inOrderStore state input).state
    ackReaction := some changed }
  have source : (inOrderAfterWith state input after reaction).ackReaction = some changed :=
    windowState_ackReaction state value input.packet.segment
  exact responseAvailable_of_pending (inOrderAfterWith state input after reaction) changed source
    (receiveRelease_pending reaction state.now (state.core.receiveNext.add input.packet.segment.payload.length)
      input.packet.segment.payload.length input.packet.segment.payload.length false)
private theorem ackPrepared_of_equal (before after : State) (same : before = after) (prepared : AckPrepared after) :
    AckPrepared before := by
  cases same
  exact prepared

theorem receive_inOrder_prepared (state : State) (input : Input) (recovery : Recovery.State) (reaction : AckReaction.State)
    (valid : state.Valid) (recoveryCoherent : RecoveryCoherent state) (prepared : AckPrepared state)
    (storageCoherent : StorageCoherent state) (runtime : state.recovery = some recovery)
    (ackRuntime : state.ackReaction = some reaction) (sent : recovery.SentBy recovery.now)
    (empty : state.receiveStore.held = []) (tuple : input.packet.header = state.core.inbound)
    (controls : EstablishedReceive.control input.packet.segment = none) (ack : Flags.ack input.packet.segment.flags = true)
    (sequence : input.packet.segment.sequence = state.core.receiveNext) (nonempty : input.packet.segment.payload ≠ [])
    (fits : input.packet.segment.payload.length ≤ offeredWindow state)
    (bounded : inOrderCount state input ≤ state.core.sent.length) :
    ∃ acknowledged after,
      Recovery.acknowledgeAt recovery (inOrderCount state input) state.now = .ok acknowledged ∧
      after = inOrderAfterWith state input acknowledged reaction ∧
      receive state input =
        ⟨after, .accepted (.receive (inOrderCount state input) input.packet.segment.payload.length), none, [],
          some (ReceiveReassembly.request after.core (offeredWindow after) .data)⟩ ∧
      receiveRuns state input = [inOrderRun state input] ∧ receivedBytes state input = input.packet.segment.payload ∧
      after.Valid ∧ RecoveryCoherent after ∧ AckPrepared after ∧ StorageCoherent after := by
  obtain ⟨acknowledged, after, accepted, afterEq, actual, runs, bytes, afterValid, afterRecovery, _, afterStorage⟩ :=
    receive_inOrder_enabled state input recovery reaction valid recoveryCoherent prepared.1 storageCoherent
      runtime ackRuntime sent empty tuple controls ack sequence nonempty fits bounded
  have clock := Recovery.acknowledgeAt_now recovery (inOrderCount state input) state.now acknowledged accepted
  have endpointClock : state.now = recovery.now := by simp [State.now, runtime]
  have afterPrepared : AckPrepared after := ackPrepared_of_equal after
    (inOrderAfterWith state input acknowledged reaction) afterEq
    (inOrderAfterWith_prepared state input acknowledged reaction ackRuntime prepared fits (clock.trans endpointClock.symm))
  exact ⟨acknowledged, after, accepted, afterEq, actual, runs, bytes, afterValid, afterRecovery, afterPrepared, afterStorage⟩


private theorem responseAvailable_of_equal (before after : State) (same : before = after)
    (available : ResponseAvailable after false) : ResponseAvailable before false := by
  cases same
  exact available

theorem receive_inOrder_emits_ack (state : State) (input : Input) (recovery : Recovery.State) (reaction : AckReaction.State)
    (valid : state.Valid) (recoveryCoherent : RecoveryCoherent state) (prepared : AckPrepared state)
    (storageCoherent : StorageCoherent state) (runtime : state.recovery = some recovery)
    (ackRuntime : state.ackReaction = some reaction) (sent : recovery.SentBy recovery.now)
    (empty : state.receiveStore.held = []) (tuple : input.packet.header = state.core.inbound)
    (controls : EstablishedReceive.control input.packet.segment = none) (ack : Flags.ack input.packet.segment.flags = true)
    (sequence : input.packet.segment.sequence = state.core.receiveNext) (nonempty : input.packet.segment.payload ≠ [])
    (fits : input.packet.segment.payload.length ≤ offeredWindow state)
    (bounded : inOrderCount state input ≤ state.core.sent.length) :
    ∃ after output,
      receive state input =
        ⟨after, .accepted (.receive (inOrderCount state input) input.packet.segment.payload.length), none, [],
          some (ReceiveReassembly.request after.core (offeredWindow after) .data)⟩ ∧
      receiveRuns state input = [inOrderRun state input] ∧ receivedBytes state input = input.packet.segment.payload ∧
      emitAck after true = ⟨outputState after, .accepted .emitAck, some output, [], none⟩ ∧
      output.packet.segment.payload = [] ∧
      output.packet.segment.acknowledgment = state.core.receiveNext.add input.packet.segment.payload.length ∧
      output.packet.segment.window.val = outputWindow after ∧ AckPrepared (outputState after) := by
  obtain ⟨acknowledged, after, _, afterEq, actual, runs, bytes, afterValid, _, afterPrepared, _⟩ :=
    receive_inOrder_prepared state input recovery reaction valid recoveryCoherent prepared storageCoherent runtime
      ackRuntime sent empty tuple controls ack sequence nonempty fits bounded
  have available := responseAvailable_of_equal after (inOrderAfterWith state input acknowledged reaction) afterEq
    (inOrderAfterWith_response state input acknowledged reaction)
  obtain ⟨output, emitted, encoded⟩ := emitAck_success_enabled after afterValid afterPrepared available
  have fields := emit_transport after [] output encoded
  have cursor := (receive_effects state input).2.2.2.2.1
  rw [actual, bytes] at cursor
  exact ⟨after, output, actual, runs, bytes, emitted, emit_payload after [] output encoded,
    fields.2.2.1.trans cursor, fields.2.2.2.1, outputState_ackPrepared after afterPrepared⟩

end Netlib.Protocol.TCP.Endpoint
