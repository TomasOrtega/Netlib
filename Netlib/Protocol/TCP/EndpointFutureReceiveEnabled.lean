import Netlib.Protocol.TCP.EndpointGapReceiveEnabled

/-!
# Holding a future payload from current endpoint facts

The new run retains the actual header and local receipt time.
No queued header is processed before the missing prefix arrives.
-/

namespace Netlib.Protocol.TCP.ReceiveStore

theorem accept_future_empty (store : State Meta) (gap : Nat) (payload : List UInt8) (metadata : Meta)
    (window budget : Nat) (empty : store.held = []) (nonempty : payload ≠ [])
    (positive : 0 < gap) (fits : gap + payload.length ≤ window) (room : window ≤ budget) :
    accept store (store.frontier + gap) payload metadata (store.frontier + window) budget = .ok
      ⟨⟨store.frontier, store.nextID + 1, [current store (store.frontier + gap) payload metadata], true⟩,
        store.nextID, payload.length, [], false⟩ := by
  have oldValid : store.Valid (store.frontier + window) budget := by
    simp [State.Valid, empty, State.heldBytes, size, room]
  have afterValid :
      (⟨store.frontier, store.nextID + 1, [current store (store.frontier + gap) payload metadata], true⟩ : State Meta).Valid
        (store.frontier + window) budget := by
    simp [State.Valid, State.heldBytes, size, Run.limit, current, nonempty]
    omega
  have physical : ¬budget < store.heldBytes + payload.length := by
    simp only [State.heldBytes, empty, size, List.map_nil, List.sum_nil, Nat.zero_add]
    omega
  have ahead : store.frontier < store.frontier + gap := by omega
  have different : store.frontier + gap ≠ store.frontier := by omega
  simp only [accept, oldValid, not_true_eq_false, ite_false, nonempty,
    show ¬store.frontier + gap < store.frontier by omega,
    show ¬store.frontier + window < store.frontier + gap + payload.length by omega,
    empty, place, Bool.false_eq_true, physical, drain, current, different,
    ahead, decide_true, Bool.or_true, size, List.map_nil, List.sum_nil, Nat.sub_zero]
  exact ite_eq_left afterValid

end Netlib.Protocol.TCP.ReceiveStore

namespace Netlib.Protocol.TCP.Endpoint

structure FutureReceiveConditions (state : State) (input : Input) (gap : Nat)
    (recovery : Recovery.State) (reaction : AckReaction.State) : Prop where
  valid : state.Valid
  coherent : RecoveryCoherent state
  prepared : AckPrepared state
  storage : StorageCoherent state
  runtime : state.recovery = some recovery
  ackRuntime : state.ackReaction = some reaction
  idle : recovery.outstanding = []
  empty : state.receiveStore.held = []
  nonempty : input.packet.segment.payload ≠ []
  tuple : input.packet.header = state.core.inbound
  controls : EstablishedReceive.control input.packet.segment = none
  ack : Flags.ack input.packet.segment.flags = true
  sequence : input.packet.segment.sequence = state.core.receiveNext.add gap
  positive : 0 < gap
  fits : gap + input.packet.segment.payload.length ≤ offeredWindow state
  oldAck : Seq.distance input.packet.segment.acknowledgment state.core.sendUna ≤ EstablishedReceive.maxSendWindow

def futureRun (state : State) (input : Input) (gap : Nat) : ReceiveReassembly.Run :=
  ReceiveStore.current state.receiveStore (state.receiveStore.frontier + gap) input.packet.segment.payload
    ⟨input.packet.segment, input.packet.header, state.now⟩

def futureStore (state : State) (input : Input) (gap : Nat) : ReceiveStore.Result ReceiveReassembly.Receipt :=
  ⟨⟨state.receiveStore.frontier, state.receiveStore.nextID + 1, [futureRun state input gap], true⟩,
    state.receiveStore.nextID, input.packet.segment.payload.length, [], false⟩

def futureReaction (state : State) (input : Input) (reaction : AckReaction.State) : AckReaction.State :=
  AckReaction.receiveRelease reaction state.now state.core.receiveNext input.packet.segment.payload.length 0 true

def futureAfter (state : State) (input : Input) (gap : Nat) (reaction : AckReaction.State) : State :=
  storedState state (futureStore state input gap).state (some (futureReaction state input reaction))

def futureEffect (state : State) (input : Input) (gap : Nat) (reaction : AckReaction.State) : ReceiveEffect :=
  ⟨⟨futureAfter state input gap reaction, .accepted (.receive 0 input.packet.segment.payload.length), none, [],
      some (ReceiveReassembly.request state.core (offeredWindow (futureAfter state input gap reaction)) .data)⟩,
    [], some (futureStore state input gap), [], none⟩

variable {state : State} {input : Input} {gap : Nat} {recovery : Recovery.State} {reaction : AckReaction.State}

theorem FutureReceiveConditions.physical (conditions : FutureReceiveConditions state input gap recovery reaction) :
    input.packet.segment.payload.length ≤ state.physicalFree := by
  have offered := offeredWindow_le state conditions.prepared.1
  simp only [State.physicalFree, ReceiveStore.State.heldBytes, conditions.empty,
    ReceiveStore.size, List.map_nil, List.sum_nil, Nat.sub_zero]
  have fits := conditions.fits
  omega

theorem FutureReceiveConditions.acknowledged (conditions : FutureReceiveConditions state input gap recovery reaction) :
    EstablishedReceive.acknowledgedCount state.core input.packet.segment.acknowledgment = some 0 :=
  EstablishedReceive.acknowledgedCount_old state.core input.packet.segment.acknowledgment
    conditions.valid.1.2.2.2.2.2 conditions.oldAck

theorem FutureReceiveConditions.ahead (conditions : FutureReceiveConditions state input gap recovery reaction) :
    Seq.Before state.core.receiveNext input.packet.segment.sequence := by
  have room := offeredWindow_le state conditions.prepared.1
  have window := EstablishedReceive.State.window_bound state.core conditions.valid.1
  have fits := conditions.fits
  have positive := conditions.positive
  have gapBound : gap < Seq.modulus := by unfold Seq.modulus; omega
  simp only [Seq.Before, conditions.sequence, Seq.distance_add, Nat.mod_eq_of_lt gapBound]
  exact ⟨conditions.positive, by unfold Seq.halfSpace; omega⟩

theorem prepare_future_empty (conditions : FutureReceiveConditions state input gap recovery reaction) :
    ReceiveReassembly.prepare state.core state.receiveStore input (offeredWindow state) state.now =
      .data (futureStore state input gap) := by
  have room := offeredWindow_le state conditions.prepared.1
  have window := EstablishedReceive.State.window_bound state.core conditions.valid.1
  have fits := conditions.fits
  have positive := conditions.positive
  have payloadPositive := List.length_pos_iff.mpr conditions.nonempty
  have gapBound : gap < Seq.modulus := by unfold Seq.modulus; omega
  have accepts : ReceiveWindow.acceptsSegment state.core.receiveNext (offeredWindow state) input.packet.segment = true := by
    rw [ReceiveWindow.acceptsSegment, EstablishedReceive.segmentLength_of_control_none _ conditions.controls,
      conditions.sequence, ReceiveWindow.coordinate_positive _ _ _ _ (by omega)
        (List.length_pos_iff.mpr conditions.nonempty)]
    exact .inl (by rw [Nat.mod_eq_of_lt gapBound]; omega)
  have gate : ReceiveReassembly.initialGate state.core input (offeredWindow state) = .next 0 := by
    simp only [ReceiveReassembly.initialGate, conditions.valid.1, not_true_eq_false, ite_false,
      conditions.tuple, ne_eq, conditions.controls, accepts, Bool.not_true, Bool.false_eq_true]
  have notBefore : Seq.before (state.core.receiveNext.add gap) state.core.receiveNext = false := by
    simp only [Seq.before, decide_eq_false_iff_not]
    rw [← conditions.sequence]
    exact Seq.before_asymm _ _ conditions.ahead
  simp only [ReceiveReassembly.prepare, gate, List.isEmpty_eq_false_iff.mpr conditions.nonempty,
    Bool.false_eq_true, ite_false, ReceiveReassembly.position, conditions.sequence,
    notBefore, Seq.distance_add, Nat.mod_eq_of_lt gapBound]
  rw [ReceiveStore.accept_future_empty state.receiveStore gap input.packet.segment.payload
    ⟨input.packet.segment, input.packet.header, state.now⟩ (offeredWindow state) state.core.window
    conditions.empty conditions.nonempty conditions.positive conditions.fits room]
  rfl

theorem FutureReceiveConditions.after_valid (conditions : FutureReceiveConditions state input gap recovery reaction) :
    (futureAfter state input gap reaction).Valid := conditions.valid

theorem FutureReceiveConditions.after_recovery (conditions : FutureReceiveConditions state input gap recovery reaction) :
    RecoveryCoherent (futureAfter state input gap reaction) := conditions.coherent

theorem FutureReceiveConditions.after_ack (conditions : FutureReceiveConditions state input gap recovery reaction) :
    AckCoherent (futureAfter state input gap reaction) := by
  have old : state.recovery.isSome = true ∧
      reaction.Coherent state.core.receiveNext state.core.window state.localReceiveMSS.limit := by
    simpa only [AckCoherent, conditions.ackRuntime] using conditions.prepared.1
  have next := AckReaction.receiveRelease_coherent reaction state.now state.core.receiveNext
    input.packet.segment.payload.length 0 true state.core.window state.localReceiveMSS.limit old.2 (Nat.zero_le _)
  change state.recovery.isSome = true ∧ (futureReaction state input reaction).Coherent
    state.core.receiveNext state.core.window state.localReceiveMSS.limit
  exact ⟨old.1, by simpa only [futureReaction, Seq.add_zero, Nat.sub_zero] using next⟩

theorem FutureReceiveConditions.after_storage (conditions : FutureReceiveConditions state input gap recovery reaction) :
    StorageCoherent (futureAfter state input gap reaction) := by
  have accepted := ReceiveStore.accept_future_empty state.receiveStore gap input.packet.segment.payload
    ⟨input.packet.segment, input.packet.header, state.now⟩ (offeredWindow state) state.core.window
    conditions.empty conditions.nonempty conditions.positive conditions.fits (offeredWindow_le state conditions.prepared.1)
  have stored : (futureStore state input gap).state.Valid
      (state.receiveStore.frontier + offeredWindow state) state.core.window := by
    simpa only [futureStore, futureRun, ReceiveStore.size, List.map_nil, List.sum_nil, Nat.sub_zero] using
      ReceiveStore.accept_valid state.receiveStore _ _ _ _ _ _ accepted
  have old : reaction.advertisement.frontier = state.receiveStore.frontier := by
    exact (show reaction.advertisement.frontier = state.receiveStore.frontier ∧ _ from
      by simpa only [conditions.ackRuntime] using conditions.storage.2).1
  constructor
  · change (futureStore state input gap).state.Valid
      (state.receiveStore.frontier + state.core.window) state.core.window
    apply ReceiveStore.State.valid_mono _ _ _ _ _ stored
    · exact Nat.add_le_add_left (offeredWindow_le state conditions.prepared.1) _
    · exact Nat.le_refl _
    · change state.receiveStore.frontier + state.core.window - state.receiveStore.frontier ≤ state.core.window
      omega
  · constructor
    · change reaction.advertisement.frontier + 0 = state.receiveStore.frontier
      simpa only [Nat.add_zero] using old
    · simpa only [futureAfter, storedState, futureStore, offeredWindow, futureReaction, AckReaction.receiveRelease,
        AckReaction.State.window, ReceiveAdvertisement.consume, ReceiveAdvertisement.State.window,
        Nat.add_zero, conditions.ackRuntime] using stored

theorem FutureReceiveConditions.after_prepared (conditions : FutureReceiveConditions state input gap recovery reaction) :
    AckPrepared (futureAfter state input gap reaction) := by
  have oldAck : state.recovery.isSome = true ∧
      reaction.Coherent state.core.receiveNext state.core.window state.localReceiveMSS.limit := by
    simpa only [AckCoherent, conditions.ackRuntime] using conditions.prepared.1
  have oldWork : reaction.WithinTime state.now ∧
      reaction.Covered state.core.capacity state.core.window state.effectiveMSS := by
    simpa only [conditions.ackRuntime] using conditions.prepared.2
  apply ackPrepared_of_fields _ (futureReaction state input reaction) conditions.after_ack rfl
  · exact AckReaction.receiveRelease_within reaction state.now state.core.receiveNext
      input.packet.segment.payload.length 0 true oldWork.1
  · simpa only [futureAfter, storedState, futureReaction, Nat.sub_zero] using
      AckReaction.receiveRelease_covered reaction state.now state.core.receiveNext input.packet.segment.payload.length
        0 true state.core.capacity state.core.window state.effectiveMSS oldWork.2 oldAck.2.1 (Nat.zero_le _)

theorem futureReaction_due (state : State) (input : Input) (reaction : AckReaction.State) :
    ∃ due, (futureReaction state input reaction).due = some due ∧ due ≤ state.now := by
  have due := Theory.TimedReaction.issue_due reaction.work state.now
    (AckReaction.demand (futureReaction state input reaction) .data state.core.receiveNext
      input.packet.segment.payload.length 0) 0
  change (futureReaction state input reaction).due = _ at due
  cases previous : Theory.TimedReaction.pendingDue reaction.work with
  | none => exact ⟨state.now, by simpa only [previous, Nat.add_zero] using due, Nat.le_refl _⟩
  | some deadline => exact ⟨min deadline state.now, by simpa only [previous, Nat.add_zero] using due, Nat.min_le_right _ _⟩

theorem FutureReceiveConditions.after_response (_conditions : FutureReceiveConditions state input gap recovery reaction) :
    ResponseAvailable (futureAfter state input gap reaction) true := by
  change (futureReaction state input reaction).work.pending ≠ [] ∧
    (true = true → ∃ due, (futureReaction state input reaction).due = some due ∧ due ≤ state.now)
  exact ⟨receiveRelease_pending reaction state.now state.core.receiveNext input.packet.segment.payload.length 0 true,
    fun _ => futureReaction_due state input reaction⟩

structure FutureHeld (state : State) (input : Input) (gap : Nat) (reaction : AckReaction.State) : Prop where
  actual : receiveEffect state input = futureEffect state input gap reaction
  valid : (futureAfter state input gap reaction).Valid
  coherent : RecoveryCoherent (futureAfter state input gap reaction)
  prepared : AckPrepared (futureAfter state input gap reaction)
  storage : StorageCoherent (futureAfter state input gap reaction)
  response : ResponseAvailable (futureAfter state input gap reaction) true

theorem receive_future_enabled (conditions : FutureReceiveConditions state input gap recovery reaction) :
    FutureHeld state input gap reaction := by
  have different : input.packet.segment.sequence ≠ state.core.receiveNext := by
    intro same
    have ahead := conditions.ahead
    rw [same] at ahead
    exact Seq.before_irrefl _ ahead
  have immediate : ReceiveReassembly.immediate state.core state.receiveStore input = true := by
    simp only [ReceiveReassembly.immediate, different, ne_eq, not_false_eq_true, decide_true, Bool.true_or]
  have raw : receiveRaw state input = futureEffect state input gap reaction := by
    simp only [receiveRaw, conditions.valid, conditions.coherent, conditions.prepared.1, conditions.storage,
      not_true_eq_false, ite_false, prepare_future_empty conditions, futureStore, processRuns,
      conditions.ackRuntime, Option.map_some, immediate, ReceiveStore.size, List.map_nil, List.sum_nil]
    change (let after := futureAfter state input gap reaction;
      if ¬RecoveryCoherent after ∨ ¬AckCoherent after ∨ ¬StorageCoherent after then _ else _) = _
    simp only [conditions.after_recovery, conditions.after_ack, conditions.after_storage,
      not_true_eq_false, or_self, ite_false]
    rfl
  refine ⟨?_, conditions.after_valid, conditions.after_recovery, conditions.after_prepared,
    conditions.after_storage, conditions.after_response⟩
  simp only [receiveEffect, raw, futureEffect, conditions.after_valid, conditions.after_storage.1, and_self, ite_true]

theorem FutureHeld.receive (held : FutureHeld state input gap reaction) :
    receive state input =
      ⟨futureAfter state input gap reaction, .accepted (.receive 0 input.packet.segment.payload.length), none, [],
        some (ReceiveReassembly.request state.core (offeredWindow (futureAfter state input gap reaction)) .data)⟩ :=
  congrArg ReceiveEffect.result held.actual

theorem FutureHeld.allocation (held : FutureHeld state input gap reaction) :
    (receiveEffect state input).stored = some (futureStore state input gap) ∧
      (receiveEffect state input).runs = [] ∧ (receiveEffect state input).headers = [] ∧
      (receiveEffect state input).failure = none := by
  rw [held.actual]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem futureAfter_frame (state : State) (input : Input) (gap : Nat) (reaction : AckReaction.State) :
    { futureAfter state input gap reaction with receiveStore := state.receiveStore, ackReaction := state.ackReaction } = state := rfl

theorem futureRun_fields (state : State) (input : Input) (gap : Nat) :
    (futureRun state input gap).position = state.receiveStore.frontier + gap ∧
      (futureRun state input gap).bytes = input.packet.segment.payload ∧
      (futureRun state input gap).receipt = state.receiveStore.nextID ∧
      (futureRun state input gap).metadata = ⟨input.packet.segment, input.packet.header, state.now⟩ :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem futureAfter_store (state : State) (input : Input) (gap : Nat) (reaction : AckReaction.State) :
    (futureAfter state input gap reaction).receiveStore =
      ⟨state.receiveStore.frontier, state.receiveStore.nextID + 1, [futureRun state input gap], true⟩ := rfl

theorem FutureHeld.no_release (held : FutureHeld state input gap reaction) :
    receiveRuns state input = [] ∧ receivedBytes state input = [] ∧ (Endpoint.receive state input).read = [] := by
  rw [receivedBytes, receiveRuns, held.actual, held.receive]
  exact ⟨rfl, rfl, rfl⟩

theorem FutureHeld.dispatch (held : FutureHeld state input gap reaction) :
    ∃ output, dispatchAck (futureAfter state input gap reaction) true =
        ⟨outputState (futureAfter state input gap reaction), .accepted .dispatchAck, some output, [], none⟩ ∧
      emit (futureAfter state input gap reaction) [] = .ok output ∧
      output.packet.segment.payload = [] ∧ output.packet.header = Output.reverse state.core.inbound ∧
      output.packet.segment.sequence = state.core.sendNext ∧
      output.packet.segment.acknowledgment = state.core.receiveNext ∧
      AckPrepared (outputState (futureAfter state input gap reaction)) := by
  obtain ⟨output, actual, encoded⟩ := dispatchAck_success_enabled _ held.valid held.prepared held.response
  have fields := emit_transport _ [] output encoded
  exact ⟨output, actual, encoded, emit_payload _ [] output encoded, fields.1, fields.2.1,
    fields.2.2.1, outputState_ackPrepared _ held.prepared⟩

end Netlib.Protocol.TCP.Endpoint
