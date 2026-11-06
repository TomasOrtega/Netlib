import Netlib.Protocol.TCP.EndpointReceiveEnabled
import Netlib.Protocol.TCP.ReceiveWindowEnabled

/-!
# Active ACK receipt and old-range feedback

A covering ACK retires the actual outstanding bytes.
An old data retry requests another ACK without releasing those bytes again.
-/

namespace Netlib.Protocol.TCP.EstablishedReceive

theorem gateWithWindow_empty_forward (state : State) (input : Input) (window : Nat)
    (valid : state.Valid) (tuple : input.packet.header = state.inbound)
    (controls : control input.packet.segment = none) (ack : Flags.ack input.packet.segment.flags = true)
    (sequence : input.packet.segment.sequence = state.receiveNext) (empty : input.packet.segment.payload = [])
    (bounded : Seq.distance state.sendUna input.packet.segment.acknowledgment ≤ state.sent.length) :
    gateWithWindow state input.packet.header input.packet.segment window =
      .next (Seq.distance state.sendUna input.packet.segment.acknowledgment) := by
  have accepts : ReceiveWindow.acceptsSegment state.receiveNext window input.packet.segment = true := by
    simp only [ReceiveWindow.acceptsSegment, sequence, segmentLength_of_control_none _ controls, empty, List.length_nil]
    exact ReceiveWindow.in_order_fits state.receiveNext window 0 (Nat.zero_le _)
  have counted := acknowledgedCount_forward state input.packet.segment.acknowledgment bounded
  change acknowledgedCountAt state.sendUna state.sent.length input.packet.segment.acknowledgment = _ at counted
  simp only [gateWithWindow, gateTailAt, valid, not_true_eq_false, ite_false, tuple, ne_eq,
    controls, accepts, Bool.not_true, Bool.false_eq_true, ack, counted]

theorem receiveWithWindow_empty_forward (state : State) (input : Input) (window : Nat)
    (valid : state.Valid) (tuple : input.packet.header = state.inbound)
    (controls : control input.packet.segment = none) (ack : Flags.ack input.packet.segment.flags = true)
    (sequence : input.packet.segment.sequence = state.receiveNext) (empty : input.packet.segment.payload = [])
    (bounded : Seq.distance state.sendUna input.packet.segment.acknowledgment ≤ state.sent.length) :
    receiveWithWindow state input window =
      ⟨commit state [] (Seq.distance state.sendUna input.packet.segment.acknowledgment),
        .accepted (Seq.distance state.sendUna input.packet.segment.acknowledgment) 0, none⟩ := by
  have gate := gateWithWindow_empty_forward state input window valid tuple controls ack sequence empty bounded
  have fits : input.packet.segment.payload.length ≤ state.window := by simp only [empty, List.length_nil, Nat.zero_le]
  simp only [receiveWithWindow, evaluateWithWindow, gate, empty, List.length_nil, Nat.not_lt_zero, ite_false]
  rw [finish_of_fits state input.packet.segment _ sequence fits]
  simp only [empty, List.isEmpty_nil, ite_true, withAckWindow, Option.map_none]
  rfl

end Netlib.Protocol.TCP.EstablishedReceive

namespace Netlib.Protocol.TCP.Endpoint

theorem prepare_empty_forward (state : State) (input : Input) (valid : state.Valid)
    (tuple : input.packet.header = state.core.inbound) (controls : EstablishedReceive.control input.packet.segment = none)
    (ack : Flags.ack input.packet.segment.flags = true) (sequence : input.packet.segment.sequence = state.core.receiveNext)
    (empty : input.packet.segment.payload = []) (bounded : inOrderCount state input ≤ state.core.sent.length) :
    ReceiveReassembly.prepare state.core state.receiveStore input (offeredWindow state) state.now =
      .acknowledgment (inOrderCount state input) := by
  have accepts : ReceiveWindow.acceptsSegment state.core.receiveNext (offeredWindow state) input.packet.segment = true := by
    simp only [ReceiveWindow.acceptsSegment, sequence, EstablishedReceive.segmentLength_of_control_none _ controls,
      empty, List.length_nil]
    exact ReceiveWindow.in_order_fits _ _ 0 (Nat.zero_le _)
  have gate : ReceiveReassembly.initialGate state.core input (offeredWindow state) = .next 0 := by
    simp only [ReceiveReassembly.initialGate, valid.1, not_true_eq_false, ite_false, tuple, ne_eq,
      controls, accepts, Bool.not_true, Bool.false_eq_true]
  have next := EstablishedReceive.gateWithWindow_empty_forward state.core input (offeredWindow state)
    valid.1 tuple controls ack sequence empty bounded
  simp only [ReceiveReassembly.prepare, gate, empty, List.isEmpty_nil, ite_true, next]
  rfl

theorem receiveRecovery_positive (state : State) (segment : Segment) (count : Nat) (recovery after : Recovery.State)
    (runtime : state.recovery = some recovery) (positive : 0 < count)
    (accepted : Recovery.acknowledge recovery count = .ok after) :
    receiveRecovery state segment count = .ok (some { after with duplicateAcks := 0 }) := by
  have notDuplicate : qualifyingDuplicate state segment count = false := by
    apply Bool.eq_false_iff.mpr
    intro selected
    have zero := (of_decide_eq_true selected).1
    exact Nat.ne_of_gt positive zero
  simp only [receiveRecovery, runtime, accepted, bind, Except.bind, notDuplicate, Bool.false_eq_true, ite_false]
  rfl

theorem receiveState_runtime_eq (state : State) (input : Input) (core : ERState) (recovery after : Recovery.State)
    (reaction : AckReaction.State) (runtime : state.recovery = some recovery) (ackRuntime : state.ackReaction = some reaction) :
    { receiveState state input core with
      recovery := some { after with duplicateAcks := 0 }
      ackReaction := some reaction } =
      windowState state { state with
        core := core
        recovery := some { after with duplicateAcks := 0 }
        lastAckWindow := some input.packet.segment.window.val } input.packet.segment := by
  unfold receiveState windowState
  simp only [runtime, Option.isSome_some, ite_true]
  split <;> simp only [ackRuntime] <;> rfl

theorem receiveInOrder_empty_of_acknowledged (state : State) (input : Input) (recovery after : Recovery.State)
    (reaction : AckReaction.State) (valid : state.Valid) (coherent : RecoveryCoherent state) (ackCoherent : AckCoherent state)
    (runtime : state.recovery = some recovery) (ackRuntime : state.ackReaction = some reaction)
    (tuple : input.packet.header = state.core.inbound) (controls : EstablishedReceive.control input.packet.segment = none)
    (ack : Flags.ack input.packet.segment.flags = true) (sequence : input.packet.segment.sequence = state.core.receiveNext)
    (empty : input.packet.segment.payload = []) (bounded : inOrderCount state input ≤ state.core.sent.length)
    (positive : 0 < inOrderCount state input) (accepted : Recovery.acknowledge recovery (inOrderCount state input) = .ok after) :
    receiveInOrder state input =
      ⟨inOrderReceivedWith state input after, .accepted (.receive (inOrderCount state input) 0), none, [], none⟩ := by
  have core := EstablishedReceive.receiveWithWindow_empty_forward state.core input reaction.window valid.1
    tuple controls ack sequence empty bounded
  have model : receiveModel state input =
      ⟨inOrderCore state input, .accepted (inOrderCount state input) 0, none⟩ := by
    simpa only [receiveModel, ackRuntime, inOrderCore, inOrderCount, empty] using core
  have recoveryStep := receiveRecovery_positive state input.packet.segment (inOrderCount state input) recovery after runtime positive accepted
  simp only [receiveInOrder, valid, coherent, ackCoherent, not_true_eq_false, ite_false, model, recoveryStep,
    issueRequest, ackRuntime]
  rw [receiveState_runtime_eq state input (inOrderCore state input) recovery after reaction runtime ackRuntime]
  rfl

theorem windowState_ack_prepared (before after : State) (segment : Segment) (prepared : AckPrepared after) :
    AckPrepared (windowState before after segment) := by
  unfold windowState
  split <;> exact prepared

theorem inOrderReceivedWith_prepared_empty (state : State) (input : Input) (recovery after : Recovery.State)
    (reaction : AckReaction.State) (prepared : AckPrepared state) (runtime : state.recovery = some recovery)
    (ackRuntime : state.ackReaction = some reaction) (empty : input.packet.segment.payload = [])
    (clock : after.now = recovery.now) : AckPrepared (inOrderReceivedWith state input after) := by
  unfold inOrderReceivedWith
  apply windowState_ack_prepared
  have old := prepared
  simp only [AckPrepared, AckCoherent, ackRuntime, runtime, Option.isSome_some, true_and,
    State.now, Option.map_some, Option.getD_some] at old ⊢
  simpa only [inOrderCore, EstablishedReceive.commit, empty, List.length_nil, Seq.add_zero, List.append_nil, clock, EstablishedReceive.State.window] using old

private theorem receiveEffect_of_raw_ready (state : State) (input : Input) (effect : ReceiveEffect)
    (raw : receiveRaw state input = effect) (valid : effect.result.state.Valid)
    (storage : effect.result.state.StorageValid) : receiveEffect state input = effect := by
  simp only [receiveEffect, raw, valid, storage, and_self, ite_true]

theorem receive_empty_full_ack (state : State) (input : Input) (recovery : Recovery.State) (reaction : AckReaction.State)
    (valid : state.Valid) (coherent : RecoveryCoherent state) (prepared : AckPrepared state)
    (storage : StorageCoherent state) (runtime : state.recovery = some recovery)
    (ackRuntime : state.ackReaction = some reaction) (positive : recovery.Positive)
    (flight : 0 < state.core.sent.length) (emptyHeld : state.receiveStore.held = [])
    (tuple : input.packet.header = state.core.inbound) (controls : EstablishedReceive.control input.packet.segment = none)
    (ack : Flags.ack input.packet.segment.flags = true) (sequence : input.packet.segment.sequence = state.core.receiveNext)
    (empty : input.packet.segment.payload = []) (covers : inOrderCount state input = state.core.sent.length) :
    ∃ acknowledged after,
      Recovery.acknowledge recovery (Recovery.flight recovery) = .ok acknowledged ∧
      after = inOrderReceivedWith state input acknowledged ∧
      receive state input = ⟨after, .accepted (.receive state.core.sent.length 0), none, [], none⟩ ∧
      receiveRuns state input = [] ∧ receivedBytes state input = [] ∧ after.core.sent = [] ∧
      after.core.sendUna = state.core.sendNext ∧ after.Valid ∧ AckPrepared after ∧
      acknowledged.outstanding = [] ∧ acknowledged.deadline = none ∧ acknowledged.timeoutCount = 0 := by
  have old := coherent
  simp only [RecoveryCoherent, runtime] at old
  have timerFlight : 0 < Recovery.flight recovery := by rw [old.2.2.1]; exact flight
  obtain ⟨acknowledged, accepted, nextValid, nextMSS, nextFlight, clock, cleared, deadline, _, attempts⟩ :=
    Recovery.acknowledge_full_success recovery old.1 positive timerFlight
  have countEq : inOrderCount state input = Recovery.flight recovery := covers.trans old.2.2.1.symm
  have acknowledgedInput : Recovery.acknowledge recovery (inOrderCount state input) = .ok acknowledged := by
    rw [countEq]
    exact accepted
  have bounded : inOrderCount state input ≤ state.core.sent.length := Nat.le_of_eq covers
  have countPositive : 0 < inOrderCount state input := by rw [covers]; exact flight
  have planned := prepare_empty_forward state input valid tuple controls ack sequence empty bounded
  have computed := receiveInOrder_empty_of_acknowledged state input recovery acknowledged reaction valid coherent prepared.1
    runtime ackRuntime tuple controls ack sequence empty bounded countPositive acknowledgedInput
  have raw : receiveRaw state input = receivePlain
      ⟨inOrderReceivedWith state input acknowledged, .accepted (.receive (inOrderCount state input) 0), none, [], none⟩ := by
    simp only [receiveRaw, valid, coherent, prepared.1, storage, not_true_eq_false, ite_false, planned, computed]
  have afterValid : (inOrderReceivedWith state input acknowledged).Valid := inOrderReceivedWith_valid state input acknowledged
    valid (by simp only [empty, List.length_nil, Nat.zero_le]) bounded
  have afterPrepared := inOrderReceivedWith_prepared_empty state input recovery acknowledged reaction prepared runtime ackRuntime empty clock
  have storeFrame : (inOrderReceivedWith state input acknowledged).receiveStore = state.receiveStore :=
    windowState_receiveStore state _ input.packet.segment
  have afterStorage : (inOrderReceivedWith state input acknowledged).StorageValid :=
    storage_valid_of_empty _ ((congrArg (fun store : ReceiveReassembly.Store => store.held) storeFrame).trans emptyHeld)
  generalize changed : inOrderReceivedWith state input acknowledged = after at raw afterValid afterPrepared afterStorage storeFrame
  refine ⟨acknowledged, after, accepted, changed.symm, ?_⟩
  let effect : ReceiveEffect := receivePlain ⟨after, .accepted (.receive (inOrderCount state input) 0), none, [], none⟩
  have actual : receiveEffect state input = effect := receiveEffect_of_raw_ready state input effect raw afterValid afterStorage
  have selected : receive state input = ⟨after, .accepted (.receive state.core.sent.length 0), none, [], none⟩ := by
    simpa only [receive, effect, receivePlain, covers] using congrArg ReceiveEffect.result actual
  have retired := (receive_effects state input).2.1
  have advanced := (receive_effects state input).2.2.2.2.2.1
  rw [selected] at retired advanced
  simp only [receiveRetired, List.drop_length] at retired
  have sentCursor := valid.1.2.2.2.2.1
  have cursor : after.core.sendUna = state.core.sendNext := advanced.trans sentCursor
  refine ⟨selected, congrArg ReceiveEffect.runs actual, ?_, retired, cursor, afterValid, afterPrepared, cleared, deadline, attempts⟩
  change ReceiveStore.bytes (receiveEffect state input).runs = []
  rw [congrArg ReceiveEffect.runs actual]
  rfl

def sequenceAfter (state : State) (reaction : AckReaction.State) : State :=
  { state with ackReaction := some (AckReaction.receiveSequence reaction state.now state.core.receiveNext) }

theorem old_whole_range_sequence (state : State) (input : Input) (valid : state.Valid)
    (tuple : input.packet.header = state.core.inbound) (controls : EstablishedReceive.control input.packet.segment = none)
    (nonempty : input.packet.segment.payload ≠ [])
    (ends : input.packet.segment.sequence.add input.packet.segment.payload.length = state.core.receiveNext)
    (epoch : input.packet.segment.payload.length + offeredWindow state ≤ Seq.modulus) :
    ReceiveReassembly.prepare state.core state.receiveStore input (offeredWindow state) state.now =
      .blocked (.reject .sequence) (some (ReceiveReassembly.request state.core (offeredWindow state) .sequence)) := by
  have outside : ReceiveWindow.acceptsSegment state.core.receiveNext (offeredWindow state) input.packet.segment = false := by
    rw [ReceiveWindow.acceptsSegment, EstablishedReceive.segmentLength_of_control_none _ controls, ← ends]
    exact ReceiveWindow.whole_old_range_rejected input.packet.segment.sequence (offeredWindow state)
      input.packet.segment.payload.length (List.length_pos_iff.mpr nonempty) epoch
  simp only [ReceiveReassembly.prepare, ReceiveReassembly.initialGate, valid.1, not_true_eq_false, ite_false,
    tuple, ne_eq, controls, outside, Bool.not_false, ite_true, Option.map_some]

theorem sequenceAfter_prepared (state : State) (reaction : AckReaction.State)
    (stored : state.ackReaction = some reaction) (prepared : AckPrepared state) :
    AckPrepared (sequenceAfter state reaction) := by
  have old := prepared.1
  simp only [AckCoherent, stored] at old
  have work := prepared.2
  simp only [stored] at work
  let next := AckReaction.receiveSequence reaction state.now state.core.receiveNext
  have coherent : AckCoherent (sequenceAfter state reaction) :=
    ⟨old.1, AckReaction.receiveSequence_coherent reaction state.now state.core.receiveNext state.core.window
      state.localReceiveMSS.limit old.2⟩
  exact ackPrepared_of_fields (sequenceAfter state reaction) next coherent rfl
    (AckReaction.receiveSequence_within reaction state.now state.core.receiveNext work.1)
    (AckReaction.receiveSequence_covered reaction state.now state.core.receiveNext state.core.capacity state.core.window
      state.effectiveMSS work.2)

theorem receiveSequence_pending (reaction : AckReaction.State) (time : Nat) (cursor : Seq) :
    (AckReaction.receiveSequence reaction time cursor).work.pending ≠ [] := by
  simp only [AckReaction.receiveSequence, AckReaction.T.issue, Netlib.Theory.TimedReaction.issue]
  exact List.append_ne_nil_of_right_ne_nil reaction.work.pending (List.cons_ne_nil _ _)

theorem receiveSequence_due_le (reaction : AckReaction.State) (time : Nat) (cursor : Seq) :
    ∃ due, (AckReaction.receiveSequence reaction time cursor).due = some due ∧ due ≤ time := by
  have current := Theory.TimedReaction.issue_due reaction.work time
    (AckReaction.demand reaction .sequence cursor 0 0) 0
  change (AckReaction.receiveSequence reaction time cursor).due = _ at current
  cases previous : Theory.TimedReaction.pendingDue reaction.work with
  | none => exact ⟨time, by simpa only [previous, Nat.add_zero] using current, Nat.le_refl _⟩
  | some due => exact ⟨min due time, by simpa only [previous, Nat.add_zero] using current, Nat.min_le_right _ _⟩

theorem sequenceAfter_dispatch (state : State) (reaction : AckReaction.State) :
    ResponseAvailable (sequenceAfter state reaction) true := by
  change (AckReaction.receiveSequence reaction state.now state.core.receiveNext).work.pending ≠ [] ∧ _
  exact ⟨receiveSequence_pending reaction state.now state.core.receiveNext,
    fun _ => receiveSequence_due_le reaction state.now state.core.receiveNext⟩

theorem receive_old_whole_range (state : State) (input : Input) (reaction : AckReaction.State)
    (valid : state.Valid) (coherent : RecoveryCoherent state) (prepared : AckPrepared state)
    (storage : StorageCoherent state) (stored : state.ackReaction = some reaction)
    (tuple : input.packet.header = state.core.inbound) (controls : EstablishedReceive.control input.packet.segment = none)
    (nonempty : input.packet.segment.payload ≠ [])
    (ends : input.packet.segment.sequence.add input.packet.segment.payload.length = state.core.receiveNext)
    (epoch : input.packet.segment.payload.length + offeredWindow state ≤ Seq.modulus) :
    receive state input =
      ⟨sequenceAfter state reaction, .reject (.input .sequence), none, [],
        some (ReceiveReassembly.request state.core (offeredWindow state) .sequence)⟩ ∧
      receiveRuns state input = [] ∧ receivedBytes state input = [] ∧
      AckPrepared (sequenceAfter state reaction) ∧ ResponseAvailable (sequenceAfter state reaction) true := by
  have plan := old_whole_range_sequence state input valid tuple controls nonempty ends epoch
  have raw : receiveRaw state input = receivePlain
      ⟨sequenceAfter state reaction, .reject (.input .sequence), none, [],
        some (ReceiveReassembly.request state.core (offeredWindow state) .sequence)⟩ := by
    simp only [receiveRaw, valid, coherent, prepared.1, storage, not_true_eq_false, ite_false, plan,
      receiveStopped, issueRequest, stored, ReceiveReassembly.request, EstablishedReceive.request]
    rfl
  let effect : ReceiveEffect := receivePlain
    ⟨sequenceAfter state reaction, .reject (.input .sequence), none, [],
      some (ReceiveReassembly.request state.core (offeredWindow state) .sequence)⟩
  have actual : receiveEffect state input = effect := receiveEffect_of_raw_ready state input effect raw valid storage.1
  refine ⟨congrArg ReceiveEffect.result actual, congrArg ReceiveEffect.runs actual, ?_,
    sequenceAfter_prepared state reaction stored prepared, sequenceAfter_dispatch state reaction⟩
  change ReceiveStore.bytes (receiveEffect state input).runs = []
  rw [congrArg ReceiveEffect.runs actual]
  rfl

theorem receive_old_whole_range_emits_ack (state : State) (input : Input) (reaction : AckReaction.State)
    (valid : state.Valid) (coherent : RecoveryCoherent state) (prepared : AckPrepared state)
    (storage : StorageCoherent state) (stored : state.ackReaction = some reaction)
    (tuple : input.packet.header = state.core.inbound) (controls : EstablishedReceive.control input.packet.segment = none)
    (nonempty : input.packet.segment.payload ≠ [])
    (ends : input.packet.segment.sequence.add input.packet.segment.payload.length = state.core.receiveNext)
    (epoch : input.packet.segment.payload.length + offeredWindow state ≤ Seq.modulus) :
    ∃ output, receivedBytes state input = [] ∧
      dispatchAck (receive state input).state true =
        ⟨outputState (sequenceAfter state reaction), .accepted .dispatchAck, some output, [], none⟩ ∧
      output.packet.segment.payload = [] ∧ output.packet.segment.acknowledgment = state.core.receiveNext := by
  obtain ⟨actual, _, bytes, afterPrepared, available⟩ :=
    receive_old_whole_range state input reaction valid coherent prepared storage stored tuple controls nonempty ends epoch
  obtain ⟨output, emitted, encoded⟩ := dispatchAck_success_enabled (sequenceAfter state reaction) valid afterPrepared available
  have fields := emit_transport (sequenceAfter state reaction) [] output encoded
  exact ⟨output, bytes, by simpa only [actual] using emitted,
    emit_payload (sequenceAfter state reaction) [] output encoded, fields.2.2.1⟩

theorem inOrderReceivedWith_storage_empty (state : State) (input : Input) (after : Recovery.State)
    (empty : input.packet.segment.payload = []) (storage : StorageCoherent state) :
    StorageCoherent (inOrderReceivedWith state input after) := by
  unfold inOrderReceivedWith
  apply windowState_storage_coherent
  simpa only [StorageCoherent, State.StorageValid, inOrderCore, EstablishedReceive.commit, empty,
    EstablishedReceive.State.window, List.append_nil] using storage

private theorem recoveryCoherent_of_equal (before after : State) (same : before = after)
    (coherent : RecoveryCoherent after) : RecoveryCoherent before := by
  cases same
  exact coherent

private theorem storageCoherent_of_equal (before after : State) (same : before = after)
    (coherent : StorageCoherent after) : StorageCoherent before := by
  cases same
  exact coherent

theorem receive_empty_full_ack_coherent (state : State) (input : Input) (recovery : Recovery.State) (reaction : AckReaction.State)
    (valid : state.Valid) (coherent : RecoveryCoherent state) (prepared : AckPrepared state)
    (storage : StorageCoherent state) (runtime : state.recovery = some recovery)
    (ackRuntime : state.ackReaction = some reaction) (positive : recovery.Positive)
    (flight : 0 < state.core.sent.length) (emptyHeld : state.receiveStore.held = [])
    (tuple : input.packet.header = state.core.inbound) (controls : EstablishedReceive.control input.packet.segment = none)
    (ack : Flags.ack input.packet.segment.flags = true) (sequence : input.packet.segment.sequence = state.core.receiveNext)
    (empty : input.packet.segment.payload = []) (covers : inOrderCount state input = state.core.sent.length) :
    ∃ acknowledged after,
      Recovery.acknowledge recovery (Recovery.flight recovery) = .ok acknowledged ∧
      after = inOrderReceivedWith state input acknowledged ∧
      receive state input = ⟨after, .accepted (.receive state.core.sent.length 0), none, [], none⟩ ∧
      receiveRuns state input = [] ∧ receivedBytes state input = [] ∧ after.core.sent = [] ∧
      after.core.sendUna = state.core.sendNext ∧ after.Valid ∧ AckPrepared after ∧
      RecoveryCoherent after ∧ StorageCoherent after ∧
      acknowledged.outstanding = [] ∧ acknowledged.deadline = none ∧ acknowledged.timeoutCount = 0 := by
  obtain ⟨acknowledged, after, accepted, afterEq, actual, runs, bytes, retired, advanced, nextValid, nextPrepared,
      cleared, deadline, attempts⟩ := receive_empty_full_ack state input recovery reaction valid coherent prepared storage
    runtime ackRuntime positive flight emptyHeld tuple controls ack sequence empty covers
  have old := coherent
  simp only [RecoveryCoherent, runtime] at old
  have ackValid := Recovery.acknowledge_valid recovery (Recovery.flight recovery) acknowledged old.1 accepted
  have ackMSS := (Recovery.acknowledge_smss recovery (Recovery.flight recovery) acknowledged accepted).trans old.2.1
  have ackFlight : Recovery.flight acknowledged = state.core.sent.length - inOrderCount state input := by
    rw [Recovery.acknowledge_flight recovery (Recovery.flight recovery) acknowledged accepted, Nat.sub_self, covers, Nat.sub_self]
  have recoveryAfter := recoveryCoherent_of_equal after (inOrderReceivedWith state input acknowledged) afterEq
    (inOrderReceivedWith_recovery state input acknowledged ackValid ackMSS ackFlight)
  have storageAfter := storageCoherent_of_equal after (inOrderReceivedWith state input acknowledged) afterEq
    (inOrderReceivedWith_storage_empty state input acknowledged empty storage)
  exact ⟨acknowledged, after, accepted, afterEq, actual, runs, bytes, retired, advanced, nextValid, nextPrepared,
    recoveryAfter, storageAfter, cleared, deadline, attempts⟩

end Netlib.Protocol.TCP.Endpoint
