import Netlib.Check.CampusTCPTwoProgressStart
import Netlib.Protocol.TCP.EndpointFutureReceiveEnabled
import Netlib.Protocol.TCP.EndpointOldSpanEnabled
import Netlib.Protocol.TCP.EndpointClockEnabled

namespace Netlib.Check.CampusTCPTwoProgressReceiver

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart (TwoWriteInitial)

variable {input : Input} {complete : H.Completed input.active input.passive}
  {cut : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}

def source (_initial : TwoWriteInitial cut sender gateway lower upper) : Endpoint.State :=
  endpoint cut.endpoints sender.other

inductive Stage where
  | empty | upperHeld | lowerReleased | allReleased
  deriving DecidableEq

def Stage.bytes (lower upper : List UInt8) : Stage → List UInt8
  | .empty | .upperHeld => []
  | .lowerReleased => lower
  | .allReleased => lower ++ upper

def Stage.allocations : Stage → Nat
  | .empty => 0
  | .upperHeld | .lowerReleased => 1
  | .allReleased => 2

structure PacketFields (initial : TwoWriteInitial cut sender gateway lower upper)
    (offset : Nat) (bytes : List UInt8) (packet : EstablishedReceive.Input) : Prop where
  tuple : packet.packet.header = (source initial).core.inbound
  controls : EstablishedReceive.control packet.packet.segment = none
  ack : Flags.ack packet.packet.segment.flags = true
  sequence : packet.packet.segment.sequence = (source initial).core.receiveNext.add offset
  acknowledgment : packet.packet.segment.acknowledgment = (source initial).core.sendUna
  payload : packet.packet.segment.payload = bytes

inductive Evolution (initial : Endpoint.State) : Endpoint.State → Type where
  | initial : Evolution initial initial
  | clock (prior : Evolution initial before) (frame : Endpoint.ClockFrame before after) : Evolution initial after
  | receive (prior : Evolution initial before) (packet : EstablishedReceive.Input) (result : Endpoint.Result)
      (actual : Endpoint.receive before packet = result) : Evolution initial result.state
  | output (prior : Evolution initial before) (packet : Endpoint.Input)
      (actual : Endpoint.emitAck before true =
        ⟨Endpoint.outputState before, .accepted .emitAck, some packet, [], none⟩) :
      Evolution initial (Endpoint.outputState before)

structure UpperReceipt (initial : TwoWriteInitial cut sender gateway lower upper) where
  before : Endpoint.State
  packet : EstablishedReceive.Input
  recovery : Recovery.State
  reaction : AckReaction.State
  runtime : before.recovery = some recovery
  ackRuntime : before.ackReaction = some reaction
  fields : PacketFields initial lower.length upper packet
  actual : Endpoint.FutureHeld before packet lower.length reaction
  frontier : before.receiveStore.frontier = (source initial).receiveStore.frontier
  nextID : before.receiveStore.nextID = (source initial).receiveStore.nextID

def UpperReceipt.run {initial : TwoWriteInitial cut sender gateway lower upper} (receipt : UpperReceipt initial) : ReceiveReassembly.Run :=
  Endpoint.futureRun receipt.before receipt.packet lower.length

def coreAt (initial : TwoWriteInitial cut sender gateway lower upper) (stage : Stage) : EstablishedReceive.State :=
  { (source initial).core with
    received := stage.bytes lower upper
    receiveNext := (source initial).core.receiveNext.add (stage.bytes lower upper).length }

structure Parameters where
  pending : List UInt8
  pendingLimit : Nat
  effectiveMSS : Nat
  ipSendLimit : Nat
  localReceiveMSS : MSS.Offer

def parameters (state : Endpoint.State) : Parameters :=
  ⟨state.pending, state.pendingLimit, state.effectiveMSS, state.ipSendLimit, state.localReceiveMSS⟩

structure Facts (initial : TwoWriteInitial cut sender gateway lower upper) (state : Endpoint.State) (stage : Stage) where
  recovery : Recovery.State
  reaction : AckReaction.State
  runtime : state.recovery = some recovery
  ackRuntime : state.ackReaction = some reaction
  recoveryState : recovery = { initial.receiverState.idle.recovery with now := recovery.now }
  fixed : parameters state = parameters (source initial)
  core : state.core = coreAt initial stage
  frontier : state.receiveStore.frontier = (source initial).receiveStore.frontier + (stage.bytes lower upper).length
  nextID : state.receiveStore.nextID = (source initial).receiveStore.nextID + stage.allocations
  upperReceipt : Option (UpperReceipt initial)
  held : state.receiveStore.held = if stage = .upperHeld then upperReceipt.toList.map UpperReceipt.run else []
  hasUpper : stage = .upperHeld → upperReceipt.isSome = true
  receiptPast : ∀ receipt, upperReceipt = some receipt → receipt.before.now ≤ state.now
  seenGap : state.receiveStore.seenGap = if upperReceipt.isSome then true else (source initial).receiveStore.seenGap
  space : lower.length + upper.length ≤ (stage.bytes lower upper).length + Endpoint.offeredWindow state
  valid : state.Valid
  coherent : Endpoint.RecoveryCoherent state
  prepared : Endpoint.AckPrepared state
  storage : Endpoint.StorageCoherent state
  monotone : (source initial).now ≤ state.now
  evolution : Evolution (source initial) state

variable {initial : TwoWriteInitial cut sender gateway lower upper} {state after : Endpoint.State} {stage : Stage}

theorem Facts.outstanding (facts : Facts initial state stage) : facts.recovery.outstanding = [] := by
  rw [facts.recoveryState]
  exact initial.receiverState.idle.outstanding

theorem Facts.sentBy (facts : Facts initial state stage) : facts.recovery.SentBy facts.recovery.now := by
  simp only [Recovery.State.SentBy, facts.outstanding, List.not_mem_nil, false_implies, implies_true]

theorem Facts.clocked (facts : Facts initial state stage) : facts.recovery.Clocked := by
  simp only [Recovery.State.Clocked, facts.outstanding, List.not_mem_nil, false_implies, implies_true]

theorem Facts.positive (facts : Facts initial state stage) : facts.recovery.Positive := by
  simp only [Recovery.State.Positive, facts.outstanding, List.not_mem_nil, false_implies, implies_true]

theorem Facts.now (facts : Facts initial state stage) : state.now = facts.recovery.now := by
  simp only [Endpoint.State.now, facts.runtime, Option.map_some, Option.getD_some]

theorem Facts.duplicate (facts : Facts initial state stage) : facts.recovery.duplicateAcks = 0 := by
  rw [facts.recoveryState]
  exact initial.receiverState.idle.duplicate

theorem Facts.sent (facts : Facts initial state stage) : state.core.sent = [] := by
  rw [facts.core]
  exact initial.receiverState.idle.sent

theorem Facts.receiveNext (facts : Facts initial state stage) :
    state.core.receiveNext = (source initial).core.receiveNext.add (stage.bytes lower upper).length := by rw [facts.core]; rfl

theorem Facts.received (facts : Facts initial state stage) : state.core.received = stage.bytes lower upper := by rw [facts.core]; rfl

theorem Facts.inbound (facts : Facts initial state stage) : state.core.inbound = (source initial).core.inbound := by rw [facts.core]; rfl

theorem Facts.sendUna (facts : Facts initial state stage) : state.core.sendUna = (source initial).core.sendUna := by rw [facts.core]; rfl

theorem Facts.sendNext (facts : Facts initial state stage) : state.core.sendNext = (source initial).core.sendNext := by rw [facts.core]; rfl

theorem Facts.capacity (facts : Facts initial state stage) : state.core.capacity = (source initial).core.capacity := by rw [facts.core]; rfl

theorem Facts.pending (facts : Facts initial state stage) : state.pending = (source initial).pending :=
  congrArg Parameters.pending facts.fixed

theorem Facts.pendingLimit (facts : Facts initial state stage) : state.pendingLimit = (source initial).pendingLimit :=
  congrArg Parameters.pendingLimit facts.fixed

theorem Facts.effectiveMSS (facts : Facts initial state stage) : state.effectiveMSS = (source initial).effectiveMSS :=
  congrArg Parameters.effectiveMSS facts.fixed

theorem Facts.ipSendLimit (facts : Facts initial state stage) : state.ipSendLimit = (source initial).ipSendLimit :=
  congrArg Parameters.ipSendLimit facts.fixed

theorem Facts.localReceiveMSS (facts : Facts initial state stage) : state.localReceiveMSS = (source initial).localReceiveMSS :=
  congrArg Parameters.localReceiveMSS facts.fixed

theorem Facts.empty_held (facts : Facts initial state stage) (notHeld : stage ≠ .upperHeld) :
    state.receiveStore.held = [] := by simp only [facts.held, ite_eq_right notHeld]

theorem Facts.old_ack (facts : Facts initial state stage) (fields : PacketFields initial offset bytes packet) :
    Seq.distance packet.packet.segment.acknowledgment state.core.sendUna ≤ EstablishedReceive.maxSendWindow := by
  rw [fields.acknowledgment, facts.sendUna, Seq.distance_self]
  exact Nat.zero_le _

def initial_facts (initial : TwoWriteInitial cut sender gateway lower upper) : Facts initial (source initial) .empty where
  recovery := initial.receiverState.idle.recovery
  reaction := initial.receiverState.idle.reaction
  runtime := initial.receiverState.idle.runtime
  ackRuntime := initial.receiverState.idle.ackRuntime
  recoveryState := rfl
  fixed := rfl
  core := by
    simp only [coreAt, Stage.bytes, List.length_nil, Seq.add_zero]
    have empty : (source initial).core.received = [] := initial.receiverState.unread
    rw [← empty]
  frontier := by simp only [Stage.bytes, List.length_nil, Nat.add_zero]
  nextID := by simp only [Stage.allocations, Nat.add_zero]
  upperReceipt := none
  held := initial.receiverState.held
  hasUpper := by intro impossible; cases impossible
  receiptPast := by intro receipt impossible; cases impossible
  seenGap := rfl
  space := by simpa only [source, Stage.bytes, List.length_nil, List.length_append, Nat.zero_add] using initial.receiverState.space
  valid := initial.receiverState.idle.valid
  coherent := initial.receiverState.idle.coherent
  prepared := initial.receiverState.idle.prepared
  storage := initial.receiverState.idle.storage
  monotone := Nat.le_refl _
  evolution := .initial

def Facts.clock (facts : Facts initial state stage) (frame : Endpoint.ClockFrame state after)
    (timely : Endpoint.AckTimeReady state after.now) : Facts initial after stage := by
  refine { facts with
    recovery := { facts.recovery with now := after.now }
    runtime := frame.runtime facts.runtime, ackRuntime := frame.ackReaction.trans facts.ackRuntime
    recoveryState := ?_, fixed := ?_, core := frame.core.trans facts.core
    frontier := ?_, nextID := ?_, held := ?_, receiptPast := ?_, seenGap := ?_, space := ?_
    valid := frame.valid facts.valid, coherent := frame.recovery_coherent facts.coherent
    prepared := frame.ack_prepared facts.prepared timely, storage := frame.storage_coherent facts.storage
    monotone := Nat.le_trans facts.monotone frame.monotone, evolution := .clock facts.evolution frame }
  · rw [facts.recoveryState]
  · simp only [parameters, frame.pending, frame.pendingLimit, frame.effectiveMSS, frame.ipSendLimit,
      frame.localReceiveMSS]
    exact facts.fixed
  · rw [frame.receiveStore]; exact facts.frontier
  · rw [frame.receiveStore]; exact facts.nextID
  · rw [frame.receiveStore]; exact facts.held
  · intro receipt recorded; exact Nat.le_trans (facts.receiptPast receipt recorded) frame.monotone
  · rw [frame.receiveStore]; exact facts.seenGap
  · simpa only [Endpoint.offeredWindow, frame.ackReaction, frame.core] using facts.space

private theorem output_space (facts : Facts initial state stage) :
    Endpoint.offeredWindow state ≤ Endpoint.offeredWindow (Endpoint.outputState state) := by
  have valid : facts.reaction.advertisement.Valid state.core.window := by
    have coherent : state.recovery.isSome = true ∧ facts.reaction.Coherent state.core.receiveNext
        state.core.window state.localReceiveMSS.limit := by
      simpa only [Endpoint.AckCoherent, facts.ackRuntime] using facts.prepared.1
    exact coherent.2.1
  have grows := (ReceiveAdvertisement.candidate_bounds facts.reaction.advertisement state.core.capacity
    state.core.window state.effectiveMSS valid).1
  simpa only [Endpoint.offeredWindow, Endpoint.outputState, facts.ackRuntime, Option.map_some,
    AckReaction.outputState, AckReaction.State.window, ReceiveAdvertisement.commit_window] using grows

def Facts.output (facts : Facts initial state stage) (packet : Endpoint.Input)
    (actual : Endpoint.emitAck state true =
      ⟨Endpoint.outputState state, .accepted .emitAck, some packet, [], none⟩) :
    Facts initial (Endpoint.outputState state) stage := by
  refine { facts with
    reaction := AckReaction.outputState facts.reaction state.now state.core.receiveNext
      state.core.capacity state.core.window state.effectiveMSS
    ackRuntime := ?_, space := ?_
    prepared := Endpoint.outputState_ackPrepared state facts.prepared
    storage := Endpoint.outputState_storage_coherent state facts.prepared facts.storage
    evolution := .output facts.evolution packet actual }
  · simp only [Endpoint.outputState, facts.ackRuntime, Option.map_some]
  · exact Nat.le_trans facts.space (Nat.add_le_add_left (output_space facts) _)

theorem Facts.emit_ack (facts : Facts initial state stage) (pending : facts.reaction.work.pending ≠ []) :
    ∃ packet, Endpoint.emitAck state true =
      ⟨Endpoint.outputState state, .accepted .emitAck, some packet, [], none⟩ ∧
      Endpoint.emit state [] = .ok packet ∧ packet.packet.segment.payload = [] ∧
      packet.packet.header = Output.reverse (source initial).core.inbound ∧
      packet.packet.segment.sequence = (source initial).core.sendNext ∧
      packet.packet.segment.acknowledgment = (source initial).core.receiveNext.add (stage.bytes lower upper).length ∧
      packet.packet.segment.window.val = Endpoint.outputWindow state ∧
      Nonempty (Facts initial (Endpoint.outputState state) stage) := by
  have available := Endpoint.responseAvailable_of_pending state facts.reaction facts.ackRuntime pending
  obtain ⟨packet, actual, encoded⟩ := Endpoint.emitAck_success_enabled state facts.valid facts.prepared available
  have fields := Endpoint.emit_transport state [] packet encoded
  exact ⟨packet, actual, encoded, Endpoint.emit_payload state [] packet encoded,
    fields.1.trans (congrArg Output.reverse facts.inbound), fields.2.1.trans facts.sendNext,
    fields.2.2.1.trans facts.receiveNext, fields.2.2.2.1, ⟨facts.output packet actual⟩⟩

theorem Facts.future_conditions (facts : Facts initial state .empty)
    (fields : PacketFields initial lower.length upper packet) :
    Endpoint.FutureReceiveConditions state packet lower.length facts.recovery facts.reaction := by
  refine ⟨facts.valid, facts.coherent, facts.prepared, facts.storage, facts.runtime, facts.ackRuntime,
    facts.outstanding, facts.empty_held (by decide), ?_, ?_, fields.controls, fields.ack, ?_, ?_, ?_, facts.old_ack fields⟩
  · rw [fields.payload]; exact initial.upperNonempty
  · rw [facts.inbound]; exact fields.tuple
  · simpa only [facts.receiveNext, Stage.bytes, List.length_nil, Seq.add_zero] using fields.sequence
  · exact List.length_pos_iff.mpr initial.lowerNonempty
  · simpa only [fields.payload, Stage.bytes, List.length_nil, Nat.zero_add] using facts.space

def Facts.future_held (facts : Facts initial state .empty)
    (fields : PacketFields initial lower.length upper packet)
    (held : Endpoint.FutureHeld state packet lower.length facts.reaction) :
    Facts initial (Endpoint.futureAfter state packet lower.length facts.reaction) .upperHeld := by
  let receipt : UpperReceipt initial := ⟨state, packet, facts.recovery, facts.reaction, facts.runtime, facts.ackRuntime, fields, held,
    by simpa only [Stage.bytes, List.length_nil, Nat.add_zero] using facts.frontier,
    by simpa only [Stage.allocations, Nat.add_zero] using facts.nextID⟩
  have sameNow : (Endpoint.futureAfter state packet lower.length facts.reaction).now = state.now := rfl
  refine {
    recovery := facts.recovery, reaction := Endpoint.futureReaction state packet facts.reaction
    runtime := facts.runtime, ackRuntime := rfl, recoveryState := facts.recoveryState
    fixed := facts.fixed, core := facts.core, frontier := ?_, nextID := ?_
    upperReceipt := some receipt, held := rfl, hasUpper := fun _ => rfl
    receiptPast := ?_, seenGap := rfl, space := ?_
    valid := held.valid, coherent := held.coherent, prepared := held.prepared, storage := held.storage
    monotone := facts.monotone, evolution := .receive facts.evolution packet _ held.receive }
  · simpa only [Endpoint.futureAfter, Endpoint.storedState, Endpoint.futureStore, Stage.bytes, List.length_nil,
      Nat.add_zero] using facts.frontier
  · simp only [Endpoint.futureAfter, Endpoint.storedState, Endpoint.futureStore, facts.nextID,
      Stage.allocations, Nat.add_zero]
  · intro selected selectedEq
    have same : receipt = selected := Option.some.inj selectedEq
    cases same
    exact Nat.le_refl _
  · simpa only [Endpoint.offeredWindow, Endpoint.futureAfter, Endpoint.storedState, Endpoint.futureReaction,
      AckReaction.receiveRelease, AckReaction.State.window, ReceiveAdvertisement.consume, Nat.add_zero,
      facts.ackRuntime, Stage.bytes, List.length_nil] using facts.space

theorem Facts.future_enabled (facts : Facts initial state .empty)
    (fields : PacketFields initial lower.length upper packet) :
    Endpoint.FutureHeld state packet lower.length facts.reaction ∧
      Nonempty (Facts initial (Endpoint.futureAfter state packet lower.length facts.reaction) .upperHeld) := by
  have held := Endpoint.receive_future_enabled (facts.future_conditions fields)
  exact ⟨held, ⟨facts.future_held fields held⟩⟩

private theorem release_window (reaction : AckReaction.State) (time : Nat) (cursor : Seq)
    (novel released : Nat) (immediate : Bool) :
    (AckReaction.receiveRelease reaction time cursor novel released immediate).window = reaction.window - released :=
  ReceiveAdvertisement.consume_window reaction.advertisement released

private theorem offered_runtime (state : Endpoint.State) (reaction : AckReaction.State)
    (runtime : state.ackReaction = some reaction) : Endpoint.offeredWindow state = reaction.window := by
  rw [Endpoint.offeredWindow, runtime]

private theorem in_order_window (state : Endpoint.State) (packet : EstablishedReceive.Input)
    (recovery : Recovery.State) (reaction : AckReaction.State) (runtime : state.ackReaction = some reaction) :
    Endpoint.offeredWindow (Endpoint.inOrderAfterWith state packet recovery reaction) =
      Endpoint.offeredWindow state - packet.packet.segment.payload.length := by
  let next := AckReaction.receiveRelease reaction state.now
    (state.core.receiveNext.add packet.packet.segment.payload.length)
    packet.packet.segment.payload.length packet.packet.segment.payload.length false
  let received : Endpoint.State := { state with
    core := Endpoint.inOrderCore state packet
    recovery := some { recovery with duplicateAcks := 0 }
    lastAckWindow := some packet.packet.segment.window.val
    receiveStore := (Endpoint.inOrderStore state packet).state
    ackReaction := some next }
  have afterAck : (Endpoint.inOrderAfterWith state packet recovery reaction).ackReaction = some next :=
    Endpoint.windowState_ackReaction state received packet.packet.segment
  exact (offered_runtime _ next afterAck).trans
    ((release_window reaction state.now (state.core.receiveNext.add packet.packet.segment.payload.length)
      packet.packet.segment.payload.length packet.packet.segment.payload.length false).trans
        (congrArg (fun n => n - packet.packet.segment.payload.length) (offered_runtime state reaction runtime).symm))

private theorem subtract_space (total front window size next : Nat)
    (bound : total ≤ front + window) (room : size ≤ window) (length : front + size = next) :
    total ≤ next + (window - size) := by omega

private structure ReceiveFrame (initial : TwoWriteInitial cut sender gateway lower upper) (state : Endpoint.State)
    (stage : Stage) (recovery : Recovery.State) (reaction : AckReaction.State)
    (upperReceipt : Option (UpperReceipt initial)) : Prop where
  runtime : state.recovery = some recovery
  ackRuntime : state.ackReaction = some reaction
  fixed : parameters state = parameters (source initial)
  core : state.core = coreAt initial stage
  frontier : state.receiveStore.frontier = (source initial).receiveStore.frontier + (stage.bytes lower upper).length
  nextID : state.receiveStore.nextID = (source initial).receiveStore.nextID + stage.allocations
  held : state.receiveStore.held = if stage = .upperHeld then upperReceipt.toList.map UpperReceipt.run else []
  seenGap : state.receiveStore.seenGap = if upperReceipt.isSome then true else (source initial).receiveStore.seenGap
  space : lower.length + upper.length ≤ (stage.bytes lower upper).length + Endpoint.offeredWindow state

private theorem in_order_frame {next : Stage} (facts : Facts initial state stage)
    (fields : PacketFields initial (stage.bytes lower upper).length bytes packet)
    (nextNotHeld : next ≠ .upperHeld)
    (appended : stage.bytes lower upper ++ bytes = next.bytes lower upper)
    (allocations : stage.allocations + 1 = next.allocations)
    (fits : bytes.length ≤ Endpoint.offeredWindow state)
    (afterEq : after = Endpoint.inOrderAfterWith state packet facts.recovery facts.reaction) :
    ReceiveFrame initial after next facts.recovery
      (AckReaction.receiveRelease facts.reaction state.now (state.core.receiveNext.add bytes.length)
        bytes.length bytes.length false) facts.upperReceipt := by
  have zero : Endpoint.inOrderCount state packet = 0 := by
    simp only [Endpoint.inOrderCount, fields.acknowledgment, facts.sendUna, Seq.distance_self]
  have duplicate : { facts.recovery with duplicateAcks := 0 } = facts.recovery := by
    exact congrArg (fun n => { facts.recovery with duplicateAcks := n }) facts.duplicate.symm
  have runtime : after.recovery = some facts.recovery := by
    rw [afterEq]
    simp only [Endpoint.inOrderAfterWith, Endpoint.windowState_recovery, duplicate]
  have sameNow : after.now = state.now := by
    simp only [Endpoint.State.now, runtime, facts.runtime]
  have length := congrArg List.length appended
  simp only [List.length_append] at length
  refine {
    runtime
    ackRuntime := ?_
    fixed := ?_
    core := ?_
    frontier := ?_
    nextID := ?_
    held := ?_
    seenGap := ?_
    space := ?_ }
  · rw [afterEq]
    simp only [Endpoint.inOrderAfterWith, Endpoint.windowState_ackReaction, fields.payload]
  · rw [afterEq]
    unfold Endpoint.inOrderAfterWith Endpoint.windowState
    split <;> exact facts.fixed
  · rw [afterEq]
    simp only [Endpoint.inOrderAfterWith, Endpoint.windowState_core, Endpoint.inOrderCore,
      EstablishedReceive.commit, zero, fields.payload, facts.core, coreAt, List.drop_zero, Seq.add_zero,
      Seq.add_add, appended, length]
  · rw [afterEq]
    simp only [Endpoint.inOrderAfterWith, Endpoint.windowState_receiveStore, Endpoint.inOrderStore,
      facts.frontier, fields.payload, Nat.add_assoc, length]
  · rw [afterEq]
    simp only [Endpoint.inOrderAfterWith, Endpoint.windowState_receiveStore, Endpoint.inOrderStore, facts.nextID, Nat.add_assoc, allocations]
  · rw [afterEq]
    simp only [Endpoint.inOrderAfterWith, Endpoint.windowState_receiveStore, Endpoint.inOrderStore,
      ite_eq_right nextNotHeld]
  · rw [afterEq]
    simpa only [Endpoint.inOrderAfterWith, Endpoint.windowState_receiveStore, Endpoint.inOrderStore] using facts.seenGap
  · have window : Endpoint.offeredWindow after = Endpoint.offeredWindow state - bytes.length := by
      rw [afterEq, in_order_window state packet facts.recovery facts.reaction facts.ackRuntime, fields.payload]
    rw [window]
    have bound := facts.space
    exact subtract_space (lower.length + upper.length) (stage.bytes lower upper).length
      (Endpoint.offeredWindow state) bytes.length (next.bytes lower upper).length bound fits length


def Facts.in_order_received {next : Stage} (facts : Facts initial state stage)
    (fields : PacketFields initial (stage.bytes lower upper).length bytes packet)
    (_notHeld : stage ≠ .upperHeld) (nextNotHeld : next ≠ .upperHeld) (_nonempty : bytes ≠ [])
    (appended : stage.bytes lower upper ++ bytes = next.bytes lower upper)
    (allocations : stage.allocations + 1 = next.allocations)
    (fits : bytes.length ≤ Endpoint.offeredWindow state)
    (afterEq : after = Endpoint.inOrderAfterWith state packet facts.recovery facts.reaction)
    (actual : Endpoint.receive state packet =
      ⟨after, .accepted (.receive 0 bytes.length), none, [],
        some (ReceiveReassembly.request after.core (Endpoint.offeredWindow after) .data)⟩)
    (valid : after.Valid) (coherent : Endpoint.RecoveryCoherent after)
    (prepared : Endpoint.AckPrepared after) (storage : Endpoint.StorageCoherent after) :
    Facts initial after next := by
  have frame := in_order_frame facts fields nextNotHeld appended allocations fits afterEq
  have sameNow : after.now = state.now := by
    simp only [Endpoint.State.now, frame.runtime, facts.runtime]
  exact {
    recovery := facts.recovery
    reaction := AckReaction.receiveRelease facts.reaction state.now (state.core.receiveNext.add bytes.length)
      bytes.length bytes.length false
    runtime := frame.runtime, ackRuntime := frame.ackRuntime, recoveryState := facts.recoveryState
    fixed := frame.fixed, core := frame.core, frontier := frame.frontier, nextID := frame.nextID
    upperReceipt := facts.upperReceipt, held := frame.held
    hasUpper := fun impossible => False.elim (nextNotHeld impossible)
    receiptPast := fun receipt recorded => sameNow.symm ▸ facts.receiptPast receipt recorded
    seenGap := frame.seenGap, space := frame.space, valid, coherent, prepared, storage
    monotone := sameNow.symm ▸ facts.monotone
    evolution := .receive facts.evolution packet _ actual }

theorem Facts.in_order_enabled {next : Stage} (facts : Facts initial state stage)
    (fields : PacketFields initial (stage.bytes lower upper).length bytes packet)
    (notHeld : stage ≠ .upperHeld) (nextNotHeld : next ≠ .upperHeld) (nonempty : bytes ≠ [])
    (appended : stage.bytes lower upper ++ bytes = next.bytes lower upper)
    (allocations : stage.allocations + 1 = next.allocations) :
    ∃ after, Endpoint.receive state packet =
        ⟨after, .accepted (.receive 0 bytes.length), none, [],
          some (ReceiveReassembly.request after.core (Endpoint.offeredWindow after) .data)⟩ ∧
      Endpoint.receiveRuns state packet = [Endpoint.inOrderRun state packet] ∧
      Endpoint.receivedBytes state packet = bytes ∧ Nonempty (Facts initial after next) ∧
      Endpoint.ResponseAvailable after false := by
  have zero : Endpoint.inOrderCount state packet = 0 := by
    simp only [Endpoint.inOrderCount, fields.acknowledgment, facts.sendUna, Seq.distance_self]
  have fits : packet.packet.segment.payload.length ≤ Endpoint.offeredWindow state := by
    rw [fields.payload]
    have bound := facts.space
    have length := congrArg List.length appended
    have nextBound : (next.bytes lower upper).length ≤ lower.length + upper.length := by
      cases next <;> simp only [Stage.bytes, List.length_nil, List.length_append] <;> omega
    simp only [List.length_append] at length
    omega
  have unchanged : Recovery.acknowledgeAt facts.recovery (Endpoint.inOrderCount state packet) state.now = .ok facts.recovery := by
    rw [zero, facts.now]
    exact Recovery.acknowledgeAt_zero_of_past _ _ (Nat.le_refl _)
  obtain ⟨acknowledged, after, computed, afterEq, actual, runs, released, valid, coherent, prepared, storage⟩ :=
    Endpoint.receive_inOrder_prepared state packet facts.recovery facts.reaction facts.valid facts.coherent facts.prepared
      facts.storage facts.runtime facts.ackRuntime facts.sentBy (facts.empty_held notHeld)
      (fields.tuple.trans facts.inbound.symm) fields.controls fields.ack (fields.sequence.trans facts.receiveNext.symm)
      (by rw [fields.payload]; exact nonempty) fits (by rw [zero]; exact Nat.zero_le _)
  have same : acknowledged = facts.recovery := Except.ok.inj (computed.symm.trans unchanged)
  subst acknowledged
  have accepted : Endpoint.receive state packet =
      ⟨after, .accepted (.receive 0 bytes.length), none, [],
        some (ReceiveReassembly.request after.core (Endpoint.offeredWindow after) .data)⟩ :=
    by simpa only [zero, fields.payload] using actual
  exact ⟨after, accepted, runs, by simpa only [fields.payload] using released,
    ⟨facts.in_order_received fields notHeld nextNotHeld nonempty appended allocations
      (by simpa only [fields.payload] using fits) afterEq accepted valid coherent prepared storage⟩,
    by rw [afterEq]; exact Endpoint.inOrderAfterWith_response _ _ _ _⟩

theorem Facts.lower_enabled (facts : Facts initial state .empty)
    (fields : PacketFields initial 0 lower packet) :
    ∃ after, Endpoint.receive state packet =
        ⟨after, .accepted (.receive 0 lower.length), none, [],
          some (ReceiveReassembly.request after.core (Endpoint.offeredWindow after) .data)⟩ ∧
      Endpoint.receiveRuns state packet = [Endpoint.inOrderRun state packet] ∧
      Endpoint.receivedBytes state packet = lower ∧ Nonempty (Facts initial after .lowerReleased) ∧
      Endpoint.ResponseAvailable after false :=
  facts.in_order_enabled fields (by decide) (by decide) initial.lowerNonempty (List.nil_append _) rfl

theorem Facts.upper_enabled (facts : Facts initial state .lowerReleased)
    (fields : PacketFields initial lower.length upper packet) :
    ∃ after, Endpoint.receive state packet =
        ⟨after, .accepted (.receive 0 upper.length), none, [],
          some (ReceiveReassembly.request after.core (Endpoint.offeredWindow after) .data)⟩ ∧
      Endpoint.receiveRuns state packet = [Endpoint.inOrderRun state packet] ∧
      Endpoint.receivedBytes state packet = upper ∧ Nonempty (Facts initial after .allReleased) ∧
      Endpoint.ResponseAvailable after false :=
  facts.in_order_enabled fields (by decide) (by decide) initial.upperNonempty rfl rfl

theorem UpperReceipt.run_fields (receipt : UpperReceipt initial) :
    receipt.run.position = (source initial).receiveStore.frontier + lower.length ∧
      receipt.run.bytes = upper ∧ receipt.run.receipt = (source initial).receiveStore.nextID ∧
      receipt.run.metadata = ⟨receipt.packet.packet.segment, receipt.packet.packet.header, receipt.before.now⟩ := by
  exact ⟨congrArg (fun n => n + lower.length) receipt.frontier, receipt.fields.payload, receipt.nextID, rfl⟩

theorem Facts.upper_receipt (facts : Facts initial state .upperHeld) :
    ∃ receipt, facts.upperReceipt = some receipt ∧ state.receiveStore.held = [receipt.run] := by
  have present := facts.hasUpper rfl
  cases recorded : facts.upperReceipt with
  | none => simp only [recorded, Option.isSome_none, Bool.false_eq_true] at present
  | some receipt =>
    refine ⟨receipt, rfl, ?_⟩
    simp only [facts.held, recorded, ite_true, Option.toList_some, List.map_cons, List.map_nil]

theorem Facts.gap_conditions (facts : Facts initial state .upperHeld) (receipt : UpperReceipt initial)
    (recorded : facts.upperReceipt = some receipt) (fields : PacketFields initial 0 lower packet) :
    Endpoint.GapReceiveConditions state packet receipt.run facts.recovery facts.reaction := by
  have run := receipt.run_fields
  refine ⟨facts.valid, facts.coherent, facts.prepared, facts.storage, facts.runtime, facts.ackRuntime,
    facts.outstanding, ?_, ?_, ?_, fields.tuple.trans facts.inbound.symm, fields.controls, fields.ack,
    ?_, facts.old_ack fields, ?_, ?_, ?_, ?_, ?_, ?_, facts.receiptPast receipt recorded⟩
  · simp only [facts.held, recorded, ite_true, Option.toList_some, List.map_cons, List.map_nil]
  · simpa only [facts.frontier, Stage.bytes, List.length_nil, Nat.add_zero, fields.payload] using run.1
  · rw [fields.payload]; exact initial.lowerNonempty
  · simpa only [facts.receiveNext, Stage.bytes, List.length_nil] using fields.sequence
  · exact receipt.fields.payload.trans run.2.1.symm
  · exact receipt.fields.tuple.trans facts.inbound.symm
  · exact receipt.fields.controls
  · exact receipt.fields.ack
  · change receipt.packet.packet.segment.sequence = _
    simpa only [facts.receiveNext, Stage.bytes, List.length_nil, Seq.add_zero, fields.payload] using receipt.fields.sequence
  · rw [show receipt.run.metadata.segment.acknowledgment = (source initial).core.sendUna from receipt.fields.acknowledgment,
      facts.sendUna, Seq.distance_self]
    exact Nat.zero_le _

def Facts.gap_filled (facts : Facts initial state .upperHeld) (receipt : UpperReceipt initial)
    (_recorded : facts.upperReceipt = some receipt) (fields : PacketFields initial 0 lower packet)
    (filled : Endpoint.GapFilled state packet receipt.run facts.recovery facts.reaction) :
    Facts initial (Endpoint.gapAfter state packet receipt.run facts.recovery facts.reaction) .allReleased := by
  generalize afterEq : Endpoint.gapAfter state packet receipt.run facts.recovery facts.reaction = after
  have duplicate : { facts.recovery with duplicateAcks := 0 } = facts.recovery :=
    congrArg (fun n => { facts.recovery with duplicateAcks := n }) facts.duplicate.symm
  have runtime : after.recovery = some facts.recovery := by
    rw [← afterEq, Endpoint.gapAfter_recovery, duplicate]
  have sameNow : after.now = state.now := by simp only [Endpoint.State.now, runtime, facts.runtime]
  have actual := filled.receive
  rw [afterEq] at actual
  refine {
    recovery := facts.recovery, reaction := Endpoint.gapReaction state packet receipt.run facts.reaction
    runtime, ackRuntime := ?_, recoveryState := facts.recoveryState, fixed := ?_, core := ?_
    frontier := ?_, nextID := ?_, upperReceipt := facts.upperReceipt, held := ?_
    hasUpper := by intro impossible; cases impossible
    receiptPast := ?_, seenGap := ?_, space := ?_
    valid := by rw [← afterEq]; exact filled.valid
    coherent := by rw [← afterEq]; exact filled.coherent
    prepared := by rw [← afterEq]; exact filled.prepared
    storage := by rw [← afterEq]; exact filled.storage
    monotone := by rw [sameNow]; exact facts.monotone
    evolution := .receive facts.evolution packet _ actual }
  · rw [← afterEq, Endpoint.gapAfter_ackReaction]
  · rw [← afterEq]
    unfold parameters Endpoint.gapAfter Endpoint.storedState Endpoint.gapReceived Endpoint.zeroRunState
    exact facts.fixed
  · rw [← afterEq, Endpoint.gapAfter_core]
    simp only [EstablishedReceive.commit, facts.core, coreAt, Stage.bytes, fields.payload, receipt.run_fields.2.1,
      List.length_nil, List.nil_append, Seq.add_zero, List.drop_zero]
  · rw [← afterEq, Endpoint.gapAfter_receiveStore]
    simp only [Endpoint.gapStore, facts.frontier, Stage.bytes, List.length_nil, Nat.add_zero, fields.payload,
      receipt.run_fields.2.1, List.length_append, Nat.add_assoc]
  · rw [← afterEq, Endpoint.gapAfter_receiveStore]
    simp only [Endpoint.gapStore, facts.nextID, Stage.allocations, Nat.add_assoc]
  · rw [← afterEq, Endpoint.gapAfter_receiveStore]
    rfl
  · intro selected selectedEq
    rw [sameNow]
    exact facts.receiptPast selected selectedEq
  · rw [← afterEq, Endpoint.gapAfter_receiveStore]
    exact facts.seenGap
  · simp only [Stage.bytes, List.length_append]
    exact Nat.le_add_right _ _

theorem Facts.gap_enabled (facts : Facts initial state .upperHeld) (fields : PacketFields initial 0 lower packet) :
    ∃ receipt, facts.upperReceipt = some receipt ∧
      Endpoint.GapFilled state packet receipt.run facts.recovery facts.reaction ∧
      Nonempty (Facts initial (Endpoint.gapAfter state packet receipt.run facts.recovery facts.reaction) .allReleased) := by
  obtain ⟨receipt, recorded, _⟩ := facts.upper_receipt
  have filled := Endpoint.receive_gap_enabled (facts.gap_conditions receipt recorded fields)
  exact ⟨receipt, recorded, filled, ⟨facts.gap_filled receipt recorded fields filled⟩⟩

private theorem span_epoch (consumed size window capacity : Nat)
    (inside : consumed ≤ size) (room : window ≤ capacity - size) (fits : size ≤ capacity) (bounded : capacity ≤ 65535) :
    consumed + window ≤ Seq.modulus := by
  unfold Seq.modulus
  omega

theorem Facts.old_span (facts : Facts initial state stage) (fields : PacketFields initial offset bytes packet)
    (_nonempty : bytes ≠ []) (old : offset + bytes.length ≤ (stage.bytes lower upper).length) :
    bytes.length ≤ (stage.bytes lower upper).length - offset ∧
      packet.packet.segment.sequence.add ((stage.bytes lower upper).length - offset) = state.core.receiveNext ∧
      (stage.bytes lower upper).length - offset + Endpoint.offeredWindow state ≤ Seq.modulus := by
  have offsetBound : offset ≤ (stage.bytes lower upper).length := by omega
  refine ⟨by omega, ?_, ?_⟩
  · rw [fields.sequence, Seq.add_add, Nat.add_sub_cancel' offsetBound, facts.receiveNext]
  · have room := Endpoint.offeredWindow_le state facts.prepared.1
    rw [EstablishedReceive.State.window, facts.received] at room
    exact span_epoch _ _ _ _ (Nat.sub_le _ _) room
      (by simpa only [facts.received] using facts.valid.1.2.1) facts.valid.1.2.2.1

def Facts.old_received (facts : Facts initial state stage) (packet : EstablishedReceive.Input)
    (actual : Endpoint.receive state packet =
      ⟨Endpoint.sequenceAfter state facts.reaction, .reject (.input .sequence), none, [],
        some (ReceiveReassembly.request state.core (Endpoint.offeredWindow state) .sequence)⟩) :
    Facts initial (Endpoint.sequenceAfter state facts.reaction) stage := by
  refine { facts with
    reaction := AckReaction.receiveSequence facts.reaction state.now state.core.receiveNext
    ackRuntime := rfl
    space := ?_
    prepared := Endpoint.sequenceAfter_prepared state facts.reaction facts.ackRuntime facts.prepared
    storage := ?_
    evolution := .receive facts.evolution packet _ actual }
  · simpa only [Endpoint.offeredWindow, Endpoint.sequenceAfter, facts.ackRuntime,
      AckReaction.receiveSequence, AckReaction.State.window] using facts.space
  · simpa only [Endpoint.StorageCoherent, Endpoint.State.StorageValid, Endpoint.sequenceAfter,
      facts.ackRuntime, AckReaction.receiveSequence, AckReaction.State.window] using facts.storage

theorem Facts.old_enabled (facts : Facts initial state stage) (fields : PacketFields initial offset bytes packet)
    (nonempty : bytes ≠ []) (old : offset + bytes.length ≤ (stage.bytes lower upper).length) :
    Endpoint.receive state packet =
        ⟨Endpoint.sequenceAfter state facts.reaction, .reject (.input .sequence), none, [],
          some (ReceiveReassembly.request state.core (Endpoint.offeredWindow state) .sequence)⟩ ∧
      Endpoint.receiveRuns state packet = [] ∧ Endpoint.receivedBytes state packet = [] ∧
      Nonempty (Facts initial (Endpoint.sequenceAfter state facts.reaction) stage) ∧
      Endpoint.ResponseAvailable (Endpoint.sequenceAfter state facts.reaction) true := by
  obtain ⟨inside, cursor, epoch⟩ := facts.old_span fields nonempty old
  obtain ⟨actual, runs, released, _, available⟩ := Endpoint.receive_old_span state packet facts.reaction
    ((stage.bytes lower upper).length - offset) facts.valid facts.coherent facts.prepared facts.storage facts.ackRuntime
    (fields.tuple.trans facts.inbound.symm) fields.controls (by rw [fields.payload]; exact nonempty)
    (by rw [fields.payload]; exact inside) cursor epoch
  exact ⟨actual, runs, released, ⟨facts.old_received packet actual⟩, available⟩

end Netlib.Check.CampusTCPTwoProgressReceiver
