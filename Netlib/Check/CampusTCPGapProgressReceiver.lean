import Netlib.Check.CampusTCPGapProgressStart
import Netlib.Check.CampusTCPGapOldData
import Netlib.Protocol.TCP.EndpointGapReceiveEnabled
import Netlib.Protocol.TCP.EndpointClockEnabled

/-!
# Current receiver state around an actual held gap

The queued upper receipt keeps its original metadata.
The first gap fill retains both header effects through later clocks and ACK output.
-/

namespace Netlib.Check.CampusTCPGapProgressReceiver

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPGapProgressStart (GapInitial)

variable {input : Input} {complete : H.Completed input.active input.passive}
  {cut : Cut input complete} {sender : Actor} {lower upper : List UInt8}

def source (_initial : GapInitial cut sender lower upper) : Endpoint.State := endpoint cut.endpoints sender.other

def withoutRuntime (state : Endpoint.State) : Endpoint.State := { state with recovery := none, ackReaction := none }

structure Geometry (initial : GapInitial cut sender lower upper) : Prop where
  lowerSequence : initial.lowerSource.attempt.output.packet.segment.sequence = (source initial).core.receiveNext
  upperSource : initial.receiver.source.delivery.source.step = initial.upperSource.attempt.step
  upperTuple : initial.receiver.run.metadata.header = (source initial).core.inbound
  upperControl : EstablishedReceive.control initial.receiver.run.metadata.segment = none
  upperAck : Flags.ack initial.receiver.run.metadata.segment.flags = true
  upperSequence : initial.receiver.run.metadata.segment.sequence = (source initial).core.receiveNext.add lower.length
  upperAckOld : Seq.distance initial.receiver.run.metadata.segment.acknowledgment (source initial).core.sendUna ≤
    EstablishedReceive.maxSendWindow
  upperPast : initial.receiver.run.metadata.receivedAt ≤ (source initial).now

structure Release (initial : GapInitial cut sender lower upper) where
  before : Endpoint.State
  packet : EstablishedReceive.Input
  recovery : Recovery.State
  reaction : AckReaction.State
  placement : Endpoint.ClockFrame (source initial) before
  payload : packet.packet.segment.payload = lower
  filled : Endpoint.GapFilled before packet initial.receiver.run recovery reaction

def Release.after (release : Release initial) : Endpoint.State :=
  Endpoint.gapAfter release.before release.packet initial.receiver.run release.recovery release.reaction

structure ReleasedAt (initial : GapInitial cut sender lower upper) (state : Endpoint.State) where
  release : Release initial
  fixed : withoutRuntime state = withoutRuntime release.after
  time : release.before.now ≤ state.now

structure Facts (initial : GapInitial cut sender lower upper) (state : Endpoint.State) (released : Bool) where
  geometry : Geometry initial
  recovery : Recovery.State
  reaction : AckReaction.State
  runtime : state.recovery = some recovery
  ackRuntime : state.ackReaction = some reaction
  recoveryState : recovery = { initial.receiver.recovery with
    now := recovery.now, duplicateAcks := if released then 0 else initial.receiver.recovery.duplicateAcks }
  reactionOrigin : reaction.origin = initial.receiver.reaction.origin
  reactionMSS : reaction.rmss = initial.receiver.reaction.rmss
  valid : state.Valid
  coherent : Endpoint.RecoveryCoherent state
  prepared : Endpoint.AckPrepared state
  storage : Endpoint.StorageCoherent state
  unreleased : released = false → Endpoint.ClockFrame (source initial) state
  releasedAt : released = true → Nonempty (ReleasedAt initial state)

variable {initial : GapInitial cut sender lower upper} {state after : Endpoint.State} {released : Bool}

theorem upper_payload (initial : GapInitial cut sender lower upper) : initial.receiver.run.metadata.segment.payload = upper := by
  rw [initial.receiver.metadata]
  exact initial.receiver.source.origin.fields.1.symm.trans initial.receiver.bytes

theorem Facts.core (facts : Facts initial state released) : state.core =
    if released then EstablishedReceive.commit (source initial).core (lower ++ upper) 0 else (source initial).core := by
  cases released with
  | false => exact (facts.unreleased rfl).core
  | true =>
    obtain ⟨past⟩ := facts.releasedAt rfl
    have core := congrArg Endpoint.State.core past.fixed
    simpa only [withoutRuntime, Release.after, Endpoint.gapAfter_core, past.release.payload,
      initial.receiver.bytes, past.release.placement.core, ↓reduceIte] using core

theorem Facts.store (facts : Facts initial state released) : state.receiveStore =
    if released then { (source initial).receiveStore with
      frontier := (source initial).receiveStore.frontier + lower.length + upper.length
      nextID := (source initial).receiveStore.nextID + 1, held := [] }
    else (source initial).receiveStore := by
  cases released with
  | false => exact (facts.unreleased rfl).receiveStore
  | true =>
    obtain ⟨past⟩ := facts.releasedAt rfl
    have store := congrArg Endpoint.State.receiveStore past.fixed
    simpa only [withoutRuntime, Release.after, Endpoint.gapAfter_receiveStore, Endpoint.gapStore,
      past.release.payload, initial.receiver.bytes, past.release.placement.receiveStore, ↓reduceIte] using store

theorem Facts.outstanding (facts : Facts initial state released) : facts.recovery.outstanding = [] := by
  rw [facts.recoveryState]
  exact initial.receiver.idle

theorem Facts.clocked (facts : Facts initial state released) : facts.recovery.Clocked := by
  simp only [Recovery.State.Clocked, facts.outstanding, List.not_mem_nil, false_implies, implies_true]

theorem Facts.positive (facts : Facts initial state released) : facts.recovery.Positive := by
  simp only [Recovery.State.Positive, facts.outstanding, List.not_mem_nil, false_implies, implies_true]

theorem Facts.sentBy (facts : Facts initial state released) : facts.recovery.SentBy facts.recovery.now := by
  simp only [Recovery.State.SentBy, facts.outstanding, List.not_mem_nil, false_implies, implies_true]

theorem Facts.now (facts : Facts initial state released) : state.now = facts.recovery.now := by
  simp only [Endpoint.State.now, facts.runtime, Option.map_some, Option.getD_some]

theorem Facts.monotone (facts : Facts initial state released) : (source initial).now ≤ state.now := by
  cases released with
  | false => exact (facts.unreleased rfl).monotone
  | true =>
    obtain ⟨past⟩ := facts.releasedAt rfl
    exact Nat.le_trans past.release.placement.monotone past.time

theorem Facts.received (facts : Facts initial state released) : state.core.received = if released then lower ++ upper else [] := by
  rw [facts.core]
  cases released <;> simp only [source, Bool.false_eq_true, ↓reduceIte, EstablishedReceive.commit, initial.receiver.unread,
    List.nil_append]

theorem Facts.receiveNext (facts : Facts initial state released) : state.core.receiveNext =
    if released then (source initial).core.receiveNext.add (lower.length + upper.length) else (source initial).core.receiveNext := by
  rw [facts.core]
  cases released <;> simp only [Bool.false_eq_true, ite_false, ite_true, EstablishedReceive.commit, List.length_append]

theorem Facts.sendUna (facts : Facts initial state released) : state.core.sendUna = (source initial).core.sendUna := by
  rw [facts.core]
  cases released <;> simp only [Bool.false_eq_true, ite_false, ite_true, EstablishedReceive.commit, Seq.add_zero]

theorem Facts.sendNext (facts : Facts initial state released) : state.core.sendNext = (source initial).core.sendNext := by
  rw [facts.core]
  cases released <;> rfl

theorem Facts.held (facts : Facts initial state released) : state.receiveStore.held = if released then [] else [initial.receiver.run] := by
  rw [facts.store]
  cases released
  · exact initial.receiver.held
  · rfl

theorem Facts.frontier (facts : Facts initial state released) : state.receiveStore.frontier = if released then lower.length + upper.length else 0 := by
  rw [facts.store]
  cases released
  · exact initial.receiver.frontier
  · simp only [source, ↓reduceIte, initial.receiver.frontier, Nat.zero_add]

theorem Facts.nextID (facts : Facts initial state released) : state.receiveStore.nextID = if released then 2 else 1 := by
  rw [facts.store]
  cases released
  · exact initial.receiver.nextID
  · simp only [source, ↓reduceIte, initial.receiver.nextID]

theorem Facts.static_fields (facts : Facts initial state released) :
    state.pending = (source initial).pending ∧ state.pendingLimit = (source initial).pendingLimit ∧
      state.effectiveMSS = (source initial).effectiveMSS ∧ state.ipSendLimit = (source initial).ipSendLimit ∧
      state.localReceiveMSS = (source initial).localReceiveMSS := by
  cases released with
  | false =>
    have frame := facts.unreleased rfl
    exact ⟨frame.pending, frame.pendingLimit, frame.effectiveMSS, frame.ipSendLimit, frame.localReceiveMSS⟩
  | true =>
    obtain ⟨past⟩ := facts.releasedAt rfl
    have same := congrArg (fun old : Endpoint.State =>
      (old.pending, old.pendingLimit, old.effectiveMSS, old.ipSendLimit, old.localReceiveMSS)) past.fixed
    simpa only [withoutRuntime, Release.after, Endpoint.gapAfter, Endpoint.storedState, Endpoint.gapReceived,
      Endpoint.zeroRunState, past.release.placement.pending, past.release.placement.pendingLimit,
      past.release.placement.effectiveMSS, past.release.placement.ipSendLimit, past.release.placement.localReceiveMSS,
      Prod.mk.injEq] using same

theorem Facts.pending (facts : Facts initial state released) : state.pending = (source initial).pending := facts.static_fields.1

theorem Facts.pendingLimit (facts : Facts initial state released) : state.pendingLimit = (source initial).pendingLimit :=
  facts.static_fields.2.1

theorem Facts.effectiveMSS (facts : Facts initial state released) : state.effectiveMSS = (source initial).effectiveMSS :=
  facts.static_fields.2.2.1

theorem Facts.ipSendLimit (facts : Facts initial state released) : state.ipSendLimit = (source initial).ipSendLimit :=
  facts.static_fields.2.2.2.1

theorem Facts.localReceiveMSS (facts : Facts initial state released) : state.localReceiveMSS = (source initial).localReceiveMSS :=
  facts.static_fields.2.2.2.2

theorem Facts.inbound (facts : Facts initial state released) : state.core.inbound = (source initial).core.inbound := by
  rw [facts.core]
  cases released <;> rfl

theorem Facts.capacity (facts : Facts initial state released) : state.core.capacity = (source initial).core.capacity := by
  rw [facts.core]
  cases released <;> rfl

theorem Facts.seenGap (facts : Facts initial state released) : state.receiveStore.seenGap = true := by
  rw [facts.store]
  cases released
  · exact initial.receiver.seenGap
  · exact initial.receiver.seenGap

theorem Facts.sent (facts : Facts initial state released) : state.core.sent = [] := by
  have coherent := facts.coherent
  simp only [Endpoint.RecoveryCoherent, facts.runtime] at coherent
  have flight := coherent.2.2.1
  simp only [Recovery.flight, facts.outstanding, List.map_nil, List.sum_nil] at flight
  simpa only [List.length_eq_zero_iff] using flight.symm

def initial_facts (initial : GapInitial cut sender lower upper) (geometry : Geometry initial) : Facts initial (source initial) false where
  geometry
  recovery := initial.receiver.recovery
  reaction := initial.receiver.reaction
  runtime := initial.receiver.runtime
  ackRuntime := initial.receiver.ackRuntime
  recoveryState := rfl
  reactionOrigin := rfl
  reactionMSS := rfl
  valid := initial.receiver.valid
  coherent := initial.receiver.coherent
  prepared := initial.receiver.prepared
  storage := initial.receiver.storage
  unreleased := fun _ => Endpoint.ClockFrame.refl _
  releasedAt := by intro impossible; cases impossible

def Facts.clock (facts : Facts initial state released) (frame : Endpoint.ClockFrame state after)
    (timely : Endpoint.AckTimeReady state after.now) : Facts initial after released := by
  refine {
    geometry := facts.geometry, recovery := { facts.recovery with now := after.now }, reaction := facts.reaction
    runtime := frame.runtime facts.runtime, ackRuntime := frame.ackReaction.trans facts.ackRuntime
    recoveryState := ?_, reactionOrigin := facts.reactionOrigin, reactionMSS := facts.reactionMSS
    valid := frame.valid facts.valid, coherent := frame.recovery_coherent facts.coherent
    prepared := frame.ack_prepared facts.prepared timely, storage := frame.storage_coherent facts.storage
    unreleased := fun before => (facts.unreleased before).trans frame, releasedAt := ?_ }
  · rw [facts.recoveryState]
  · intro received
    obtain ⟨past⟩ := facts.releasedAt received
    have fixed := congrArg (fun old : Endpoint.State => { old with ackReaction := none }) frame.fixed.symm
    exact ⟨⟨past.release, fixed.trans past.fixed, Nat.le_trans past.time frame.monotone⟩⟩

theorem Facts.gap_conditions (facts : Facts initial state false) (packet : EstablishedReceive.Input)
    (tuple : packet.packet.header = (source initial).core.inbound)
    (controls : EstablishedReceive.control packet.packet.segment = none)
    (ack : Flags.ack packet.packet.segment.flags = true)
    (sequence : packet.packet.segment.sequence = initial.lowerSource.attempt.output.packet.segment.sequence)
    (ackOld : Seq.distance packet.packet.segment.acknowledgment (source initial).core.sendUna ≤ EstablishedReceive.maxSendWindow)
    (payload : packet.packet.segment.payload = lower) :
    Endpoint.GapReceiveConditions state packet initial.receiver.run facts.recovery facts.reaction := by
  refine ⟨facts.valid, facts.coherent, facts.prepared, facts.storage, facts.runtime, facts.ackRuntime,
    facts.outstanding, ?_, ?_, ?_, ?_, controls, ack, ?_, ?_, ?_, ?_, facts.geometry.upperControl,
    facts.geometry.upperAck, ?_, ?_, Nat.le_trans facts.geometry.upperPast facts.monotone⟩
  · exact facts.held
  · rw [facts.frontier, payload]
    simpa only [Bool.false_eq_true, ite_false, Nat.zero_add] using initial.receiver.position
  · rw [payload]; exact initial.lowerNonempty
  · rw [facts.core]; exact tuple
  · rw [facts.receiveNext]
    exact sequence.trans facts.geometry.lowerSequence
  · rw [facts.sendUna]; exact ackOld
  · exact (upper_payload initial).trans initial.receiver.bytes.symm
  · rw [facts.core]; exact facts.geometry.upperTuple
  · rw [facts.receiveNext, payload]
    exact facts.geometry.upperSequence
  · rw [facts.sendUna]; exact facts.geometry.upperAckOld

def Facts.gap_filled (facts : Facts initial state false) (packet : EstablishedReceive.Input)
    (payload : packet.packet.segment.payload = lower)
    (filled : Endpoint.GapFilled state packet initial.receiver.run facts.recovery facts.reaction) :
    Facts initial (Endpoint.gapAfter state packet initial.receiver.run facts.recovery facts.reaction) true := by
  refine {
    geometry := facts.geometry, recovery := { facts.recovery with duplicateAcks := 0 }
    reaction := Endpoint.gapReaction state packet initial.receiver.run facts.reaction
    runtime := Endpoint.gapAfter_recovery _ _ _ _ _, ackRuntime := Endpoint.gapAfter_ackReaction _ _ _ _ _
    recoveryState := ?_, reactionOrigin := facts.reactionOrigin, reactionMSS := facts.reactionMSS
    valid := filled.valid, coherent := filled.coherent, prepared := filled.prepared, storage := filled.storage
    unreleased := by intro impossible; cases impossible
    releasedAt := ?_ }
  · rw [facts.recoveryState]
    rfl
  · intro _
    let release : Release initial := ⟨state, packet, facts.recovery, facts.reaction, facts.unreleased rfl, payload, filled⟩
    refine ⟨⟨release, rfl, ?_⟩⟩
    change state.now ≤ (Endpoint.gapAfter state packet initial.receiver.run facts.recovery facts.reaction).now
    simp only [Endpoint.State.now, Endpoint.gapAfter_recovery, facts.runtime, Option.map_some, Option.getD_some, Nat.le_refl]

theorem Facts.gap_enabled (facts : Facts initial state false) (packet : EstablishedReceive.Input)
    (tuple : packet.packet.header = (source initial).core.inbound)
    (controls : EstablishedReceive.control packet.packet.segment = none)
    (ack : Flags.ack packet.packet.segment.flags = true)
    (sequence : packet.packet.segment.sequence = initial.lowerSource.attempt.output.packet.segment.sequence)
    (ackOld : Seq.distance packet.packet.segment.acknowledgment (source initial).core.sendUna ≤ EstablishedReceive.maxSendWindow)
    (payload : packet.packet.segment.payload = lower) :
    Endpoint.GapFilled state packet initial.receiver.run facts.recovery facts.reaction ∧
      Nonempty (Facts initial (Endpoint.gapAfter state packet initial.receiver.run facts.recovery facts.reaction) true) := by
  have filled := Endpoint.receive_gap_enabled (facts.gap_conditions packet tuple controls ack sequence ackOld payload)
  exact ⟨filled, ⟨facts.gap_filled packet payload filled⟩⟩

def Facts.output (facts : Facts initial state true) : Facts initial (Endpoint.outputState state) true := by
  let reaction := AckReaction.outputState facts.reaction state.now state.core.receiveNext state.core.capacity state.core.window state.effectiveMSS
  refine {
    geometry := facts.geometry, recovery := facts.recovery, reaction, runtime := facts.runtime
    ackRuntime := ?_, recoveryState := facts.recoveryState
    reactionOrigin := facts.reactionOrigin, reactionMSS := facts.reactionMSS
    valid := facts.valid, coherent := facts.coherent, prepared := Endpoint.outputState_ackPrepared state facts.prepared
    storage := Endpoint.outputState_storage_coherent state facts.prepared facts.storage
    unreleased := by intro impossible; cases impossible
    releasedAt := ?_ }
  · simp only [Endpoint.outputState, facts.ackRuntime, Option.map_some]
    rfl
  · intro _
    obtain ⟨past⟩ := facts.releasedAt rfl
    exact ⟨⟨past.release, past.fixed, past.time⟩⟩

def Facts.sequence (facts : Facts initial state true) : Facts initial (Endpoint.sequenceAfter state facts.reaction) true := by
  refine {
    geometry := facts.geometry, recovery := facts.recovery
    reaction := AckReaction.receiveSequence facts.reaction state.now state.core.receiveNext
    runtime := facts.runtime, ackRuntime := rfl, recoveryState := facts.recoveryState
    reactionOrigin := facts.reactionOrigin, reactionMSS := facts.reactionMSS
    valid := facts.valid, coherent := facts.coherent
    prepared := Endpoint.sequenceAfter_prepared state facts.reaction facts.ackRuntime facts.prepared
    storage := ?_, unreleased := by intro impossible; cases impossible
    releasedAt := ?_ }
  · simpa only [Endpoint.sequenceAfter, Endpoint.StorageCoherent, Endpoint.State.StorageValid,
      facts.ackRuntime, AckReaction.receiveSequence, AckReaction.State.window] using facts.storage
  · intro _
    obtain ⟨past⟩ := facts.releasedAt rfl
    exact ⟨⟨past.release, past.fixed, past.time⟩⟩

theorem Facts.emit_ack (facts : Facts initial state true) (pending : facts.reaction.work.pending ≠ []) :
    ∃ packet, Endpoint.emitAck state true =
        ⟨Endpoint.outputState state, .accepted .emitAck, some packet, [], none⟩ ∧
      Endpoint.emit state [] = .ok packet ∧ packet.packet.segment.payload = [] ∧
      packet.packet.header = Output.reverse (source initial).core.inbound ∧
      packet.packet.segment.sequence = (source initial).core.sendNext ∧
      packet.packet.segment.acknowledgment = (source initial).core.receiveNext.add (lower.length + upper.length) ∧
      packet.packet.segment.window.val = Endpoint.outputWindow state ∧ packet.packet.ip.packet.ttl.toNat = 64 ∧
      Nonempty (Facts initial (Endpoint.outputState state) true) := by
  have available := Endpoint.responseAvailable_of_pending state facts.reaction facts.ackRuntime pending
  obtain ⟨packet, actual, encoded⟩ := Endpoint.emitAck_success_enabled state facts.valid facts.prepared available
  have fields := Endpoint.emit_transport state [] packet encoded
  refine ⟨packet, actual, encoded, Endpoint.emit_payload state [] packet encoded, ?_,
    fields.2.1.trans facts.sendNext, ?_, fields.2.2.2.1,
    CampusTCPRoundLocal.emit_ttl state [] packet encoded, ⟨facts.output⟩⟩
  · simpa only [facts.core, ↓reduceIte, EstablishedReceive.commit] using fields.1
  · simpa only [facts.receiveNext, ↓reduceIte] using fields.2.2.1

theorem Facts.old_span_ready (facts : Facts initial state true) (packet : EstablishedReceive.Input)
    (tuple : packet.packet.header = (source initial).core.inbound)
    (controls : EstablishedReceive.control packet.packet.segment = none)
    (sequence : packet.packet.segment.sequence = initial.lowerSource.attempt.output.packet.segment.sequence)
    (payload : packet.packet.segment.payload = lower) :
    CampusTCPGapOldData.OldSpanReady state packet facts.reaction (lower.length + upper.length) := by
  refine ⟨facts.coherent, facts.prepared, facts.storage, facts.ackRuntime, ?_, controls, ?_, ?_, ?_, ?_⟩
  · rw [facts.core]
    exact tuple
  · rw [payload]; exact initial.lowerNonempty
  · rw [payload]
    omega
  · rw [sequence, facts.geometry.lowerSequence, facts.receiveNext]
    rfl
  · have room := Endpoint.offeredWindow_le state facts.prepared.1
    have capacity := facts.valid.1.2.2.1
    have fits := facts.valid.1.2.1
    simp only [EstablishedReceive.State.window, facts.received, ↓reduceIte, List.length_append] at room fits
    unfold Seq.modulus
    omega

theorem Facts.old_span_strict (_facts : Facts initial state true) (packet : EstablishedReceive.Input)
    (payload : packet.packet.segment.payload = lower) :
    packet.packet.segment.payload.length < lower.length + upper.length := by
  rw [payload]
  have upperPositive := List.length_pos_iff.mpr initial.upperNonempty
  omega

theorem Facts.receive_old (facts : Facts initial state true) (packet : EstablishedReceive.Input)
    (tuple : packet.packet.header = (source initial).core.inbound)
    (controls : EstablishedReceive.control packet.packet.segment = none)
    (sequence : packet.packet.segment.sequence = initial.lowerSource.attempt.output.packet.segment.sequence)
    (payload : packet.packet.segment.payload = lower) :
    Endpoint.receive state packet =
      ⟨Endpoint.sequenceAfter state facts.reaction, .reject (.input .sequence), none, [],
        some (ReceiveReassembly.request state.core (Endpoint.offeredWindow state) .sequence)⟩ ∧
      Endpoint.receiveRuns state packet = [] ∧ Endpoint.receivedBytes state packet = [] ∧
      Nonempty (Facts initial (Endpoint.sequenceAfter state facts.reaction) true) ∧
      Endpoint.ResponseAvailable (Endpoint.sequenceAfter state facts.reaction) true := by
  have ready := facts.old_span_ready packet tuple controls sequence payload
  obtain ⟨actual, runs, released, _, available⟩ := Endpoint.receive_old_span state packet facts.reaction
    (lower.length + upper.length) facts.valid facts.coherent facts.prepared facts.storage facts.ackRuntime
    ready.tuple ready.controls ready.nonempty ready.inside ready.cursor ready.epoch
  exact ⟨actual, runs, released, ⟨facts.sequence⟩, available⟩

def Facts.old_delivered {events : List CampusTCPModel.Event} {report : Report input events} {endpoints : Applications complete}
    {index : Nat} {served : Served input} {emission : WireForwarding.Emission served.ticket.value.source.packet}
    {emitted : served.evidence.output = some emission}
    (facts : Facts initial (endpoint endpoints served.ticket.value.produced.actor.other) true)
    (delivery : CampusTCPTimedOldData.OldDataDelivered report complete endpoints index served emission emitted facts.reaction) :
    Facts initial delivery.after true := by
  rw [delivery.afterEq]
  exact facts.sequence

theorem Facts.header_effects (facts : Facts initial state true) :
    ∃ release : Release initial,
      state.sendWindow = release.after.sendWindow ∧ state.sendWL1 = release.after.sendWL1 ∧
      state.sendWL2 = release.after.sendWL2 ∧ state.lastAckWindow = release.after.lastAckWindow ∧
      (Endpoint.receiveEffect release.before release.packet).headers.map (fun header =>
        (header.run.receipt, header.run.metadata.receivedAt, header.acknowledged)) =
        [(release.before.receiveStore.nextID, release.before.now, 0),
          (initial.receiver.run.receipt, initial.receiver.run.metadata.receivedAt, 0)] := by
  obtain ⟨past⟩ := facts.releasedAt rfl
  refine ⟨past.release, ?_, ?_, ?_, ?_, past.release.filled.header_receipts⟩
  · simpa only [withoutRuntime] using congrArg Endpoint.State.sendWindow past.fixed
  · simpa only [withoutRuntime] using congrArg Endpoint.State.sendWL1 past.fixed
  · simpa only [withoutRuntime] using congrArg Endpoint.State.sendWL2 past.fixed
  · simpa only [withoutRuntime] using congrArg Endpoint.State.lastAckWindow past.fixed

end Netlib.Check.CampusTCPGapProgressReceiver
