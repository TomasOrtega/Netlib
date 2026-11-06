import Netlib.Check.CampusTCPRoundEndpointGuards
import Netlib.Check.CampusTCPRoundStart
import Netlib.Protocol.TCP.EndpointClockEnabled
import Netlib.Protocol.TCP.EndpointAckReceiveEnabled

/-!
# The actual receiver state in one recovery round

The first selected data receipt releases the range once.
Later whole-old receipts keep these bytes and cause new ACK work.
-/

namespace Netlib.Check.CampusTCPRecoveryRoundReceiver

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRoundSetup

variable {input : Input} {events : List Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}

def initialReaction : AckReaction.State := AckReaction.initial complete.certificate.passiveSeed.core.receiveNext
  complete.certificate.passiveSeed.core.capacity complete.certificate.passiveSeed.localReceiveMSS.limit

structure Facts (initial : Initial report complete request) (state : Endpoint.State) (released : Bool) where
  recovery : Recovery.State
  reaction : AckReaction.State
  runtime : state.recovery = some recovery
  ackRuntime : state.ackReaction = some reaction
  recoveryState : recovery = { Recovery.initial complete.certificate.passiveSeed.effectiveMSS with now := recovery.now }
  valid : state.Valid
  coherent : Endpoint.RecoveryCoherent state
  prepared : Endpoint.AckPrepared state
  storage : Endpoint.StorageCoherent state
  core : state.core = { complete.certificate.passiveSeed.core with
    received := if released then request.bytes else []
    receiveNext := if released then complete.certificate.passiveSeed.core.receiveNext.add request.bytes.length
      else complete.certificate.passiveSeed.core.receiveNext }
  pending : state.pending = []
  pendingLimit : state.pendingLimit = complete.certificate.passiveSeed.pendingLimit
  mss : state.effectiveMSS = complete.certificate.passiveSeed.effectiveMSS
  ipLimit : state.ipSendLimit = complete.certificate.passiveSeed.ipSendLimit
  receiveMSS : state.localReceiveMSS = complete.certificate.passiveSeed.localReceiveMSS
  held : state.receiveStore.held = []
  frontier : state.receiveStore.frontier = if released then request.bytes.length else 0
  nextID : state.receiveStore.nextID = if released then 1 else 0
  seenGap : state.receiveStore.seenGap = false
  unreleased : released = false → reaction = initialReaction (complete := complete)

variable {initial : Initial report complete request} {state after : Endpoint.State} {released : Bool}

theorem Facts.outstanding (facts : Facts initial state released) : facts.recovery.outstanding = [] := by
  rw [facts.recoveryState]
  rfl

theorem Facts.clocked (facts : Facts initial state released) : facts.recovery.Clocked := by
  simp only [Recovery.State.Clocked, facts.outstanding, List.not_mem_nil, false_implies, implies_true]

theorem Facts.sentBy (facts : Facts initial state released) : facts.recovery.SentBy facts.recovery.now := by
  simp only [Recovery.State.SentBy, facts.outstanding, List.not_mem_nil, false_implies, implies_true]

theorem Facts.positive (facts : Facts initial state released) : facts.recovery.Positive := by
  simp only [Recovery.State.Positive, facts.outstanding, List.not_mem_nil, false_implies, implies_true]

theorem Facts.sent (facts : Facts initial state released) : state.core.sent = [] := by
  rw [facts.core]
  exact complete.certificate.empty.2.2.2.2.1

theorem Facts.sendUna (facts : Facts initial state released) : state.core.sendUna = input.passive.iss.add 1 := by
  rw [facts.core]
  simpa only [complete.passiveConfig] using complete.certificate.initial_sequences.2.2.2.1

theorem Facts.sendNext (facts : Facts initial state released) : state.core.sendNext = input.passive.iss.add 1 := by
  rw [facts.core]
  simpa only [complete.passiveConfig] using complete.certificate.initial_sequences.2.2.2.2.1

theorem Facts.receiveNext (facts : Facts initial state released) :
    state.core.receiveNext = if released then (input.active.iss.add 1).add request.bytes.length else input.active.iss.add 1 := by
  have cursor := complete.certificate.initial_sequences.2.2.2.2.2
  simp only [complete.activeConfig] at cursor
  simp only [facts.core, cursor]

theorem Facts.received (facts : Facts initial state released) : state.core.received = if released then request.bytes else [] := by
  rw [facts.core]

theorem Facts.unreleased_core (facts : Facts initial state false) : state.core = complete.certificate.passiveSeed.core := by
  rw [facts.core]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [← complete.certificate.empty.2.2.2.2.2]

def initial_facts (initial : Initial report complete request) :
    Facts initial (endpoint initial.start.next.endpoints .server) false := by
  have guarded := CampusTCPRoundGuards.PreparedStart.server_guards initial.start
  refine {
    recovery := Recovery.initial complete.certificate.passiveSeed.effectiveMSS
    reaction := initialReaction
    runtime := ?_, ackRuntime := ?_, recoveryState := rfl
    valid := endpoint_valid initial.start.next.endpoints .server
    coherent := guarded.recoveryCoherent, prepared := guarded.prepared, storage := ?_
    core := ?_, pending := ?_, pendingLimit := ?_, mss := ?_, ipLimit := ?_, receiveMSS := ?_
    held := ?_, frontier := ?_, nextID := ?_, seenGap := ?_, unreleased := fun _ => rfl }
  all_goals rw [initial.start.server]
  · rfl
  · rfl
  · exact CampusTCPRoundLocal.prepared_storage _ complete.certificate.empty.2.2.2.2.2
      complete.certificate.receiveStore_initial.2
  · change complete.certificate.passiveSeed.core = { complete.certificate.passiveSeed.core with received := [] }
    rw [← complete.certificate.empty.2.2.2.2.2]
  · exact complete.certificate.empty.2.2.2.1
  · rfl
  · rfl
  · rfl
  · rfl
  · change complete.certificate.passiveSeed.receiveStore.held = []
    rw [complete.certificate.receiveStore_initial.2]
    rfl
  · change complete.certificate.passiveSeed.receiveStore.frontier = 0
    rw [complete.certificate.receiveStore_initial.2]
    rfl
  · change complete.certificate.passiveSeed.receiveStore.nextID = 0
    rw [complete.certificate.receiveStore_initial.2]
    rfl
  · change complete.certificate.passiveSeed.receiveStore.seenGap = false
    rw [complete.certificate.receiveStore_initial.2]
    rfl

def Facts.clock (facts : Facts initial state released) (frame : Endpoint.ClockFrame state after)
    (timely : Endpoint.AckTimeReady state after.now) : Facts initial after released := by
  refine {
    recovery := { facts.recovery with now := after.now }, reaction := facts.reaction
    runtime := frame.runtime facts.runtime, ackRuntime := frame.ackReaction.trans facts.ackRuntime
    recoveryState := ?_, valid := frame.valid facts.valid, coherent := frame.recovery_coherent facts.coherent
    prepared := frame.ack_prepared facts.prepared timely, storage := frame.storage_coherent facts.storage
    core := frame.core.trans facts.core, pending := frame.pending.trans facts.pending
    pendingLimit := frame.pendingLimit.trans facts.pendingLimit, mss := frame.effectiveMSS.trans facts.mss
    ipLimit := frame.ipSendLimit.trans facts.ipLimit, receiveMSS := frame.localReceiveMSS.trans facts.receiveMSS
    held := ?_, frontier := ?_, nextID := ?_, seenGap := ?_, unreleased := facts.unreleased }
  · rw [facts.recoveryState]
  · rw [frame.receiveStore]
    exact facts.held
  · rw [frame.receiveStore]
    exact facts.frontier
  · rw [frame.receiveStore]
    exact facts.nextID
  · rw [frame.receiveStore]
    exact facts.seenGap

private theorem storage_of_empty (state : Endpoint.State) (reaction : AckReaction.State)
    (prepared : Endpoint.AckPrepared state) (stored : state.ackReaction = some reaction)
    (empty : state.receiveStore.held = [])
    (frontier : reaction.advertisement.frontier = state.receiveStore.frontier) : Endpoint.StorageCoherent state := by
  have room : reaction.window ≤ state.core.window := by
    simpa only [Endpoint.offeredWindow, stored] using Endpoint.offeredWindow_le state prepared.1
  refine ⟨Endpoint.storage_valid_of_empty state empty, ?_⟩
  rw [stored]
  exact ⟨frontier, Endpoint.store_valid_empty _ _ _ empty room⟩

def Facts.output (facts : Facts initial state released) : Facts initial (Endpoint.outputState state) released := by
  let reaction := AckReaction.outputState facts.reaction state.now state.core.receiveNext
    state.core.capacity state.core.window state.effectiveMSS
  have stored : (Endpoint.outputState state).ackReaction = some reaction := by
    simp only [Endpoint.outputState, facts.ackRuntime, Option.map_some]
    rfl
  have prepared := Endpoint.outputState_ackPrepared state facts.prepared
  have empty : (Endpoint.outputState state).receiveStore.held = [] := facts.held
  have frontier : reaction.advertisement.frontier = (Endpoint.outputState state).receiveStore.frontier := by
    have old := facts.storage.2
    rw [facts.ackRuntime] at old
    exact old.1
  refine {
    recovery := facts.recovery, reaction, runtime := facts.runtime, ackRuntime := stored
    recoveryState := facts.recoveryState, valid := facts.valid, coherent := facts.coherent, prepared
    storage := storage_of_empty _ _ prepared stored empty frontier, core := facts.core, pending := facts.pending
    pendingLimit := facts.pendingLimit, mss := facts.mss, ipLimit := facts.ipLimit, receiveMSS := facts.receiveMSS
    held := facts.held, frontier := facts.frontier, nextID := facts.nextID, seenGap := facts.seenGap, unreleased := ?_ }
  intro unreleased
  cases unreleased
  change AckReaction.outputState facts.reaction state.now state.core.receiveNext
    state.core.capacity state.core.window state.effectiveMSS = initialReaction
  rw [facts.unreleased rfl, facts.unreleased_core]
  simp only [initialReaction, EstablishedReceive.State.window, complete.certificate.empty.2.2.2.2.2,
    List.length_nil, Nat.sub_zero]
  exact CampusTCPRoundEndpointGeometry.initial_ack_output _ _ _ _ _

def Facts.sequence (facts : Facts initial state true) :
    Facts initial (Endpoint.sequenceAfter state facts.reaction) true := by
  refine {
    recovery := facts.recovery
    reaction := AckReaction.receiveSequence facts.reaction state.now state.core.receiveNext
    runtime := facts.runtime, ackRuntime := rfl, recoveryState := facts.recoveryState
    valid := facts.valid, coherent := facts.coherent
    prepared := Endpoint.sequenceAfter_prepared state facts.reaction facts.ackRuntime facts.prepared
    storage := ?_, core := facts.core, pending := facts.pending, pendingLimit := facts.pendingLimit
    mss := facts.mss, ipLimit := facts.ipLimit, receiveMSS := facts.receiveMSS
    held := facts.held, frontier := facts.frontier, nextID := facts.nextID, seenGap := facts.seenGap
    unreleased := by intro impossible; cases impossible }
  simpa only [Endpoint.StorageCoherent, Endpoint.State.StorageValid, Endpoint.sequenceAfter,
    facts.ackRuntime, AckReaction.receiveSequence, AckReaction.State.window] using facts.storage

theorem Facts.sequence_available (facts : Facts initial state true) :
    Endpoint.ResponseAvailable (Endpoint.sequenceAfter state facts.reaction) true :=
  Endpoint.sequenceAfter_dispatch state facts.reaction

theorem Facts.old_geometry (facts : Facts initial state true) (packet : EstablishedReceive.Input)
    (sequence : packet.packet.segment.sequence = input.active.iss.add 1)
    (payload : packet.packet.segment.payload = request.bytes) :
    packet.packet.segment.payload ≠ [] ∧
      packet.packet.segment.sequence.add packet.packet.segment.payload.length = state.core.receiveNext ∧
      packet.packet.segment.payload.length + Endpoint.offeredWindow state ≤ Seq.modulus := by
  refine ⟨by rw [payload]; exact request.nonempty, ?_, ?_⟩
  · simp only [payload, sequence, facts.receiveNext, ↓reduceIte]
  · have room := Endpoint.offeredWindow_le state facts.prepared.1
    have capacity := facts.valid.1.2.2.1
    have fits := facts.valid.1.2.1
    simp only [EstablishedReceive.State.window, facts.received, ↓reduceIte] at room fits
    rw [payload]
    unfold Seq.modulus
    omega

theorem Facts.in_order_ready (facts : Facts initial state false) (packet : EstablishedReceive.Input)
    (tuple : packet.packet.header = complete.certificate.passiveSeed.core.inbound)
    (controls : EstablishedReceive.control packet.packet.segment = none)
    (ack : Flags.ack packet.packet.segment.flags = true)
    (sequence : packet.packet.segment.sequence = input.active.iss.add 1)
    (acknowledgment : packet.packet.segment.acknowledgment = input.passive.iss.add 1)
    (payload : packet.packet.segment.payload = request.bytes) :
    CampusTCPDeliveryEnabled.InOrderReady state packet facts.recovery facts.reaction := by
  refine ⟨facts.coherent, facts.prepared, facts.storage, facts.runtime, facts.ackRuntime, facts.sentBy,
    facts.held, ?_, controls, ack, ?_, ?_, ?_, ?_⟩
  · rw [facts.unreleased_core]
    exact tuple
  · rw [facts.receiveNext]
    exact sequence
  · rw [payload]
    exact request.nonempty
  · simp only [Endpoint.offeredWindow, facts.ackRuntime, facts.unreleased rfl, initialReaction,
      AckReaction.initial, AckReaction.State.window, ReceiveAdvertisement.State.window,
      ReceiveAdvertisement.initial, Nat.sub_zero, payload]
    simpa only [complete.certificate.configuration.2.2.2.1, complete.passiveConfig] using request.receiveFits
  · simp only [Endpoint.inOrderCount, facts.sendUna, acknowledgment, Seq.distance_self, facts.sent,
      List.length_nil, Nat.le_refl]

theorem Facts.receive_data (facts : Facts initial state false) (packet : EstablishedReceive.Input)
    (tuple : packet.packet.header = complete.certificate.passiveSeed.core.inbound)
    (controls : EstablishedReceive.control packet.packet.segment = none)
    (ack : Flags.ack packet.packet.segment.flags = true)
    (sequence : packet.packet.segment.sequence = input.active.iss.add 1)
    (acknowledgment : packet.packet.segment.acknowledgment = input.passive.iss.add 1)
    (payload : packet.packet.segment.payload = request.bytes) :
    ∃ after, Endpoint.receive state packet =
      ⟨after, .accepted (.receive 0 request.bytes.length), none, [],
        some (ReceiveReassembly.request after.core (Endpoint.offeredWindow after) .data)⟩ ∧
      Endpoint.receiveRuns state packet = [Endpoint.inOrderRun state packet] ∧
      Endpoint.receivedBytes state packet = request.bytes ∧
      Nonempty (Facts initial after true) ∧ Endpoint.ResponseAvailable after false := by
  have ready := facts.in_order_ready packet tuple controls ack sequence acknowledgment payload
  have zero : Endpoint.inOrderCount state packet = 0 := by
    simp only [Endpoint.inOrderCount, facts.sendUna, acknowledgment, Seq.distance_self]
  have now : state.now = facts.recovery.now := by
    simp only [Endpoint.State.now, facts.runtime, Option.map_some, Option.getD_some]
  have unchanged : Recovery.acknowledgeAt facts.recovery 0 state.now = .ok facts.recovery := by
    rw [now, facts.recoveryState]
    simp [Recovery.acknowledgeAt, Recovery.touched, Recovery.acknowledge, Recovery.acknowledgeState,
      Recovery.acknowledgeAtState, Recovery.initial, Except.map]
  obtain ⟨acknowledged, after, computed, afterEq, actual, runs, bytes, valid, coherent, prepared, storage⟩ :=
    Endpoint.receive_inOrder_prepared state packet facts.recovery facts.reaction facts.valid ready.recoveryCoherent
      ready.ackPrepared ready.storageCoherent ready.runtime ready.ackRuntime ready.sent ready.empty ready.tuple
      ready.controls ready.acknowledgment ready.sequence ready.nonempty ready.fits ready.bounded
  rw [zero] at computed
  have same : acknowledged = facts.recovery := Except.ok.inj (computed.symm.trans unchanged)
  subst acknowledged
  subst after
  refine ⟨_, by simpa only [zero, payload] using actual, runs, by simpa only [payload] using bytes, ?_,
    Endpoint.inOrderAfterWith_response _ _ _ _⟩
  have duplicate : { facts.recovery with duplicateAcks := 0 } = facts.recovery := by
    rw [facts.recoveryState]
    rfl
  refine ⟨{
    recovery := facts.recovery
    reaction := AckReaction.receiveRelease facts.reaction state.now (state.core.receiveNext.add request.bytes.length)
      request.bytes.length request.bytes.length false
    runtime := ?_, ackRuntime := ?_, recoveryState := facts.recoveryState
    valid, coherent, prepared, storage, core := ?_, pending := ?_, pendingLimit := ?_, mss := ?_
    ipLimit := ?_, receiveMSS := ?_, held := ?_, frontier := ?_, nextID := ?_, seenGap := ?_
    unreleased := by intro impossible; cases impossible }⟩
  · simp only [Endpoint.inOrderAfterWith, Endpoint.windowState_recovery, duplicate]
  · simp only [Endpoint.inOrderAfterWith, Endpoint.windowState_ackReaction, payload]
  · simp only [Endpoint.inOrderAfterWith, Endpoint.windowState_core, Endpoint.inOrderCore,
      EstablishedReceive.commit, zero, payload, facts.unreleased_core, List.drop_zero,
      complete.certificate.empty.2.2.2.2.2, List.nil_append, Seq.add_zero, ↓reduceIte]
  · simpa only [Endpoint.inOrderAfterWith, Endpoint.windowState_pending] using facts.pending
  · unfold Endpoint.inOrderAfterWith Endpoint.windowState
    split <;> exact facts.pendingLimit
  · simpa only [Endpoint.inOrderAfterWith, Endpoint.windowState_effectiveMSS] using facts.mss
  · unfold Endpoint.inOrderAfterWith Endpoint.windowState
    split <;> exact facts.ipLimit
  · simpa only [Endpoint.inOrderAfterWith, Endpoint.windowState_ownMSS] using facts.receiveMSS
  · simp only [Endpoint.inOrderAfterWith, Endpoint.windowState_receiveStore, Endpoint.inOrderStore]
  · simp only [Endpoint.inOrderAfterWith, Endpoint.windowState_receiveStore, Endpoint.inOrderStore,
      facts.frontier, payload, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
  · simp only [Endpoint.inOrderAfterWith, Endpoint.windowState_receiveStore, Endpoint.inOrderStore,
      facts.nextID, Bool.false_eq_true, ↓reduceIte]
  · simpa only [Endpoint.inOrderAfterWith, Endpoint.windowState_receiveStore, Endpoint.inOrderStore] using facts.seenGap

theorem Facts.emit_ack (facts : Facts initial state true) (pending : facts.reaction.work.pending ≠ []) :
    ∃ packet, Endpoint.emitAck state true =
      ⟨Endpoint.outputState state, .accepted .emitAck, some packet, [], none⟩ ∧
      Endpoint.emit state [] = .ok packet ∧ packet.packet.segment.payload = [] ∧
      packet.packet.header = Output.reverse complete.certificate.passiveSeed.core.inbound ∧
      packet.packet.segment.sequence = input.passive.iss.add 1 ∧
      packet.packet.segment.acknowledgment = (input.active.iss.add 1).add request.bytes.length ∧
      packet.packet.segment.window.val = Endpoint.outputWindow state ∧
      Nonempty (Facts initial (Endpoint.outputState state) true) := by
  have available := Endpoint.responseAvailable_of_pending state facts.reaction facts.ackRuntime pending
  obtain ⟨packet, computed, encoded⟩ := Endpoint.emitAck_success_enabled state facts.valid facts.prepared available
  have fields := Endpoint.emit_transport state [] packet encoded
  refine ⟨packet, computed, encoded, Endpoint.emit_payload state [] packet encoded, ?_,
    fields.2.1.trans facts.sendNext, ?_, fields.2.2.2.1, ⟨facts.output⟩⟩
  · simpa only [facts.core] using fields.1
  · simpa only [facts.receiveNext, ↓reduceIte] using fields.2.2.1

theorem Facts.receive_old (facts : Facts initial state true) (packet : EstablishedReceive.Input)
    (tuple : packet.packet.header = complete.certificate.passiveSeed.core.inbound)
    (controls : EstablishedReceive.control packet.packet.segment = none)
    (sequence : packet.packet.segment.sequence = input.active.iss.add 1)
    (payload : packet.packet.segment.payload = request.bytes) :
    Endpoint.receive state packet =
      ⟨Endpoint.sequenceAfter state facts.reaction, .reject (.input .sequence), none, [],
        some (ReceiveReassembly.request state.core (Endpoint.offeredWindow state) .sequence)⟩ ∧
      Endpoint.receiveRuns state packet = [] ∧ Endpoint.receivedBytes state packet = [] ∧
      Nonempty (Facts initial (Endpoint.sequenceAfter state facts.reaction) true) ∧
      Endpoint.ResponseAvailable (Endpoint.sequenceAfter state facts.reaction) true := by
  obtain ⟨nonempty, ends, epoch⟩ := facts.old_geometry packet sequence payload
  have packetTuple : packet.packet.header = state.core.inbound := by simpa only [facts.core] using tuple
  obtain ⟨computed, runs, released, _, available⟩ := Endpoint.receive_old_whole_range state packet facts.reaction
    facts.valid facts.coherent facts.prepared facts.storage facts.ackRuntime packetTuple controls nonempty ends epoch
  exact ⟨computed, runs, released, ⟨facts.sequence⟩, available⟩

end Netlib.Check.CampusTCPRecoveryRoundReceiver
