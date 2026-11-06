import Netlib.Check.CampusTCPRoundEndpointGuards
import Netlib.Check.CampusTCPRoundStart
import Netlib.Protocol.TCP.EndpointClockEnabled
import Netlib.Protocol.TCP.EndpointTimeoutEnabled

/-!
# The actual sender ledger in one recovery round

The selected range keeps one original identity across clocks and timer retries.
The current ledger supplies timeout and covering-ACK guards.
-/

namespace Netlib.Check.CampusTCPRecoveryRoundSender

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRoundSetup

variable {input : Input} {events : List Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}

def preparedClient (initial : Initial report complete request) : Endpoint.State :=
  endpoint initial.start.next.endpoints .client

def sentState (initial : Initial report complete request) : Endpoint.State :=
  Endpoint.sendState (preparedClient initial) request.bytes.length

def withoutRecovery (state : Endpoint.State) : Endpoint.State := { state with recovery := none }

def reaction : AckReaction.State := AckReaction.initial complete.certificate.activeSeed.core.receiveNext
  complete.certificate.activeSeed.core.capacity complete.certificate.activeSeed.localReceiveMSS.limit

theorem prepared_runtime (initial : Initial report complete request) :
    (preparedClient initial).recovery = some (Recovery.initial complete.certificate.activeSeed.effectiveMSS) := by
  rw [preparedClient, initial.start.client]
  rfl

theorem prepared_reaction (initial : Initial report complete request) :
    (preparedClient initial).ackReaction = some (reaction (complete := complete)) := by
  rw [preparedClient, initial.start.client]
  rfl

theorem prepared_output (initial : Initial report complete request) :
    Endpoint.outputState (preparedClient initial) = preparedClient initial := by
  rw [preparedClient, initial.start.client]
  exact CampusTCPRoundEndpointGeometry.prepared_write_output _ _ complete.certificate.empty.2.2.1

theorem sent_core (initial : Initial report complete request) :
    (sentState initial).core = { complete.certificate.activeSeed.core with
      sent := request.bytes, sendNext := complete.certificate.activeSeed.core.sendNext.add request.bytes.length } := by
  simp only [sentState, Endpoint.sendState, preparedClient, initial.start.client, Endpoint.writeState,
    preparedSeed, ackState, recoveryState, complete.certificate.empty.1, complete.certificate.empty.2.1,
    List.nil_append, List.take_length]

theorem sent_runtime (initial : Initial report complete request) :
    (sentState initial).recovery = some (Recovery.sent (Recovery.initial complete.certificate.activeSeed.effectiveMSS)
      request.bytes.length) := by
  simp only [sentState, Endpoint.sendState, prepared_runtime, Option.map_some]

theorem sent_reaction (initial : Initial report complete request) :
    (sentState initial).ackReaction = some (reaction (complete := complete)) := by
  change (Endpoint.outputState (preparedClient initial)).ackReaction = _
  rw [prepared_output, prepared_reaction]

theorem sent_storage (initial : Initial report complete request) : Endpoint.StorageCoherent (sentState initial) := by
  rw [sentState, preparedClient, initial.start.client]
  simp only [Endpoint.sendState, CampusTCPRoundEndpointGeometry.prepared_write_output _ _
    complete.certificate.empty.2.2.1]
  change Endpoint.StorageCoherent (preparedSeed complete.certificate.activeSeed)
  exact CampusTCPRoundLocal.prepared_storage _ complete.certificate.empty.2.2.1
    complete.certificate.receiveStore_initial.1

structure Flight (initial : Initial report complete request) (sentAt : Nat) (state : Endpoint.State) (retries : Nat) where
  recovery : Recovery.State
  entry : Recovery.Outstanding
  bound : retries ≤ 2
  fixed : withoutRecovery state = withoutRecovery (sentState initial)
  runtime : state.recovery = some recovery
  source : recovery.outstanding = [entry]
  count : entry.count = request.bytes.length
  originalID : entry.id = 0
  originalStart : entry.start = 0
  originalTime : entry.sentAt = sentAt
  firstTime : retries = 0 → entry.lastAt = sentAt
  rto : recovery.rto = 2 ^ retries * 1000
  deadline : recovery.deadline = some (entry.lastAt + recovery.rto)
  attempts : recovery.timeoutCount = retries
  retried : entry.retried = decide (0 < retries)
  timedOut : recovery.lastTimedOut = if retries = 0 then none else some entry.id
  nextId : recovery.nextId = 1
  frontier : recovery.frontier = request.bytes.length
  estimator : recovery.estimator = none
  sample : recovery.lastSample = none
  duplicateAcks : recovery.duplicateAcks = 0
  valid : state.Valid
  coherent : Endpoint.RecoveryCoherent state
  prepared : Endpoint.AckPrepared state
  storage : Endpoint.StorageCoherent state
  clocked : recovery.Clocked

variable {initial : Initial report complete request} {state after : Endpoint.State} {sentAt retries : Nat}

theorem Flight.core (flight : Flight initial sentAt state retries) : state.core = (sentState initial).core := by
  simpa only [withoutRecovery] using congrArg Endpoint.State.core flight.fixed

theorem Flight.sendWindow (flight : Flight initial sentAt state retries) :
    state.sendWindow = (sentState initial).sendWindow := by
  simpa only [withoutRecovery] using congrArg Endpoint.State.sendWindow flight.fixed

theorem Flight.receiveStore (flight : Flight initial sentAt state retries) :
    state.receiveStore = (sentState initial).receiveStore := by
  simpa only [withoutRecovery] using congrArg Endpoint.State.receiveStore flight.fixed

theorem Flight.ackReaction (flight : Flight initial sentAt state retries) :
    state.ackReaction = some (reaction (complete := complete)) :=
  (congrArg Endpoint.State.ackReaction flight.fixed).trans (sent_reaction initial)

theorem Flight.sent (flight : Flight initial sentAt state retries) : state.core.sent = request.bytes := by
  rw [flight.core, sent_core]

theorem Flight.positive (flight : Flight initial sentAt state retries) : flight.recovery.Positive := by
  intro entry member
  have same : entry = flight.entry := by simpa only [flight.source, List.mem_singleton] using member
  rw [same, flight.count]
  exact request.positive

theorem Flight.flight_count (flight : Flight initial sentAt state retries) :
    Recovery.flight flight.recovery = request.bytes.length := by
  simp only [Recovery.flight, flight.source, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero, flight.count]

theorem Flight.ack_empty (flight : Flight initial sentAt state retries) (value : AckReaction.State)
    (stored : state.ackReaction = some value) : value.work.pending = [] := by
  rw [flight.ackReaction] at stored
  cases stored
  rfl

theorem Flight.ack_time_ready (flight : Flight initial sentAt state retries) (millis : Nat) :
    Endpoint.AckTimeReady state millis := by
  intro value stored
  simp only [AckReaction.State.WithinTime, flight.ack_empty value stored, List.not_mem_nil,
    false_implies, implies_true]

theorem Flight.outputState (flight : Flight initial sentAt state retries) : Endpoint.outputState state = state := by
  have received := complete.certificate.empty.2.2.1
  have unchanged : (Endpoint.outputState state).ackReaction = state.ackReaction := by
    simp only [Endpoint.outputState, flight.ackReaction, Option.map_some, flight.core, sent_core, reaction,
      EstablishedReceive.State.window, received, List.length_nil, Nat.sub_zero]
    rw [CampusTCPRoundEndpointGeometry.initial_ack_output]
  change { state with ackReaction := (Endpoint.outputState state).ackReaction } = state
  rw [unchanged]

def Flight.clock (flight : Flight initial sentAt state retries) (frame : Endpoint.ClockFrame state after)
    (timely : Endpoint.AckTimeReady state after.now) : Flight initial sentAt after retries := by
  refine {
    recovery := { flight.recovery with now := after.now }, entry := flight.entry
    bound := flight.bound, fixed := frame.fixed.symm.trans flight.fixed
    runtime := frame.runtime flight.runtime, source := flight.source, count := flight.count
    originalID := flight.originalID, originalStart := flight.originalStart, originalTime := flight.originalTime
    firstTime := flight.firstTime, rto := flight.rto, deadline := flight.deadline, attempts := flight.attempts
    retried := flight.retried, timedOut := flight.timedOut, nextId := flight.nextId, frontier := flight.frontier
    estimator := flight.estimator, sample := flight.sample, duplicateAcks := flight.duplicateAcks
    valid := frame.valid flight.valid, coherent := frame.recovery_coherent flight.coherent
    prepared := frame.ack_prepared flight.prepared timely, storage := frame.storage_coherent flight.storage
    clocked := frame.clocked flight.runtime flight.clocked }

def Flight.tick (flight : Flight initial sentAt state retries) (frame : Endpoint.ClockFrame state after) :
    Flight initial sentAt after retries := flight.clock frame (flight.ack_time_ready after.now)

theorem Flight.timeout_ready (flight : Flight initial sentAt state retries) (credit : retries < 2)
    (due : flight.entry.lastAt + flight.recovery.rto ≤ flight.recovery.now) :
    Endpoint.TimeoutReady state flight.recovery flight.entry (flight.entry.lastAt + flight.recovery.rto) := by
  refine ⟨flight.runtime, flight.coherent, flight.prepared, flight.source, ?_, flight.deadline,
    due, due, fun _ => ?_, flight.clocked, ?_⟩
  · rw [flight.count]
    exact request.positive
  · simpa only [flight.attempts] using credit
  · rw [flight.count, flight.sendWindow]
    have bound := initial.send_ready.2.2.1
    change (preparedClient initial).core.sent.length + request.bytes.length ≤ (preparedClient initial).sendWindow at bound
    change request.bytes.length ≤ (preparedClient initial).sendWindow
    omega

def initial_flight (initial : Initial report complete request) : Flight initial 0 (sentState initial) 0 := by
  let recovery := Recovery.sent (Recovery.initial complete.certificate.activeSeed.effectiveMSS) request.bytes.length
  let entry : Recovery.Outstanding := ⟨0, 0, request.bytes.length, 0, 0, false⟩
  have guards := CampusTCPRoundGuards.PreparedStart.sent_guards initial.start request.nonempty
    request.mssFits request.receiveFits
  refine {
    recovery, entry, bound := by decide, fixed := rfl, runtime := sent_runtime initial
    source := rfl, count := rfl, originalID := rfl, originalStart := rfl, originalTime := rfl
    firstTime := fun _ => rfl, rto := rfl, deadline := rfl, attempts := rfl, retried := rfl
    timedOut := rfl, nextId := rfl, frontier := by simp only [recovery, Recovery.sent, Recovery.initial, Nat.zero_add]
    estimator := rfl, sample := rfl, duplicateAcks := rfl
    valid := Endpoint.sendState_valid (preparedClient initial) request.bytes.length
      (endpoint_valid initial.start.next.endpoints .client) initial.send_ready
    coherent := guards.recoveryCoherent, prepared := guards.prepared, storage := sent_storage initial
    clocked := Recovery.sent_clocked _ _ (Recovery.initial_clocked _) }

theorem prepared_clock_ready (initial : Initial report complete request) (before : Endpoint.State)
    (frame : Endpoint.ClockFrame (preparedClient initial) before) :
    before.Valid ∧ Endpoint.RecoveryCoherent before ∧ Endpoint.AckPrepared before ∧
      Endpoint.StorageCoherent before ∧ Endpoint.SendReady before request.bytes.length ∧
      Endpoint.outputState before = before := by
  have guarded := CampusTCPRoundGuards.PreparedStart.client_guards initial.start
  have runtime := frame.runtime (prepared_runtime initial)
  have coherent := frame.recovery_coherent guarded.recoveryCoherent
  have timely : Endpoint.AckTimeReady (preparedClient initial) before.now := by
    intro value stored
    rw [prepared_reaction] at stored
    cases stored
    exact AckReaction.initial_within _ _ _ _
  have ready := initial.send_ready
  have size : request.bytes.length ≤ complete.certificate.activeSeed.effectiveMSS := by
    have size := ready.2.2.2.2.1
    simpa only [preparedClient, initial.start.client, Endpoint.writeState, preparedSeed, ackState, recoveryState] using size
  have recoveryReady : Endpoint.recoveryReady before request.bytes.length := by
    rw [Endpoint.recoveryReady, runtime]
    exact ⟨coherent, request.positive, by simpa only [Recovery.flight, Recovery.initial, List.map_nil,
      List.sum_nil, Nat.zero_add] using size, by simpa only [Recovery.flight, Recovery.initial,
      List.map_nil, List.sum_nil, Nat.zero_add] using size⟩
  have sendReady : Endpoint.SendReady before request.bytes.length := by
    refine ⟨ready.1, ?_, ?_, ?_, ?_, ?_, recoveryReady⟩
    · simpa only [frame.pending, preparedClient] using ready.2.1
    · simpa only [frame.core, frame.sendWindow, preparedClient] using ready.2.2.1
    · simpa only [frame.core, preparedClient] using ready.2.2.2.1
    · simpa only [frame.effectiveMSS, preparedClient] using ready.2.2.2.2.1
    · simpa only [frame.ipSendLimit, preparedClient] using ready.2.2.2.2.2.1
  have storage : Endpoint.StorageCoherent (preparedClient initial) := by
    rw [preparedClient, initial.start.client]
    exact CampusTCPRoundLocal.prepared_storage _ complete.certificate.empty.2.2.1
      complete.certificate.receiveStore_initial.1
  refine ⟨frame.valid (endpoint_valid initial.start.next.endpoints .client), coherent,
    frame.ack_prepared guarded.prepared timely, frame.storage_coherent storage, sendReady, ?_⟩
  have core : before.core = complete.certificate.activeSeed.core := by
    rw [frame.core, preparedClient, initial.start.client]
    rfl
  have ack : before.ackReaction = some (reaction (complete := complete)) := frame.ackReaction.trans (prepared_reaction initial)
  have unchanged : (Endpoint.outputState before).ackReaction = before.ackReaction := by
    simp only [Endpoint.outputState, ack, Option.map_some, core, reaction, EstablishedReceive.State.window,
      complete.certificate.empty.2.2.1, List.length_nil, Nat.sub_zero]
    rw [CampusTCPRoundEndpointGeometry.initial_ack_output]
  change { before with ackReaction := (Endpoint.outputState before).ackReaction } = before
  rw [unchanged]

def first_send (initial : Initial report complete request) (before : Endpoint.State)
    (frame : Endpoint.ClockFrame (preparedClient initial) before) :
    Flight initial before.now (Endpoint.sendState before request.bytes.length) 0 := by
  obtain ⟨valid, coherent, ack, storage, ready, output⟩ := prepared_clock_ready initial before frame
  let recovery := Recovery.sent { Recovery.initial complete.certificate.activeSeed.effectiveMSS with now := before.now }
    request.bytes.length
  let entry : Recovery.Outstanding := ⟨0, 0, request.bytes.length, before.now, before.now, false⟩
  have runtime := frame.runtime (prepared_runtime initial)
  have guarded : CampusTCPRoundGuards.Guarded before := ⟨coherent, ack, by rw [runtime]; rfl⟩
  have next := guarded.sendState request.bytes.length ready
  refine {
    recovery, entry, bound := by decide, fixed := ?_, runtime := ?_, source := rfl, count := rfl
    originalID := rfl, originalStart := rfl, originalTime := rfl, firstTime := fun _ => rfl
    rto := rfl, deadline := rfl, attempts := rfl, retried := rfl, timedOut := rfl, nextId := rfl
    frontier := by simp only [recovery, Recovery.sent, Recovery.initial, Nat.zero_add]
    estimator := rfl, sample := rfl, duplicateAcks := rfl
    valid := Endpoint.sendState_valid before request.bytes.length valid ready
    coherent := next.recoveryCoherent, prepared := next.prepared, storage := ?_
    clocked := Recovery.sent_clocked _ _ (Recovery.advance_clocked _ _ (Recovery.initial_clocked _) (Nat.zero_le _)) }
  · let update (state : Endpoint.State) : Endpoint.State := { state with
      recovery := none
      pending := state.pending.drop request.bytes.length
      core := { state.core with
        sent := state.core.sent ++ state.pending.take request.bytes.length
        sendNext := state.core.sendNext.add request.bytes.length } }
    have same := congrArg update frame.fixed
    simpa only [update, withoutRecovery, sentState, Endpoint.sendState, output, prepared_output] using same.symm
  · simp only [Endpoint.sendState, runtime, Option.map_some]
    rfl
  · simp only [Endpoint.sendState, output]
    change Endpoint.StorageCoherent before
    exact storage

theorem first_send_enabled (initial : Initial report complete request) (before : Endpoint.State)
    (frame : Endpoint.ClockFrame (preparedClient initial) before) :
    ∃ packet, Endpoint.send before request.bytes.length true =
      ⟨Endpoint.sendState before request.bytes.length, .accepted (.send request.bytes.length), some packet, [], none⟩ ∧
      Nonempty (Flight initial before.now (Endpoint.send before request.bytes.length true).state 0) := by
  obtain ⟨valid, _, prepared, _, ready, _⟩ := prepared_clock_ready initial before frame
  obtain ⟨packet, accepted⟩ := Endpoint.send_success_enabled before request.bytes.length valid ready prepared
  refine ⟨packet, accepted, ?_⟩
  rw [accepted]
  exact ⟨first_send initial before frame⟩

def Flight.retry (flight : Flight initial sentAt state retries) (credit : retries < 2)
    (due : flight.entry.lastAt + flight.recovery.rto ≤ flight.recovery.now) :
    Flight initial sentAt (Endpoint.retryState state flight.recovery flight.entry) (retries + 1) := by
  let ready := flight.timeout_ready credit due
  refine {
    recovery := Recovery.timeoutState flight.recovery flight.entry []
    entry := { flight.entry with lastAt := flight.recovery.now, retried := true }
    bound := by have bound := flight.bound; omega
    fixed := ?_, runtime := rfl, source := rfl, count := flight.count
    originalID := flight.originalID, originalStart := flight.originalStart, originalTime := flight.originalTime
    firstTime := by omega, rto := ?_, deadline := rfl, attempts := ?_, retried := by simp
    timedOut := by simp only [Recovery.timeoutState, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, ↓reduceIte]
    nextId := flight.nextId, frontier := flight.frontier, estimator := flight.estimator
    sample := flight.sample, duplicateAcks := rfl
    valid := Endpoint.retryState_valid ready flight.valid, coherent := Endpoint.retryState_coherent ready
    prepared := Endpoint.retryState_prepared ready, storage := ?_, clocked := Endpoint.retryState_clocked ready }
  · simpa only [withoutRecovery, Endpoint.retryState, flight.outputState] using flight.fixed
  · change 2 * flight.recovery.rto = 2 ^ (retries + 1) * 1000
    rw [flight.rto, Nat.pow_succ]
    omega
  · change (if flight.recovery.lastTimedOut = some flight.entry.id then flight.recovery.timeoutCount + 1 else 1) = retries + 1
    by_cases first : retries = 0
    · simp only [flight.timedOut, first, ↓reduceIte, reduceCtorEq]
    · simp only [flight.timedOut, first, ↓reduceIte, flight.attempts]
  · simpa only [Endpoint.retryState, flight.outputState, Endpoint.StorageCoherent, Endpoint.State.StorageValid] using flight.storage

theorem Flight.retry_enabled (flight : Flight initial sentAt state retries) (credit : retries < 2)
    (due : flight.entry.lastAt + flight.recovery.rto ≤ flight.recovery.now) :
    ∃ packet, Endpoint.timeout state true =
      ⟨Endpoint.retryState state flight.recovery flight.entry, .accepted (.retry request.bytes.length), some packet, [], none⟩ ∧
      Endpoint.emitAt state state.core.sendUna request.bytes = .ok packet ∧
      Nonempty (Flight initial sentAt (Endpoint.timeout state true).state (retries + 1)) := by
  obtain ⟨packet, accepted, encoded⟩ := Endpoint.timeout_success_enabled state flight.recovery flight.entry
    (flight.entry.lastAt + flight.recovery.rto) flight.valid (flight.timeout_ready credit due)
  have payload : state.core.sent.take flight.entry.count = request.bytes := by
    rw [flight.sent, flight.count, List.take_length]
  refine ⟨packet, by simpa only [flight.count] using accepted, by simpa only [payload] using encoded, ?_⟩
  rw [accepted]
  exact ⟨flight.retry credit due⟩

theorem Flight.full_ack_ready (flight : Flight initial sentAt state retries) (packet : EstablishedReceive.Input)
    (tuple : packet.packet.header = complete.certificate.activeSeed.core.inbound)
    (controls : EstablishedReceive.control packet.packet.segment = none)
    (ack : Flags.ack packet.packet.segment.flags = true)
    (sequence : packet.packet.segment.sequence = input.passive.iss.add 1)
    (acknowledgment : packet.packet.segment.acknowledgment = (input.active.iss.add 1).add request.bytes.length)
    (empty : packet.packet.segment.payload = []) :
    ∃ reaction, CampusTCPDeliveryEnabled.FullAckReady state packet flight.recovery reaction := by
  obtain ⟨_, reaction, ready⟩ := CampusTCPRoundEndpointGeometry.client_ready initial.start packet
    request.nonempty request.mssFits request.receiveFits tuple controls ack sequence acknowledgment empty
  have ackRuntime : state.ackReaction = (sentState initial).ackReaction := by
    simpa only [withoutRecovery] using congrArg Endpoint.State.ackReaction flight.fixed
  refine ⟨reaction, flight.coherent, flight.prepared, flight.storage, flight.runtime,
    ackRuntime.trans ready.ackRuntime, flight.positive, ?_, ?_, ?_, controls, ack, ?_, empty, ?_⟩
  · rw [flight.sent]
    exact request.positive
  · rw [flight.receiveStore]
    exact ready.emptyHeld
  · rw [flight.core]
    exact ready.tuple
  · rw [flight.core]
    exact ready.sequence
  · simpa only [Endpoint.inOrderCount, flight.core, sentState, preparedClient] using ready.covers

theorem Flight.karn (flight : Flight initial sentAt state retries) (retried : 0 < retries) :
    Recovery.sample flight.recovery request.bytes.length = none := by
  simp only [Recovery.sample, flight.source, Recovery.retired, Nat.ne_of_gt request.positive, ite_false,
    flight.count, Nat.le_refl, ite_true, List.any_cons, List.any_nil, Bool.or_false, flight.retried,
    decide_eq_true retried]

theorem Flight.full_ack_retirement (flight : Flight initial sentAt state retries) :
    (Recovery.acknowledgeState flight.recovery request.bytes.length).outstanding = [] ∧
      (Recovery.acknowledgeState flight.recovery request.bytes.length).deadline = none ∧
      (Recovery.acknowledgeState flight.recovery request.bytes.length).lastTimedOut = none ∧
      (Recovery.acknowledgeState flight.recovery request.bytes.length).timeoutCount = 0 := by
  have result := Recovery.acknowledgeState_full flight.recovery flight.positive (by rw [flight.flight_count]; exact request.positive)
  simpa only [flight.flight_count] using result

theorem Flight.full_ack_karn (flight : Flight initial sentAt state retries) (retried : 0 < retries) :
    (Recovery.acknowledgeState flight.recovery request.bytes.length).rto = flight.recovery.rto ∧
      (Recovery.acknowledgeState flight.recovery request.bytes.length).estimator = flight.recovery.estimator ∧
      (Recovery.acknowledgeState flight.recovery request.bytes.length).lastSample = flight.recovery.lastSample := by
  simp only [Recovery.acknowledgeState, Nat.ne_of_gt request.positive, ite_false, flight.karn retried,
    Option.map_none, and_self]

theorem Flight.receive_full_ack (flight : Flight initial sentAt state retries) (packet : EstablishedReceive.Input)
    (tuple : packet.packet.header = complete.certificate.activeSeed.core.inbound)
    (controls : EstablishedReceive.control packet.packet.segment = none)
    (ack : Flags.ack packet.packet.segment.flags = true)
    (sequence : packet.packet.segment.sequence = input.passive.iss.add 1)
    (acknowledgment : packet.packet.segment.acknowledgment = (input.active.iss.add 1).add request.bytes.length)
    (empty : packet.packet.segment.payload = []) :
    ∃ after recovered,
      Endpoint.receive state packet = ⟨after, .accepted (.receive request.bytes.length 0), none, [], none⟩ ∧
      after.recovery = some recovered ∧ after.core.sent = [] ∧ after.core.sendUna = state.core.sendNext ∧
      after.Valid ∧ Endpoint.AckPrepared after ∧ Endpoint.RecoveryCoherent after ∧ Endpoint.StorageCoherent after ∧
      recovered.outstanding = [] ∧ recovered.deadline = none ∧ recovered.lastTimedOut = none ∧ recovered.timeoutCount = 0 ∧
      (0 < retries → recovered.rto = flight.recovery.rto ∧
        recovered.estimator = none ∧ recovered.lastSample = none) := by
  obtain ⟨reaction, ready⟩ := flight.full_ack_ready packet tuple controls ack sequence acknowledgment empty
  obtain ⟨acknowledged, after, accepted, afterEq, actual, _, _, retired, cursor, valid, prepared, coherent,
      storage, cleared, deadline, attempts⟩ := Endpoint.receive_empty_full_ack_coherent state packet flight.recovery
    reaction flight.valid ready.recoveryCoherent ready.ackPrepared ready.storageCoherent ready.runtime ready.ackRuntime
    ready.positive ready.flight ready.emptyHeld ready.tuple ready.controls ready.acknowledgment ready.sequence ready.empty ready.covers
  have acknowledgedEq : acknowledged = Recovery.acknowledgeState flight.recovery request.bytes.length := by
    have evaluated := Recovery.acknowledge_of_bounded flight.recovery (Recovery.flight flight.recovery) (Nat.le_refl _)
    simpa only [flight.flight_count] using Except.ok.inj (accepted.symm.trans evaluated)
  have runtime : after.recovery = some { acknowledged with duplicateAcks := 0 } := by
    simp only [afterEq, Endpoint.inOrderReceivedWith, Endpoint.windowState_recovery]
  refine ⟨after, { acknowledged with duplicateAcks := 0 }, ?_, runtime, retired, cursor,
    valid, prepared, coherent, storage, cleared, deadline, ?_, attempts, ?_⟩
  · simpa only [flight.sent] using actual
  · change acknowledged.lastTimedOut = none
    rw [acknowledgedEq]
    exact flight.full_ack_retirement.2.2.1
  · intro retried
    change acknowledged.rto = flight.recovery.rto ∧ acknowledged.estimator = none ∧ acknowledged.lastSample = none
    rw [acknowledgedEq]
    simpa only [flight.estimator, flight.sample] using flight.full_ack_karn retried

end Netlib.Check.CampusTCPRecoveryRoundSender
