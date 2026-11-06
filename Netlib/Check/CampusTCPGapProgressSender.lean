import Netlib.Check.CampusTCPGapProgressStart
import Netlib.Protocol.TCP.EndpointClockEnabled

/-!
# Current sender records for a held-gap task

The upper original record remains fixed across head retries.
ACK output can update the sender's historical ACK reaction.
-/

namespace Netlib.Check.CampusTCPGapProgressSender

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPGapProgressStart (Original SenderStart)

variable {input : Input} {complete : H.Completed input.active input.passive}
  {cut : Cut input complete} {actor : Actor} {lower upper : List UInt8}
  {first : Original cut actor lower} {second : Original cut actor upper}

def withoutRuntime (state : Endpoint.State) : Endpoint.State := { state with recovery := none, ackReaction := none }

theorem original_positive (original : Original cut actor bytes) : 0 < bytes.length := by
  cases original.attempt.origin with
  | send count policy event accepted actual =>
    have same := ApplicationTrace.Event.send.inj (event.symm.trans original.event)
    have selected : (Endpoint.send original.attempt.step.before count policy).decision = .accepted (.send count) := by
      simpa only [original.attempt.step.computed, event, ApplicationTrace.evaluate] using accepted
    have positive := (Endpoint.send_accepted _ _ _ selected).2.2.1.1
    rw [same.1] at positive
    exact positive
  | ack policy event accepted actual => rw [original.event] at event; cases event
  | dispatchAck policy event accepted actual => rw [original.event] at event; cases event
  | retry count policy event accepted actual => rw [original.event] at event; cases event

structure Flight (start : SenderStart cut actor lower upper first second) (state : Endpoint.State) (retries : Nat) where
  recovery : Recovery.State
  reaction : AckReaction.State
  head : Recovery.Outstanding
  bound : retries ≤ 2
  fixed : withoutRuntime state = withoutRuntime (endpoint cut.endpoints actor)
  runtime : state.recovery = some recovery
  ackRuntime : state.ackReaction = some reaction
  ackEmpty : reaction.work.pending = []
  reactionOrigin : reaction.origin = start.reaction.origin
  reactionMSS : reaction.rmss = start.reaction.rmss
  reactionFrontier : reaction.advertisement.frontier = start.reaction.advertisement.frontier
  source : recovery.outstanding = [head, start.tail]
  headFixed : { head with lastAt := start.head.lastAt, retried := start.head.retried } = start.head
  firstTime : retries = 0 → head.lastAt = start.head.lastAt
  rto : recovery.rto = 2 ^ retries * 1000
  deadline : recovery.deadline = some (head.lastAt + recovery.rto)
  attempts : recovery.timeoutCount = retries
  retried : head.retried = decide (0 < retries)
  timedOut : recovery.lastTimedOut = if retries = 0 then none else some head.id
  nextID : recovery.nextId = start.recovery.nextId
  frontier : recovery.frontier = start.recovery.frontier
  estimator : recovery.estimator = start.recovery.estimator
  sample : recovery.lastSample = start.recovery.lastSample
  duplicate : recovery.duplicateAcks = if retries = 0 then 1 else 0
  valid : state.Valid
  coherent : Endpoint.RecoveryCoherent state
  prepared : Endpoint.AckPrepared state
  storage : Endpoint.StorageCoherent state
  clocked : recovery.Clocked
  positive : recovery.Positive
  monotone : (endpoint cut.endpoints actor).now ≤ state.now

variable {start : SenderStart cut actor lower upper first second} {state after : Endpoint.State} {retries : Nat}

theorem Flight.core (flight : Flight start state retries) : state.core = (endpoint cut.endpoints actor).core := by
  simpa only [withoutRuntime] using congrArg Endpoint.State.core flight.fixed

theorem Flight.pending (flight : Flight start state retries) : state.pending = [] :=
  (congrArg Endpoint.State.pending flight.fixed).trans start.pending

theorem Flight.sendWindow (flight : Flight start state retries) : state.sendWindow = (endpoint cut.endpoints actor).sendWindow := by
  simpa only [withoutRuntime] using congrArg Endpoint.State.sendWindow flight.fixed

theorem Flight.receiveStore (flight : Flight start state retries) : state.receiveStore = (endpoint cut.endpoints actor).receiveStore := by
  simpa only [withoutRuntime] using congrArg Endpoint.State.receiveStore flight.fixed

theorem Flight.effectiveMSS (flight : Flight start state retries) : state.effectiveMSS = (endpoint cut.endpoints actor).effectiveMSS := by
  simpa only [withoutRuntime] using congrArg Endpoint.State.effectiveMSS flight.fixed

theorem Flight.ipSendLimit (flight : Flight start state retries) : state.ipSendLimit = (endpoint cut.endpoints actor).ipSendLimit := by
  simpa only [withoutRuntime] using congrArg Endpoint.State.ipSendLimit flight.fixed

theorem Flight.localReceiveMSS (flight : Flight start state retries) : state.localReceiveMSS = (endpoint cut.endpoints actor).localReceiveMSS := by
  simpa only [withoutRuntime] using congrArg Endpoint.State.localReceiveMSS flight.fixed

theorem Flight.sendWL1 (flight : Flight start state retries) : state.sendWL1 = (endpoint cut.endpoints actor).sendWL1 := by
  simpa only [withoutRuntime] using congrArg Endpoint.State.sendWL1 flight.fixed

theorem Flight.sendWL2 (flight : Flight start state retries) : state.sendWL2 = (endpoint cut.endpoints actor).sendWL2 := by
  simpa only [withoutRuntime] using congrArg Endpoint.State.sendWL2 flight.fixed

theorem Flight.lastAckWindow (flight : Flight start state retries) : state.lastAckWindow = (endpoint cut.endpoints actor).lastAckWindow := by
  simpa only [withoutRuntime] using congrArg Endpoint.State.lastAckWindow flight.fixed

theorem Flight.emptyHeld (flight : Flight start state retries) : state.receiveStore.held = [] := by
  rw [flight.receiveStore]
  exact start.emptyHeld

theorem Flight.sent (flight : Flight start state retries) : state.core.sent = lower ++ upper := by rw [flight.core]; exact start.sent

theorem Flight.headCount (flight : Flight start state retries) : flight.head.count = lower.length :=
  (congrArg Recovery.Outstanding.count flight.headFixed).trans start.headCount

theorem Flight.headID (flight : Flight start state retries) : flight.head.id = 0 :=
  (congrArg Recovery.Outstanding.id flight.headFixed).trans start.headID

theorem Flight.headStart (flight : Flight start state retries) : flight.head.start = 0 :=
  (congrArg Recovery.Outstanding.start flight.headFixed).trans start.headStart

theorem Flight.headTime (flight : Flight start state retries) : flight.head.sentAt = first.attempt.step.before.now :=
  (congrArg Recovery.Outstanding.sentAt flight.headFixed).trans start.headTime

theorem Flight.headSequence (flight : Flight start state retries) : state.core.sendUna = first.attempt.output.packet.segment.sequence := by
  rw [flight.core]; exact start.headSequence

theorem Flight.sendNext (flight : Flight start state retries) :
    state.core.sendNext = first.attempt.output.packet.segment.sequence.add (lower.length + upper.length) := by
  have span := flight.valid.1.2.2.2.2.1
  rw [flight.sent, List.length_append, flight.headSequence] at span
  exact span.symm

theorem Flight.flight_count (flight : Flight start state retries) : Recovery.flight flight.recovery = lower.length + upper.length := by
  simp only [Recovery.flight, flight.source, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero, flight.headCount, start.tailCount]

theorem Flight.payload (flight : Flight start state retries) : state.core.sent.take flight.head.count = lower := by
  rw [flight.sent, flight.headCount, List.take_left]

theorem Flight.ack_time_ready (flight : Flight start state retries) (millis : Nat) : Endpoint.AckTimeReady state millis := by
  intro reaction stored
  rw [flight.ackRuntime] at stored
  cases stored
  simp only [AckReaction.State.WithinTime, flight.ackEmpty, List.not_mem_nil, false_implies, implies_true]

def initial_flight (start : SenderStart cut actor lower upper first second) : Flight start (endpoint cut.endpoints actor) 0 where
  recovery := start.recovery
  reaction := start.reaction
  head := start.head
  bound := by decide
  fixed := rfl
  runtime := start.runtime
  ackRuntime := start.ackRuntime
  ackEmpty := start.ackEmpty
  reactionOrigin := rfl
  reactionMSS := rfl
  reactionFrontier := rfl
  source := start.ledger
  headFixed := rfl
  firstTime := fun _ => rfl
  rto := start.rto
  deadline := start.deadline
  attempts := start.timeoutCount
  retried := start.headRetried
  timedOut := start.timedOut
  nextID := rfl
  frontier := rfl
  estimator := rfl
  sample := rfl
  duplicate := start.duplicate
  valid := start.valid
  coherent := start.coherent
  prepared := start.prepared
  storage := start.storage
  clocked := start.clocked
  positive := by
    intro entry member
    simp only [start.ledger, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with head | tail
    · rw [head, start.headCount]; exact original_positive first
    · rw [tail, start.tailCount]; exact original_positive second
  monotone := Nat.le_refl _

def Flight.clock (flight : Flight start state retries) (frame : Endpoint.ClockFrame state after) : Flight start after retries := by
  refine {
    recovery := { flight.recovery with now := after.now }, reaction := flight.reaction, head := flight.head
    bound := flight.bound, fixed := ?_, runtime := frame.runtime flight.runtime
    ackRuntime := frame.ackReaction.trans flight.ackRuntime, ackEmpty := flight.ackEmpty
    reactionOrigin := flight.reactionOrigin, reactionMSS := flight.reactionMSS, reactionFrontier := flight.reactionFrontier
    source := flight.source, headFixed := flight.headFixed, firstTime := flight.firstTime
    rto := flight.rto, deadline := flight.deadline, attempts := flight.attempts, retried := flight.retried
    timedOut := flight.timedOut, nextID := flight.nextID, frontier := flight.frontier, estimator := flight.estimator
    sample := flight.sample, duplicate := flight.duplicate, valid := frame.valid flight.valid
    coherent := frame.recovery_coherent flight.coherent
    prepared := frame.ack_prepared flight.prepared (flight.ack_time_ready after.now)
    storage := frame.storage_coherent flight.storage, clocked := frame.clocked flight.runtime flight.clocked
    positive := frame.positive flight.runtime flight.positive
    monotone := Nat.le_trans flight.monotone frame.monotone }
  have fixed := congrArg (fun old : Endpoint.State => { old with ackReaction := none }) frame.fixed.symm
  exact fixed.trans flight.fixed

theorem Flight.timeout_ready (flight : Flight start state retries) (credit : retries < 2)
    (due : flight.head.lastAt + flight.recovery.rto ≤ flight.recovery.now) :
    Endpoint.HeadTimeoutReady state flight.recovery flight.head [start.tail] (flight.head.lastAt + flight.recovery.rto) := by
  refine ⟨flight.runtime, flight.coherent, flight.prepared, flight.source, flight.positive, flight.deadline,
    due, due, fun _ => ?_, flight.clocked, ?_⟩
  · rw [flight.attempts]; exact credit
  · rw [flight.headCount, flight.sendWindow]; exact start.window

def Flight.retry (flight : Flight start state retries) (credit : retries < 2)
    (due : flight.head.lastAt + flight.recovery.rto ≤ flight.recovery.now) :
    Flight start (Endpoint.headRetryState state flight.recovery flight.head [start.tail]) (retries + 1) := by
  let ready := flight.timeout_ready credit due
  let reaction := AckReaction.outputState flight.reaction state.now state.core.receiveNext state.core.capacity state.core.window state.effectiveMSS
  refine {
    recovery := Recovery.timeoutState flight.recovery flight.head [start.tail]
    reaction, head := { flight.head with lastAt := flight.recovery.now, retried := true }
    bound := by have bound := flight.bound; omega
    fixed := ?_, runtime := rfl, ackRuntime := ?_, ackEmpty := AckReaction.outputState_pending _ _ _ _ _ _
    reactionOrigin := flight.reactionOrigin, reactionMSS := flight.reactionMSS
    reactionFrontier := flight.reactionFrontier, source := rfl, headFixed := flight.headFixed
    firstTime := by omega, rto := ?_, deadline := rfl, attempts := ?_, retried := by simp
    timedOut := by simp only [Recovery.timeoutState, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
    nextID := flight.nextID, frontier := flight.frontier, estimator := flight.estimator, sample := flight.sample
    duplicate := by simp only [Recovery.timeoutState, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
    valid := Endpoint.headRetryState_valid ready flight.valid, coherent := Endpoint.headRetryState_coherent ready
    prepared := Endpoint.headRetryState_prepared ready, storage := Endpoint.headRetryState_storage_coherent ready flight.storage
    clocked := Endpoint.headRetryState_clocked ready, positive := Endpoint.headRetryState_positive ready
    monotone := ?_ }
  · exact flight.fixed
  · simp only [Endpoint.headRetryState, Endpoint.outputState, flight.ackRuntime, Option.map_some]
    rfl
  · change 2 * flight.recovery.rto = 2 ^ (retries + 1) * 1000
    rw [flight.rto, Nat.pow_succ]
    omega
  · change (if flight.recovery.lastTimedOut = some flight.head.id then flight.recovery.timeoutCount + 1 else 1) = retries + 1
    by_cases first : retries = 0
    · simp only [flight.timedOut, first, ite_true, reduceCtorEq, ite_false]
    · simp only [flight.timedOut, first, ite_false, ite_true, flight.attempts]
  · simpa only [Endpoint.headRetryState, Endpoint.State.now, flight.runtime, Option.map_some, Option.getD_some,
      Recovery.timeoutState] using flight.monotone

theorem Flight.retry_enabled (flight : Flight start state retries) (credit : retries < 2)
    (due : flight.head.lastAt + flight.recovery.rto ≤ flight.recovery.now) :
    ∃ packet, Endpoint.timeout state true =
      ⟨Endpoint.headRetryState state flight.recovery flight.head [start.tail],
        .accepted (.retry lower.length), some packet, [], none⟩ ∧
      Endpoint.emitAt state state.core.sendUna lower = .ok packet ∧
      Nonempty (Flight start (Endpoint.timeout state true).state (retries + 1)) := by
  obtain ⟨packet, accepted, encoded⟩ := Endpoint.head_timeout_success_enabled state flight.recovery flight.head [start.tail]
    (flight.head.lastAt + flight.recovery.rto) flight.valid (flight.timeout_ready credit due)
  refine ⟨packet, by simpa only [flight.headCount] using accepted, ?_, ?_⟩
  · simpa only [flight.payload] using encoded
  · rw [accepted]
    exact ⟨flight.retry credit due⟩

theorem Flight.full_ack_ready (flight : Flight start state retries) (packet : EstablishedReceive.Input)
    (tuple : packet.packet.header = (endpoint cut.endpoints actor).core.inbound)
    (controls : EstablishedReceive.control packet.packet.segment = none)
    (ack : Flags.ack packet.packet.segment.flags = true)
    (sequence : packet.packet.segment.sequence = (endpoint cut.endpoints actor).core.receiveNext)
    (acknowledgment : packet.packet.segment.acknowledgment = (endpoint cut.endpoints actor).core.sendNext)
    (empty : packet.packet.segment.payload = []) :
    CampusTCPDeliveryEnabled.FullAckReady state packet flight.recovery flight.reaction := by
  refine ⟨flight.coherent, flight.prepared, flight.storage, flight.runtime, flight.ackRuntime, flight.positive,
    ?_, ?_, ?_, controls, ack, ?_, empty, ?_⟩
  · rw [flight.sent, List.length_append]
    have lowerPositive := original_positive first
    omega
  · exact flight.emptyHeld
  · rw [flight.core]; exact tuple
  · rw [flight.core]; exact sequence
  · apply Endpoint.inOrderCount_of_full_ack state packet flight.valid
    rw [flight.core]; exact acknowledgment

theorem Flight.full_ack_retirement (flight : Flight start state retries) :
    let after := Recovery.acknowledgeState flight.recovery (lower.length + upper.length)
    after.outstanding = [] ∧ after.deadline = none ∧ after.lastTimedOut = none ∧ after.timeoutCount = 0 := by
  have nonempty : 0 < Recovery.flight flight.recovery := by
    rw [flight.flight_count]
    have lowerPositive := original_positive first
    omega
  simpa only [flight.flight_count] using Recovery.acknowledgeState_full flight.recovery flight.positive nonempty

theorem Flight.karn (flight : Flight start state retries) (retried : 0 < retries) :
    Recovery.sample flight.recovery (lower.length + upper.length) = none := by
  have headRetried : flight.head.retried = true := by rw [flight.retried]; exact decide_eq_true retried
  simpa only [flight.flight_count] using
    (Endpoint.full_ack_of_retried_head flight.recovery flight.head [start.tail] flight.source flight.positive headRetried).1

theorem Flight.full_ack_exact (flight : Flight start state retries) (retried : 0 < retries) :
    Recovery.acknowledgeState flight.recovery (lower.length + upper.length) =
      { flight.recovery with
        outstanding := [], deadline := none, lastTimedOut := none
        timeoutCount := 0, duplicateAcks := 0 } := by
  have headRetried : flight.head.retried = true := by rw [flight.retried]; exact decide_eq_true retried
  simpa only [flight.flight_count] using
    (Endpoint.full_ack_of_retried_head flight.recovery flight.head [start.tail] flight.source flight.positive headRetried).2

theorem Flight.full_ack_karn (flight : Flight start state retries) (retried : 0 < retries) :
    let after := Recovery.acknowledgeState flight.recovery (lower.length + upper.length)
    after.rto = 2 ^ retries * 1000 ∧ after.estimator = start.recovery.estimator ∧ after.lastSample = start.recovery.lastSample := by
  simp only [flight.full_ack_exact retried, flight.rto, flight.estimator, flight.sample, and_self]

theorem Flight.receive_full_ack (flight : Flight start state retries) (packet : EstablishedReceive.Input)
    (tuple : packet.packet.header = (endpoint cut.endpoints actor).core.inbound)
    (controls : EstablishedReceive.control packet.packet.segment = none)
    (ack : Flags.ack packet.packet.segment.flags = true)
    (sequence : packet.packet.segment.sequence = (endpoint cut.endpoints actor).core.receiveNext)
    (acknowledgment : packet.packet.segment.acknowledgment = (endpoint cut.endpoints actor).core.sendNext)
    (empty : packet.packet.segment.payload = []) :
    ∃ after recovered,
      Endpoint.receive state packet = ⟨after, .accepted (.receive (lower.length + upper.length) 0), none, [], none⟩ ∧
      after.recovery = some recovered ∧ after.core.sent = [] ∧ after.core.sendUna = state.core.sendNext ∧
      after.Valid ∧ Endpoint.AckPrepared after ∧ Endpoint.RecoveryCoherent after ∧ Endpoint.StorageCoherent after ∧
      recovered.outstanding = [] ∧ recovered.deadline = none ∧ recovered.lastTimedOut = none ∧ recovered.timeoutCount = 0 ∧
      recovered.nextId = start.recovery.nextId ∧ recovered.frontier = start.recovery.frontier ∧
      recovered.now = flight.recovery.now ∧
      (0 < retries → recovered.rto = 2 ^ retries * 1000 ∧
        recovered.estimator = start.recovery.estimator ∧ recovered.lastSample = start.recovery.lastSample) := by
  have ready := flight.full_ack_ready packet tuple controls ack sequence acknowledgment empty
  obtain ⟨acknowledged, after, accepted, afterEq, actual, _, _, sent, cursor, valid, prepared, coherent,
      storage, cleared, deadline, attempts⟩ := Endpoint.receive_empty_full_ack_coherent state packet flight.recovery
    flight.reaction flight.valid ready.recoveryCoherent ready.ackPrepared ready.storageCoherent ready.runtime ready.ackRuntime
    ready.positive ready.flight ready.emptyHeld ready.tuple ready.controls ready.acknowledgment ready.sequence ready.empty ready.covers
  have acknowledgedEq : acknowledged = Recovery.acknowledgeState flight.recovery (lower.length + upper.length) := by
    simpa only [flight.flight_count] using (Recovery.acknowledge_fields _ _ _ accepted).2
  have runtime : after.recovery = some { acknowledged with duplicateAcks := 0 } := by
    simp only [afterEq, Endpoint.inOrderReceivedWith, Endpoint.windowState_recovery]
  have nonzero : lower.length + upper.length ≠ 0 := by have positive := original_positive first; omega
  refine ⟨after, { acknowledged with duplicateAcks := 0 }, ?_, runtime, sent, cursor, valid, prepared, coherent,
    storage, cleared, deadline, ?_, attempts, ?_, ?_, ?_, ?_⟩
  · simpa only [flight.sent, List.length_append] using actual
  · rw [acknowledgedEq]
    exact flight.full_ack_retirement.2.2.1
  · rw [acknowledgedEq]
    simp only [Recovery.acknowledgeState, nonzero, ite_false, flight.nextID]
  · rw [acknowledgedEq]
    simp only [Recovery.acknowledgeState, nonzero, ite_false, flight.frontier]
  · rw [acknowledgedEq]
    exact Recovery.acknowledgeState_now _ _
  · intro retried
    rw [acknowledgedEq]
    exact flight.full_ack_karn retried

end Netlib.Check.CampusTCPGapProgressSender
