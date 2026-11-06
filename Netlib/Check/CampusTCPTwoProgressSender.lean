import Netlib.Check.CampusTCPTwoProgressStart
import Netlib.Protocol.TCP.EndpointPartialAckEnabled
import Netlib.Protocol.TCP.EndpointZeroAckEnabled
import Netlib.Protocol.TCP.EndpointClockEnabled
import Netlib.Protocol.TCP.EndpointWindowFloor

/-!
# Current sender state for two original records

Original records keep their actual local send operations.
Global timeout counts remain separate from the current head's retry count.
-/

namespace Netlib.Check.CampusTCPTwoProgressSender

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart (TwoWriteInitial)

variable {input : Input} {complete : H.Completed input.active input.passive}
  {cut : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}

def source (_initial : TwoWriteInitial cut sender gateway lower upper) : Endpoint.State :=
  endpoint cut.endpoints sender

inductive Part where
  | lower | upper
  deriving DecidableEq

def Part.bytes (lower upper : List UInt8) : Part → List UInt8
  | .lower => lower
  | .upper => upper

def Part.offset (lower : List UInt8) : Part → Nat
  | .lower => 0
  | .upper => lower.length

def Part.index : Part → Nat
  | .lower => 0
  | .upper => 1

structure Original (initial : TwoWriteInitial cut sender gateway lower upper) (part : Part) where
  operation : ApplicationTrace.Step
  event : operation.event = .send (part.bytes lower upper).length true
  accepted : operation.result.decision = .accepted (.send (part.bytes lower upper).length)
  packet : EstablishedReceive.Input
  origin : ApplicationTrace.OutputOrigin operation packet
  encoded : Endpoint.emit operation.before (part.bytes lower upper) = .ok packet
  payload : packet.packet.segment.payload = part.bytes lower upper
  sequence : packet.packet.segment.sequence = (source initial).core.sendNext.add (part.offset lower)

variable {initial : TwoWriteInitial cut sender gateway lower upper} {part : Part}

def Original.entry (original : Original initial part) : Recovery.Outstanding :=
  ⟨initial.senderState.idle.recovery.nextId + part.index,
    initial.senderState.idle.recovery.frontier + part.offset lower,
    (part.bytes lower upper).length, original.operation.before.now, original.operation.before.now, false⟩

inductive Stage (initial : TwoWriteInitial cut sender gateway lower upper) where
  | written
  | lower (first : Original initial .lower)
  | both (first : Original initial .lower) (second : Original initial .upper) (head : Recovery.Outstanding)
  | tail (first : Original initial .lower) (second : Original initial .upper) (head : Recovery.Outstanding)
  | retired (first : Original initial .lower) (second : Original initial .upper)

def Stage.pending : Stage initial → List UInt8
  | .written => lower ++ upper
  | .lower _ => upper
  | _ => []

def Stage.sent : Stage initial → List UInt8
  | .lower _ => lower
  | .both .. => lower ++ upper
  | .tail .. => upper
  | _ => []

def Stage.issued : Stage initial → Nat
  | .written => 0
  | .lower _ => lower.length
  | _ => lower.length + upper.length

def Stage.retiredBytes : Stage initial → Nat
  | .tail .. => lower.length
  | .retired .. => lower.length + upper.length
  | _ => 0

def Stage.outputCount : Stage initial → Nat
  | .written => 0
  | .lower _ => 1
  | _ => 2

def Stage.ledger : Stage initial → List Recovery.Outstanding
  | .written | .retired .. => []
  | .lower first => [first.entry]
  | .both _ second head => [head, second.entry]
  | .tail _ _ head => [head]

def HeadFixed (original : Recovery.Outstanding) (head : Recovery.Outstanding) : Prop :=
  { head with lastAt := original.lastAt, retried := original.retried } = original

def Stage.HeadValid : Stage initial → Prop
  | .both first _ head => HeadFixed first.entry head
  | .tail _ second head => HeadFixed second.entry head
  | _ => True

def Stage.TimedHead : Stage initial → Option Nat → Prop
  | .both first _ _, timed => timed = none ∨ timed = some first.entry.id
  | .tail first second _, timed => timed = none ∨ timed = some first.entry.id ∨ timed = some second.entry.id
  | _, timed => timed = none

def Stage.preparing : Stage initial → Bool
  | .written | .lower _ => true
  | _ => false

def Stage.hasOutput : Stage initial → Bool
  | .written => false
  | _ => true

def coreAt (initial : TwoWriteInitial cut sender gateway lower upper) (stage : Stage initial) : EstablishedReceive.State :=
  { (source initial).core with
    sent := stage.sent
    sendUna := (source initial).core.sendUna.add stage.retiredBytes
    sendNext := (source initial).core.sendNext.add stage.issued }

structure Parameters where
  pendingLimit : Nat
  effectiveMSS : Nat
  ipSendLimit : Nat
  localReceiveMSS : MSS.Offer
  receiveStore : ReceiveReassembly.Store

def parameters (state : Endpoint.State) : Parameters :=
  ⟨state.pendingLimit, state.effectiveMSS, state.ipSendLimit, state.localReceiveMSS, state.receiveStore⟩

structure Flight (initial : TwoWriteInitial cut sender gateway lower upper) (state : Endpoint.State)
    (stage : Stage initial) (timeouts : Nat) where
  recovery : Recovery.State
  reaction : AckReaction.State
  runtime : state.recovery = some recovery
  ackRuntime : state.ackReaction = some reaction
  fixed : parameters state = parameters (source initial)
  core : state.core = coreAt initial stage
  pending : state.pending = stage.pending
  ledger : recovery.outstanding = stage.ledger
  headFixed : stage.HeadValid
  nextID : recovery.nextId = initial.senderState.idle.recovery.nextId + stage.outputCount
  frontier : recovery.frontier = initial.senderState.idle.recovery.frontier + stage.issued
  counter : recovery.timeoutCount ≤ timeouts
  timedHead : stage.TimedHead recovery.lastTimedOut
  retried : ∀ entry ∈ recovery.outstanding, entry.retried = true → 0 < timeouts
  quiet : stage.hasOutput = true → reaction.work.pending = []
  advertised : Endpoint.offeredWindow (source initial) ≤ Endpoint.offeredWindow state
  originalWindow : stage.preparing = true → state.sendWindow = (source initial).sendWindow
  headWindow : ∀ head, stage.ledger.head? = some head → head.count ≤ state.sendWindow
  armed : stage.ledger ≠ [] → recovery.deadline.isSome = true
  idle : stage.ledger = [] → recovery.deadline = none ∧ recovery.lastTimedOut = none ∧ recovery.timeoutCount = 0
  valid : state.Valid
  coherent : Endpoint.RecoveryCoherent state
  prepared : Endpoint.AckPrepared state
  storage : Endpoint.StorageCoherent state
  clocked : recovery.Clocked
  positive : recovery.Positive
  monotone : (source initial).now ≤ state.now

variable {state after : Endpoint.State}
  {stage : Stage initial} {timeouts : Nat}

theorem Flight.receiveStore (flight : Flight initial state stage timeouts) :
    state.receiveStore = (source initial).receiveStore := congrArg Parameters.receiveStore flight.fixed

theorem Flight.effectiveMSS (flight : Flight initial state stage timeouts) :
    state.effectiveMSS = (source initial).effectiveMSS := congrArg Parameters.effectiveMSS flight.fixed

theorem Flight.ipSendLimit (flight : Flight initial state stage timeouts) :
    state.ipSendLimit = (source initial).ipSendLimit := congrArg Parameters.ipSendLimit flight.fixed

theorem Flight.localReceiveMSS (flight : Flight initial state stage timeouts) :
    state.localReceiveMSS = (source initial).localReceiveMSS := congrArg Parameters.localReceiveMSS flight.fixed

theorem Flight.inbound (flight : Flight initial state stage timeouts) : state.core.inbound = (source initial).core.inbound := by
  rw [flight.core]
  rfl

theorem Flight.receiveNext (flight : Flight initial state stage timeouts) :
    state.core.receiveNext = (source initial).core.receiveNext := by
  rw [flight.core]
  rfl

theorem Flight.received (flight : Flight initial state stage timeouts) :
    state.core.received = (source initial).core.received := by
  rw [flight.core]
  rfl

theorem Flight.capacity (flight : Flight initial state stage timeouts) : state.core.capacity = (source initial).core.capacity := by
  rw [flight.core]
  rfl

theorem Flight.sent (flight : Flight initial state stage timeouts) : state.core.sent = stage.sent := by
  rw [flight.core]
  rfl

theorem Flight.sendUna (flight : Flight initial state stage timeouts) :
    state.core.sendUna = (source initial).core.sendUna.add stage.retiredBytes := by
  rw [flight.core]
  rfl

theorem Flight.sendNext (flight : Flight initial state stage timeouts) :
    state.core.sendNext = (source initial).core.sendNext.add stage.issued := by
  rw [flight.core]
  rfl

theorem Flight.recovery_valid (flight : Flight initial state stage timeouts) : flight.recovery.Valid := by
  have fields := flight.coherent
  rw [Endpoint.RecoveryCoherent, flight.runtime] at fields
  exact fields.1

theorem Flight.smss (flight : Flight initial state stage timeouts) : flight.recovery.smss = state.effectiveMSS := by
  have fields := flight.coherent
  rw [Endpoint.RecoveryCoherent, flight.runtime] at fields
  exact fields.2.1

theorem Flight.flight_count (flight : Flight initial state stage timeouts) : Recovery.flight flight.recovery = stage.sent.length := by
  have fields := flight.coherent
  rw [Endpoint.RecoveryCoherent, flight.runtime] at fields
  exact fields.2.2.1.trans (congrArg List.length flight.sent)

def initial_flight (initial : TwoWriteInitial cut sender gateway lower upper) :
    Flight initial (source initial) .written 0 where
  recovery := initial.senderState.idle.recovery
  reaction := initial.senderState.idle.reaction
  runtime := initial.senderState.idle.runtime
  ackRuntime := initial.senderState.idle.ackRuntime
  fixed := rfl
  core := by
    simp only [coreAt, Stage.sent, Stage.retiredBytes, Stage.issued, Seq.add_zero]
    have empty := initial.senderState.idle.sent
    change (source initial).core.sent = [] at empty
    rw [← empty]
  pending := initial.senderState.pending
  ledger := initial.senderState.idle.outstanding
  headFixed := trivial
  nextID := by simp only [Stage.outputCount, Nat.add_zero]
  frontier := by simp only [Stage.issued, Nat.add_zero]
  counter := by rw [initial.senderState.idle.timeoutCount]; exact Nat.le_refl _
  timedHead := initial.senderState.idle.timedOut
  retried := by simp only [initial.senderState.idle.outstanding, List.not_mem_nil, false_implies, implies_true]
  quiet := by intro impossible; cases impossible
  advertised := Nat.le_refl _
  originalWindow := fun _ => rfl
  headWindow := by intro head impossible; cases impossible
  armed := by intro impossible; exact False.elim (impossible rfl)
  idle := fun _ => ⟨initial.senderState.idle.deadline, initial.senderState.idle.timedOut, initial.senderState.idle.timeoutCount⟩
  valid := initial.senderState.idle.valid
  coherent := initial.senderState.idle.coherent
  prepared := initial.senderState.idle.prepared
  storage := initial.senderState.idle.storage
  clocked := initial.senderState.idle.clocked
  positive := initial.senderState.idle.positive
  monotone := Nat.le_refl _

def Flight.clock (flight : Flight initial state stage timeouts) (frame : Endpoint.ClockFrame state after)
    (timely : Endpoint.AckTimeReady state after.now) : Flight initial after stage timeouts where
  recovery := { flight.recovery with now := after.now }
  reaction := flight.reaction
  runtime := frame.runtime flight.runtime
  ackRuntime := frame.ackReaction.trans flight.ackRuntime
  fixed := by
    unfold parameters
    rw [frame.pendingLimit, frame.effectiveMSS, frame.ipSendLimit, frame.localReceiveMSS, frame.receiveStore]
    exact flight.fixed
  core := frame.core.trans flight.core
  pending := frame.pending.trans flight.pending
  ledger := flight.ledger
  headFixed := flight.headFixed
  nextID := flight.nextID
  frontier := flight.frontier
  counter := flight.counter
  timedHead := flight.timedHead
  retried := flight.retried
  quiet := flight.quiet
  advertised := by rw [frame.offeredWindow]; exact flight.advertised
  originalWindow := fun preparing => frame.sendWindow.trans (flight.originalWindow preparing)
  headWindow := by intro head present; rw [frame.sendWindow]; exact flight.headWindow head present
  armed := flight.armed
  idle := flight.idle
  valid := frame.valid flight.valid
  coherent := frame.recovery_coherent flight.coherent
  prepared := frame.ack_prepared flight.prepared timely
  storage := frame.storage_coherent flight.storage
  clocked := frame.clocked flight.runtime flight.clocked
  positive := frame.positive flight.runtime flight.positive
  monotone := Nat.le_trans flight.monotone frame.monotone

private theorem send_coherent (flight : Flight initial state stage timeouts) (ready : Endpoint.SendReady state count) :
    Endpoint.RecoveryCoherent (Endpoint.sendState state count) := by
  have old := flight.coherent
  rw [Endpoint.RecoveryCoherent, flight.runtime] at old
  have sentReady : Recovery.SendReady flight.recovery count := by
    have current := ready.2.2.2.2.2.2
    rw [Endpoint.recoveryReady, flight.runtime] at current
    exact current.2
  simp only [Endpoint.RecoveryCoherent, Endpoint.sendState, Endpoint.outputState, flight.runtime, Option.map_some]
  refine ⟨Recovery.sent_valid _ _ old.1 sentReady, old.2.1, ?_, old.2.2.2⟩
  rw [Recovery.sent_flight, old.2.2.1, List.length_append, List.length_take, Nat.min_eq_left ready.2.1]

private theorem send_storage (flight : Flight initial state stage timeouts) (count : Nat) :
    Endpoint.StorageCoherent (Endpoint.sendState state count) := by
  simpa only [Endpoint.StorageCoherent, Endpoint.State.StorageValid, Endpoint.sendState, Endpoint.outputState,
    Endpoint.State.now, flight.runtime, Option.map_some, Option.getD_some, Recovery.sent, EstablishedReceive.State.window] using
    Endpoint.outputState_storage_coherent state flight.prepared flight.storage

private theorem send_advertised (flight : Flight initial state stage timeouts) (count : Nat) :
    Endpoint.offeredWindow (source initial) ≤ Endpoint.offeredWindow (Endpoint.sendState state count) :=
  Nat.le_trans flight.advertised (Endpoint.offeredWindow_le_outputState state flight.prepared.1)

private theorem send_ready (flight : Flight initial state stage timeouts) (positive : 0 < count)
    (pending : count ≤ stage.pending.length) (batch : stage.sent.length + count ≤ lower.length + upper.length)
    (preparing : stage.preparing = true) : Endpoint.SendReady state count := by
  have countBatch : count ≤ lower.length + upper.length := by omega
  have window := initial.senderState.window
  change lower.length + upper.length ≤ (source initial).sendWindow at window
  have mss := initial.senderState.mss
  change lower.length + upper.length ≤ (source initial).effectiveMSS at mss
  have smss := flight.smss
  have valid := flight.recovery_valid
  refine ⟨positive, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [flight.pending]
    exact pending
  · rw [flight.sent, flight.originalWindow preparing]
    exact Nat.le_trans batch window
  · rw [flight.sent]
    have bounded := initial.senderState.idle.valid.2.2.2.1
    change (source initial).sendWindow ≤ 65535 at bounded
    exact Nat.le_trans (Nat.le_trans batch window) bounded
  · rw [flight.effectiveMSS]
    exact Nat.le_trans countBatch mss
  · exact Nat.le_trans (Nat.add_le_add_left (by rw [flight.effectiveMSS]; exact Nat.le_trans countBatch mss) 40)
      flight.valid.2.2.2.2.2.1
  · rw [Endpoint.recoveryReady, flight.runtime]
    refine ⟨flight.coherent, positive, ?_, ?_⟩
    · rw [flight.flight_count, smss, flight.effectiveMSS]
      exact Nat.le_trans batch mss
    · rw [flight.flight_count, valid.2.2.1, smss, flight.effectiveMSS]
      exact Nat.le_trans batch mss

private theorem original_send (flight : Flight initial state stage timeouts) (part : Part) (stamp : Nat)
    (ready : Endpoint.SendReady state (part.bytes lower upper).length)
    (payload : state.pending.take (part.bytes lower upper).length = part.bytes lower upper)
    (sequence : state.core.sendNext = (source initial).core.sendNext.add (part.offset lower)) :
    ∃ original : Original initial part,
      original.operation = ApplicationTrace.Step.make state flight.valid (.send (part.bytes lower upper).length true) stamp ∧
      original.operation.result = ⟨Endpoint.sendState state (part.bytes lower upper).length,
        .accepted (.send (part.bytes lower upper).length), some original.packet, [], none⟩ := by
  have bounded : 40 + (part.bytes lower upper).length ≤ 65535 :=
    Nat.le_trans ready.2.2.2.2.2.1 flight.valid.2.2.2.2.2.2
  obtain ⟨packet, encoded⟩ := Endpoint.emit_exists state (part.bytes lower upper) flight.valid flight.prepared.1 bounded
  have actual := Endpoint.send_of_ready state _ flight.valid ready (Endpoint.ackReady_of_prepared state flight.prepared)
    packet (by rw [payload]; exact encoded)
  let operation := ApplicationTrace.Step.make state flight.valid (.send (part.bytes lower upper).length true) stamp
  have result : operation.result = ⟨Endpoint.sendState state (part.bytes lower upper).length,
      .accepted (.send (part.bytes lower upper).length), some packet, [], none⟩ := actual
  let original : Original initial part := {
    operation, event := rfl, accepted := congrArg Endpoint.Result.decision result, packet
    origin := .send _ true rfl (congrArg Endpoint.Result.decision result) (congrArg Endpoint.Result.output result)
    encoded, payload := Endpoint.emit_payload _ _ _ encoded
    sequence := (Endpoint.emit_transport _ _ _ encoded).2.1.trans sequence }
  exact ⟨original, rfl, result⟩

theorem Flight.first_send_ready (flight : Flight initial state .written timeouts) : Endpoint.SendReady state lower.length := by
  apply send_ready flight (List.length_pos_iff.mpr initial.lowerNonempty)
  · simp only [Stage.pending, List.length_append]
    omega
  · simp only [Stage.sent, List.length_nil, Nat.zero_add]
    omega
  · rfl

theorem Flight.second_send_ready (flight : Flight initial state (.lower first) timeouts) : Endpoint.SendReady state upper.length := by
  apply send_ready flight (List.length_pos_iff.mpr initial.upperNonempty)
  · exact Nat.le_refl _
  · simp only [Stage.sent]
    exact Nat.le_refl _
  · rfl

theorem Flight.first_send (flight : Flight initial state .written timeouts) (stamp : Nat) :
    ∃ first : Original initial .lower,
      first.operation = ApplicationTrace.Step.make state flight.valid (.send lower.length true) stamp ∧
      first.operation.result = ⟨Endpoint.sendState state lower.length, .accepted (.send lower.length), some first.packet, [], none⟩ ∧
      Nonempty (Flight initial first.operation.result.state (.lower first) timeouts) := by
  have payload : state.pending.take lower.length = lower := by rw [flight.pending]; exact List.take_left
  have sequence : state.core.sendNext = (source initial).core.sendNext.add 0 := by
    simpa only [Stage.issued] using flight.sendNext
  obtain ⟨first, operation, result⟩ := original_send flight .lower stamp flight.first_send_ready payload sequence
  dsimp only [Part.bytes] at operation result
  have before : first.operation.before = state := by rw [operation]; rfl
  have time : first.operation.before.now = flight.recovery.now := by
    rw [before, Endpoint.State.now, flight.runtime]
    rfl
  have ready := flight.first_send_ready
  have ledger : (Recovery.sent flight.recovery lower.length).outstanding = [first.entry] := by
    rw [Recovery.sent, flight.ledger]
    simp only [Stage.ledger, List.nil_append]
    congr 1
    simp only [Original.entry, Part.index, Part.offset, Part.bytes, flight.nextID, flight.frontier,
      Stage.outputCount, Stage.issued, Nat.add_zero, time]
  refine ⟨first, operation, result, ?_⟩
  rw [result]
  refine ⟨{
    recovery := Recovery.sent flight.recovery lower.length
    reaction := AckReaction.outputState flight.reaction state.now state.core.receiveNext state.core.capacity state.core.window state.effectiveMSS
    runtime := by simp only [Endpoint.sendState, flight.runtime, Option.map_some]
    ackRuntime := by simp only [Endpoint.sendState, Endpoint.outputState, flight.ackRuntime, Option.map_some]
    fixed := flight.fixed
    core := ?_, pending := ?_, ledger, headFixed := trivial
    nextID := by simp only [Recovery.sent, flight.nextID, Stage.outputCount, Nat.add_zero]
    frontier := by simp only [Recovery.sent, flight.frontier, Stage.issued, Nat.add_zero]
    counter := flight.counter
    timedHead := flight.timedHead
    retried := by simp only [ledger, List.mem_singleton, forall_eq, Original.entry, Bool.false_eq_true, false_implies]
    quiet := fun _ => AckReaction.outputState_pending _ _ _ _ _ _
    advertised := send_advertised flight _
    originalWindow := fun _ => flight.originalWindow rfl
    headWindow := ?_
    armed := ?_
    idle := by intro impossible; cases impossible
    valid := Endpoint.sendState_valid state _ flight.valid ready
    coherent := send_coherent flight ready
    prepared := Endpoint.sendState_ackPrepared state _ flight.prepared
    storage := send_storage flight _
    clocked := Recovery.sent_clocked _ _ flight.clocked
    positive := Recovery.sent_positive _ _ flight.positive (List.length_pos_iff.mpr initial.lowerNonempty)
    monotone := ?_ }⟩
  · change (Endpoint.sendState state lower.length).core = _
    simp only [Endpoint.sendState, flight.core, coreAt, Stage.sent, Stage.retiredBytes, Stage.issued,
      Seq.add_zero, List.nil_append]
    rw [payload]
  · change state.pending.drop lower.length = upper
    rw [flight.pending]
    exact List.drop_left
  · intro head present
    have same : first.entry = head := Option.some.inj present
    subst head
    change lower.length ≤ state.sendWindow
    rw [flight.originalWindow rfl]
    have window := initial.senderState.window
    change lower.length + upper.length ≤ (source initial).sendWindow at window
    omega
  · intro _
    have idle := (flight.idle rfl).1
    simp only [Recovery.sent, idle, Option.isSome_some]
  · simpa only [Endpoint.State.now, Endpoint.sendState, flight.runtime, Option.map_some, Option.getD_some, Recovery.sent] using flight.monotone

theorem Flight.second_send (flight : Flight initial state (.lower first) timeouts) (stamp : Nat) :
    ∃ second : Original initial .upper,
      second.operation = ApplicationTrace.Step.make state flight.valid (.send upper.length true) stamp ∧
      second.operation.result = ⟨Endpoint.sendState state upper.length, .accepted (.send upper.length), some second.packet, [], none⟩ ∧
      Nonempty (Flight initial second.operation.result.state (.both first second first.entry) timeouts) := by
  have payload : state.pending.take upper.length = upper := by rw [flight.pending]; exact List.take_length
  have sequence : state.core.sendNext = (source initial).core.sendNext.add lower.length := flight.sendNext
  obtain ⟨second, operation, result⟩ := original_send flight .upper stamp flight.second_send_ready payload sequence
  dsimp only [Part.bytes] at operation result
  have before : second.operation.before = state := by rw [operation]; rfl
  have time : second.operation.before.now = flight.recovery.now := by
    rw [before, Endpoint.State.now, flight.runtime]
    rfl
  have ready := flight.second_send_ready
  have ledger : (Recovery.sent flight.recovery upper.length).outstanding = [first.entry, second.entry] := by
    rw [Recovery.sent, flight.ledger]
    simp only [Stage.ledger, List.cons_append, List.nil_append]
    congr 2
    simp only [Original.entry, Part.index, Part.offset, Part.bytes, flight.nextID, flight.frontier,
      Stage.outputCount, Stage.issued, time]
  refine ⟨second, operation, result, ?_⟩
  rw [result]
  refine ⟨{
    recovery := Recovery.sent flight.recovery upper.length
    reaction := AckReaction.outputState flight.reaction state.now state.core.receiveNext state.core.capacity state.core.window state.effectiveMSS
    runtime := by simp only [Endpoint.sendState, flight.runtime, Option.map_some]
    ackRuntime := by simp only [Endpoint.sendState, Endpoint.outputState, flight.ackRuntime, Option.map_some]
    fixed := flight.fixed
    core := ?_, pending := ?_, ledger, headFixed := rfl
    nextID := by simp only [Recovery.sent, flight.nextID, Stage.outputCount, Nat.add_assoc]
    frontier := by simp only [Recovery.sent, flight.frontier, Stage.issued, Nat.add_assoc]
    counter := flight.counter
    timedHead := Or.inl flight.timedHead
    retried := by
      intro entry member impossible
      rw [ledger] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same <;> subst entry <;> cases impossible
    quiet := fun _ => AckReaction.outputState_pending _ _ _ _ _ _
    advertised := send_advertised flight _
    originalWindow := by intro impossible; cases impossible
    headWindow := ?_, armed := ?_
    idle := by intro impossible; cases impossible
    valid := Endpoint.sendState_valid state _ flight.valid ready
    coherent := send_coherent flight ready
    prepared := Endpoint.sendState_ackPrepared state _ flight.prepared
    storage := send_storage flight _
    clocked := Recovery.sent_clocked _ _ flight.clocked
    positive := Recovery.sent_positive _ _ flight.positive (List.length_pos_iff.mpr initial.upperNonempty)
    monotone := ?_ }⟩
  · change (Endpoint.sendState state upper.length).core = _
    simp only [Endpoint.sendState, flight.core, coreAt, Stage.sent, Stage.retiredBytes, Stage.issued,
      Seq.add_zero, Seq.add_add]
    rw [payload]
  · change state.pending.drop upper.length = []
    rw [flight.pending]
    exact List.drop_length
  · intro head present
    have same : first.entry = head := Option.some.inj present
    subst head
    exact flight.headWindow first.entry rfl
  · intro _
    cases timer : flight.recovery.deadline <;> simp only [Recovery.sent, timer, Option.isSome_some]
  · simpa only [Endpoint.State.now, Endpoint.sendState, flight.runtime, Option.map_some, Option.getD_some, Recovery.sent] using flight.monotone

def Stage.retry : Stage initial → Nat → Stage initial
  | .both first second head, now => .both first second { head with lastAt := now, retried := true }
  | .tail first second head, now => .tail first second { head with lastAt := now, retried := true }
  | stage, _ => stage

private theorem Stage.retry_fields (stage : Stage initial) (now : Nat) :
    (stage.retry now).pending = stage.pending ∧ (stage.retry now).issued = stage.issued ∧
      (stage.retry now).outputCount = stage.outputCount ∧ (stage.retry now).preparing = stage.preparing ∧
      coreAt initial (stage.retry now) = coreAt initial stage := by cases stage <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem Stage.retry_ledger (stage : Stage initial) (head : Recovery.Outstanding) (rest : List Recovery.Outstanding)
    (source : stage.ledger = head :: rest) (recovering : stage.preparing = false) (now : Nat) :
    (stage.retry now).ledger = { head with lastAt := now, retried := true } :: rest := by
  cases stage with
  | written => cases recovering
  | lower first => cases recovering
  | both first second old =>
    obtain ⟨same, tail⟩ := List.cons.inj source
    cases same
    cases tail
    rfl
  | tail first second old =>
    obtain ⟨same, tail⟩ := List.cons.inj source
    cases same
    cases tail
    rfl
  | retired first second => cases source

private theorem Stage.retry_valid (stage : Stage initial) (valid : stage.HeadValid) (now : Nat) :
    (stage.retry now).HeadValid := by
  cases stage with
  | written => trivial
  | lower first => trivial
  | both first second head => exact valid
  | tail first second head => exact valid
  | retired first second => trivial

private theorem Stage.retry_timed (stage : Stage initial) (valid : stage.HeadValid)
    (head : Recovery.Outstanding) (rest : List Recovery.Outstanding) (source : stage.ledger = head :: rest)
    (recovering : stage.preparing = false) (now : Nat) : (stage.retry now).TimedHead (some head.id) := by
  cases stage with
  | written => cases recovering
  | lower first => cases recovering
  | both first second old =>
    have same := (List.cons.inj source).1
    have id := congrArg Recovery.Outstanding.id valid
    right
    exact congrArg some ((congrArg Recovery.Outstanding.id same).symm.trans id)
  | tail first second old =>
    have same := (List.cons.inj source).1
    have id := congrArg Recovery.Outstanding.id valid
    right; right
    exact congrArg some ((congrArg Recovery.Outstanding.id same).symm.trans id)
  | retired first second => cases source

theorem Flight.timeout_ready (flight : Flight initial state stage timeouts) (head : Recovery.Outstanding)
    (rest : List Recovery.Outstanding) (selected : stage.ledger = head :: rest) (credit : timeouts < 2)
    (timer : flight.recovery.deadline = some deadline) (due : deadline ≤ flight.recovery.now)
    (elapsed : head.lastAt + flight.recovery.rto ≤ flight.recovery.now) :
    Endpoint.HeadTimeoutReady state flight.recovery head rest deadline := by
  refine ⟨flight.runtime, flight.coherent, flight.prepared, flight.ledger.trans selected,
    flight.positive, timer, due, elapsed, ?_, flight.clocked, ?_⟩
  · intro _
    have bounded := flight.counter
    omega
  · exact flight.headWindow head (by rw [selected]; rfl)

def Flight.retry (flight : Flight initial state stage timeouts) (head : Recovery.Outstanding)
    (rest : List Recovery.Outstanding) (selected : stage.ledger = head :: rest) (recovering : stage.preparing = false)
    (credit : timeouts < 2) (timer : flight.recovery.deadline = some deadline)
    (due : deadline ≤ flight.recovery.now) (elapsed : head.lastAt + flight.recovery.rto ≤ flight.recovery.now) :
    Flight initial (Endpoint.headRetryState state flight.recovery head rest)
      (stage.retry flight.recovery.now) (timeouts + 1) := by
  let ready := flight.timeout_ready head rest selected credit timer due elapsed
  have fields := stage.retry_fields flight.recovery.now
  have ledger := stage.retry_ledger head rest selected recovering flight.recovery.now
  refine {
    recovery := Recovery.timeoutState flight.recovery head rest
    reaction := AckReaction.outputState flight.reaction state.now state.core.receiveNext state.core.capacity state.core.window state.effectiveMSS
    runtime := rfl
    ackRuntime := by simp only [Endpoint.headRetryState, Endpoint.outputState, flight.ackRuntime, Option.map_some]
    fixed := flight.fixed
    core := flight.core.trans fields.2.2.2.2.symm
    pending := flight.pending.trans fields.1.symm
    ledger := ledger.symm
    headFixed := stage.retry_valid flight.headFixed _
    nextID := flight.nextID.trans (congrArg (initial.senderState.idle.recovery.nextId + ·) fields.2.2.1.symm)
    frontier := flight.frontier.trans (congrArg (initial.senderState.idle.recovery.frontier + ·) fields.2.1.symm)
    counter := ?_
    timedHead := stage.retry_timed flight.headFixed head rest selected recovering _
    retried := by intro entry member repeated; omega
    quiet := fun _ => AckReaction.outputState_pending _ _ _ _ _ _
    advertised := Nat.le_trans flight.advertised (Endpoint.offeredWindow_le_outputState state flight.prepared.1)
    originalWindow := ?_
    headWindow := ?_
    armed := fun _ => rfl
    idle := ?_
    valid := Endpoint.headRetryState_valid ready flight.valid
    coherent := Endpoint.headRetryState_coherent ready
    prepared := Endpoint.headRetryState_prepared ready
    storage := Endpoint.headRetryState_storage_coherent ready flight.storage
    clocked := Endpoint.headRetryState_clocked ready
    positive := Endpoint.headRetryState_positive ready
    monotone := ?_ }
  · change (if flight.recovery.lastTimedOut = some head.id then flight.recovery.timeoutCount + 1 else 1) ≤ timeouts + 1
    have bound := flight.counter
    split <;> omega
  · intro preparing
    rw [fields.2.2.2.1, recovering] at preparing
    cases preparing
  · intro repeated present
    rw [ledger] at present
    have same := Option.some.inj present
    cases same
    exact flight.headWindow head (by rw [selected]; rfl)
  · intro empty
    rw [ledger] at empty
    cases empty
  · simpa only [Endpoint.headRetryState, Endpoint.State.now, flight.runtime, Option.map_some, Option.getD_some, Recovery.timeoutState] using flight.monotone

theorem Flight.retry_enabled (flight : Flight initial state stage timeouts) (head : Recovery.Outstanding)
    (rest : List Recovery.Outstanding) (selected : stage.ledger = head :: rest) (recovering : stage.preparing = false)
    (credit : timeouts < 2) (timer : flight.recovery.deadline = some deadline)
    (due : deadline ≤ flight.recovery.now) (elapsed : head.lastAt + flight.recovery.rto ≤ flight.recovery.now) :
    ∃ packet, Endpoint.timeout state true =
      ⟨Endpoint.headRetryState state flight.recovery head rest, .accepted (.retry head.count), some packet, [], none⟩ ∧
      Endpoint.emitAt state state.core.sendUna (state.core.sent.take head.count) = .ok packet ∧
      Nonempty (Flight initial (Endpoint.timeout state true).state (stage.retry flight.recovery.now) (timeouts + 1)) := by
  obtain ⟨packet, result, encoded⟩ := Endpoint.head_timeout_success_enabled state flight.recovery head rest deadline
    flight.valid (flight.timeout_ready head rest selected credit timer due elapsed)
  refine ⟨packet, result, encoded, ?_⟩
  rw [result]
  exact ⟨flight.retry head rest selected recovering credit timer due elapsed⟩

theorem timeout_new_head (recovery : Recovery.State) (head : Recovery.Outstanding) (rest : List Recovery.Outstanding)
    (fresh : recovery.lastTimedOut ≠ some head.id) : (Recovery.timeoutState recovery head rest).timeoutCount = 1 := by
  simp only [Recovery.timeoutState, fresh, ite_false]

inductive Retires : Stage initial → Nat → Stage initial → Prop
  | lower (first : Original initial .lower) (second : Original initial .upper) (head : Recovery.Outstanding) :
      Retires (.both first second head) lower.length (.tail first second second.entry)
  | both (first : Original initial .lower) (second : Original initial .upper) (head : Recovery.Outstanding) :
      Retires (.both first second head) (lower.length + upper.length) (.retired first second)
  | tail (first : Original initial .lower) (second : Original initial .upper) (head : Recovery.Outstanding) :
      Retires (.tail first second head) upper.length (.retired first second)

private theorem Retires.positive (retiring : Retires stage count next) : 0 < count := by
  have first := List.length_pos_iff.mpr initial.lowerNonempty
  have second := List.length_pos_iff.mpr initial.upperNonempty
  cases retiring <;> omega

private theorem Retires.bounded (retiring : Retires stage count next) : count ≤ stage.sent.length := by
  cases retiring <;> simp only [Stage.sent, List.length_append] <;> omega

private theorem Retires.fields (retiring : Retires stage count next) :
    next.pending = stage.pending ∧ next.issued = stage.issued ∧ next.outputCount = stage.outputCount ∧
      next.preparing = false ∧ stage.hasOutput = true := by cases retiring <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem Retires.headValid (retiring : Retires stage count next) : next.HeadValid := by
  cases retiring
  · rfl
  · trivial
  · trivial

private theorem Retires.core (retiring : Retires stage count next) :
    EstablishedReceive.commit (coreAt initial stage) [] count = coreAt initial next := by
  cases retiring <;>
    simp [EstablishedReceive.commit, coreAt, Stage.sent, Stage.retiredBytes, Stage.issued,
      Seq.add_add, List.drop_append]

private theorem Retires.ledger (retiring : Retires stage count next) (fixed : stage.HeadValid) :
    Recovery.retire count stage.ledger = next.ledger := by
  have firstPositive := List.length_pos_iff.mpr initial.lowerNonempty
  have secondPositive := List.length_pos_iff.mpr initial.upperNonempty
  cases retiring with
  | lower first second head =>
    have size : head.count = lower.length := congrArg Recovery.Outstanding.count fixed
    simp only [Stage.ledger, Recovery.retire, Nat.ne_of_gt firstPositive, ite_false, size,
      Nat.le_refl, ite_true, Nat.sub_self]
  | both first second head =>
    have size : head.count = lower.length := congrArg Recovery.Outstanding.count fixed
    have nonzero : lower.length + upper.length ≠ 0 := by omega
    have bounded : lower.length ≤ lower.length + upper.length := by omega
    simp only [Stage.ledger, Recovery.retire, nonzero, ite_false, size, bounded, ite_true,
      Nat.add_sub_cancel_left, Original.entry, Part.bytes, Nat.ne_of_gt secondPositive, Nat.le_refl, Nat.sub_self]
  | tail first second head =>
    have size : head.count = upper.length := congrArg Recovery.Outstanding.count fixed
    simp only [Stage.ledger, Recovery.retire, Nat.ne_of_gt secondPositive, ite_false, size, Nat.le_refl, ite_true, Nat.sub_self]

private theorem Retires.unretried (retiring : Retires stage count next) (entry : Recovery.Outstanding)
    (member : entry ∈ next.ledger) : entry.retried = false := by
  cases retiring with
  | lower first second head =>
    have same : entry = second.entry := List.mem_singleton.mp member
    subst entry
    rfl
  | both first second head => cases member
  | tail first second head => cases member

private theorem Retires.head_space (retiring : Retires stage count next) (head : Recovery.Outstanding)
    (present : next.ledger.head? = some head) : head.count ≤ next.sent.length := by
  cases retiring with
  | lower first second old =>
    have same : second.entry = head := Option.some.inj present
    subst head
    exact Nat.le_refl _
  | both first second old => cases present
  | tail first second old => cases present

private theorem Retires.timed (retiring : Retires stage count next) (timed : stage.TimedHead last) :
    next.TimedHead (if next.ledger.isEmpty then none else last) := by
  cases retiring with
  | lower first second head =>
    rcases timed with absent | lower
    · exact Or.inl absent
    · exact Or.inr (Or.inl lower)
  | both first second head => rfl
  | tail first second head => rfl

private theorem ack_parameters (received : Endpoint.AdvancingAck state packet recovery after) : parameters after = parameters state := by
  rw [received.afterEq]
  unfold Endpoint.advancingAckState Endpoint.inOrderReceivedWith Endpoint.windowState
  split <;> rfl

private theorem ack_reaction (received : Endpoint.AdvancingAck state packet recovery after) : after.ackReaction = state.ackReaction := by
  rw [received.afterEq]
  unfold Endpoint.advancingAckState Endpoint.inOrderReceivedWith
  rw [Endpoint.windowState_ackReaction]

private theorem ack_window (received : Endpoint.AdvancingAck state packet recovery after)
    (old : count ≤ state.sendWindow) (incoming : count ≤ packet.packet.segment.window.val) : count ≤ after.sendWindow := by
  rw [received.afterEq]
  unfold Endpoint.advancingAckState Endpoint.inOrderReceivedWith Endpoint.windowState
  split
  · exact incoming
  · exact old

private theorem acknowledge_nextID (recovery : Recovery.State) (count : Nat) :
    (Recovery.acknowledgeState recovery count).nextId = recovery.nextId := by
  unfold Recovery.acknowledgeState
  split <;> rfl

private theorem acknowledge_frontier (recovery : Recovery.State) (count : Nat) :
    (Recovery.acknowledgeState recovery count).frontier = recovery.frontier := by
  unfold Recovery.acknowledgeState
  split <;> rfl

private theorem acknowledge_counter (recovery : Recovery.State) (count : Nat) :
    (Recovery.acknowledgeState recovery count).timeoutCount ≤ recovery.timeoutCount := by
  unfold Recovery.acknowledgeState
  split
  · exact Nat.le_refl _
  · dsimp only
    split
    · exact Nat.zero_le _
    · exact Nat.le_refl _

private theorem acknowledge_timed (recovery : Recovery.State) (count : Nat) (positive : 0 < count) :
    (Recovery.acknowledgeState recovery count).lastTimedOut =
      if (Recovery.retire count recovery.outstanding).isEmpty then none else recovery.lastTimedOut := by
  rw [Recovery.acknowledgeState, ite_eq_right (Nat.ne_of_gt positive)]

private theorem acknowledge_armed (recovery : Recovery.State) (count : Nat) (positive : 0 < count)
    (nonempty : Recovery.retire count recovery.outstanding ≠ []) :
    (Recovery.acknowledgeState recovery count).deadline.isSome = true := by
  rw [Recovery.acknowledgeState, ite_eq_right (Nat.ne_of_gt positive)]
  simp only [List.isEmpty_eq_false_iff.mpr nonempty, Bool.false_eq_true, ite_false, Option.isSome_some]

private theorem acknowledge_idle (recovery : Recovery.State) (count : Nat) (positive : 0 < count)
    (empty : Recovery.retire count recovery.outstanding = []) :
    (Recovery.acknowledgeState recovery count).deadline = none ∧
      (Recovery.acknowledgeState recovery count).lastTimedOut = none ∧
      (Recovery.acknowledgeState recovery count).timeoutCount = 0 := by
  rw [Recovery.acknowledgeState, ite_eq_right (Nat.ne_of_gt positive)]
  simp only [empty, List.isEmpty_nil, ite_true, and_self]

private theorem ack_ledger (flight : Flight initial state stage timeouts) (retiring : Retires stage count next)
    (counted : Endpoint.inOrderCount state packet = count) (current : Recovery.State)
    (same : current = Endpoint.advancingAckRecovery state packet flight.recovery) : current.outstanding = next.ledger := by
  have remaining : Recovery.retire count flight.recovery.outstanding = next.ledger := by
    rw [flight.ledger]
    exact retiring.ledger flight.headFixed
  rw [same]
  simp only [Endpoint.advancingAckRecovery, counted, Recovery.acknowledgeState,
    Nat.ne_of_gt retiring.positive, ite_false, remaining]

private theorem ack_id (flight : Flight initial state stage timeouts) (retiring : Retires stage count next)
    (current : Recovery.State) (same : current = Endpoint.advancingAckRecovery state packet flight.recovery) :
    current.nextId = initial.senderState.idle.recovery.nextId + next.outputCount := by
  rw [same]
  exact (acknowledge_nextID flight.recovery (Endpoint.inOrderCount state packet)).trans
    (flight.nextID.trans (congrArg (initial.senderState.idle.recovery.nextId + ·) retiring.fields.2.2.1.symm))

private theorem ack_frontier (flight : Flight initial state stage timeouts) (retiring : Retires stage count next)
    (current : Recovery.State) (same : current = Endpoint.advancingAckRecovery state packet flight.recovery) :
    current.frontier = initial.senderState.idle.recovery.frontier + next.issued := by
  rw [same]
  exact (acknowledge_frontier flight.recovery (Endpoint.inOrderCount state packet)).trans
    (flight.frontier.trans (congrArg (initial.senderState.idle.recovery.frontier + ·) retiring.fields.2.1.symm))

private theorem ack_counter (flight : Flight initial state stage timeouts)
    (current : Recovery.State) (same : current = Endpoint.advancingAckRecovery state packet flight.recovery) :
    current.timeoutCount ≤ timeouts := by
  rw [same]
  exact Nat.le_trans (acknowledge_counter flight.recovery (Endpoint.inOrderCount state packet)) flight.counter

private theorem ack_timed (flight : Flight initial state stage timeouts) (retiring : Retires stage count next)
    (counted : Endpoint.inOrderCount state packet = count) (current : Recovery.State)
    (same : current = Endpoint.advancingAckRecovery state packet flight.recovery) : next.TimedHead current.lastTimedOut := by
  have positiveNow : 0 < Endpoint.inOrderCount state packet := by rw [counted]; exact retiring.positive
  have remaining : Recovery.retire (Endpoint.inOrderCount state packet) flight.recovery.outstanding = next.ledger := by
    rw [counted, flight.ledger]
    exact retiring.ledger flight.headFixed
  have mapped := acknowledge_timed flight.recovery (Endpoint.inOrderCount state packet) positiveNow
  have mappedNext : current.lastTimedOut = (if next.ledger.isEmpty then none else flight.recovery.lastTimedOut) := by
    rw [same]
    exact mapped.trans (congrArg (fun entries : List Recovery.Outstanding =>
      if entries.isEmpty then none else flight.recovery.lastTimedOut) remaining)
  exact Eq.mpr (congrArg next.TimedHead mappedNext) (retiring.timed flight.timedHead)

private theorem ack_armed (flight : Flight initial state stage timeouts) (retiring : Retires stage count next)
    (counted : Endpoint.inOrderCount state packet = count) (current : Recovery.State)
    (same : current = Endpoint.advancingAckRecovery state packet flight.recovery) (nonempty : next.ledger ≠ []) :
    current.deadline.isSome = true := by
  rw [same]
  apply acknowledge_armed flight.recovery (Endpoint.inOrderCount state packet) (by rw [counted]; exact retiring.positive)
  rw [counted, flight.ledger, retiring.ledger flight.headFixed]
  exact nonempty

private theorem ack_idle (flight : Flight initial state stage timeouts) (retiring : Retires stage count next)
    (counted : Endpoint.inOrderCount state packet = count) (current : Recovery.State)
    (same : current = Endpoint.advancingAckRecovery state packet flight.recovery) (empty : next.ledger = []) :
    current.deadline = none ∧ current.lastTimedOut = none ∧ current.timeoutCount = 0 := by
  rw [same]
  apply acknowledge_idle flight.recovery (Endpoint.inOrderCount state packet) (by rw [counted]; exact retiring.positive)
  rw [counted, flight.ledger, retiring.ledger flight.headFixed]
  exact empty

private theorem ack_retried (flight : Flight initial state stage timeouts) (retiring : Retires stage count next)
    (counted : Endpoint.inOrderCount state packet = count) (current : Recovery.State)
    (same : current = Endpoint.advancingAckRecovery state packet flight.recovery) :
    ∀ entry ∈ current.outstanding, entry.retried = true → 0 < timeouts := by
  intro entry member repeated
  have stored : entry ∈ next.ledger := ack_ledger flight retiring counted current same ▸ member
  have quiet := retiring.unretried entry stored
  exact False.elim (Bool.noConfusion (quiet.symm.trans repeated))

private theorem ack_core (flight : Flight initial state stage timeouts) (retiring : Retires stage count next)
    (received : Endpoint.AdvancingAck state packet flight.recovery after)
    (counted : Endpoint.inOrderCount state packet = count) : after.core = coreAt initial next := by
  rw [received.core, flight.core, counted]
  exact retiring.core

private theorem ack_head_space (flight : Flight initial state stage timeouts) (retiring : Retires stage count next)
    (received : Endpoint.AdvancingAck state packet flight.recovery after)
    (old : next.sent.length ≤ state.sendWindow) (incoming : next.sent.length ≤ packet.packet.segment.window.val) :
    ∀ head, next.ledger.head? = some head → head.count ≤ after.sendWindow := by
  intro head present
  exact Nat.le_trans (retiring.head_space head present) (ack_window received old incoming)

private noncomputable def ack_frame (flight : Flight initial state stage timeouts) (retiring : Retires stage count next)
    (received : Endpoint.AdvancingAck state packet flight.recovery after)
    (counted : Endpoint.inOrderCount state packet = count)
    (oldWindow : next.sent.length ≤ state.sendWindow) (incomingWindow : next.sent.length ≤ packet.packet.segment.window.val)
    (current : Recovery.State) (same : current = Endpoint.advancingAckRecovery state packet flight.recovery) :
    Flight initial after next timeouts where
  recovery := current
  reaction := flight.reaction
  runtime := by rw [same]; exact received.runtime
  ackRuntime := (ack_reaction received).trans flight.ackRuntime
  fixed := (ack_parameters received).trans flight.fixed
  core := ack_core flight retiring received counted
  pending := received.pending.trans (flight.pending.trans retiring.fields.1.symm)
  ledger := ack_ledger flight retiring counted current same
  headFixed := retiring.headValid
  nextID := ack_id flight retiring current same
  frontier := ack_frontier flight retiring current same
  counter := ack_counter flight current same
  timedHead := ack_timed flight retiring counted current same
  retried := ack_retried flight retiring counted current same
  quiet := fun _ => flight.quiet retiring.fields.2.2.2.2
  advertised := by rw [received.offeredWindow]; exact flight.advertised
  originalWindow := by intro impossible; rw [retiring.fields.2.2.2.1] at impossible; cases impossible
  headWindow := ack_head_space flight retiring received oldWindow incomingWindow
  armed := ack_armed flight retiring counted current same
  idle := ack_idle flight retiring counted current same
  valid := received.valid
  coherent := received.coherent
  prepared := received.prepared
  storage := received.storage
  clocked := by rw [same]; exact received.recovery_clocked flight.clocked
  positive := by rw [same]; exact received.recovery_positive flight.positive
  monotone := Nat.le_trans flight.monotone (Nat.le_of_eq received.now.symm)

noncomputable def Flight.ack_received (flight : Flight initial state stage timeouts) (retiring : Retires stage count next)
    (received : Endpoint.AdvancingAck state packet flight.recovery after)
    (counted : Endpoint.inOrderCount state packet = count)
    (oldWindow : next.sent.length ≤ state.sendWindow) (incomingWindow : next.sent.length ≤ packet.packet.segment.window.val) :
    Flight initial after next timeouts :=
  ack_frame flight retiring received counted oldWindow incomingWindow
    (Endpoint.advancingAckRecovery state packet flight.recovery) rfl

theorem Flight.ack_counted (flight : Flight initial state stage timeouts) (retiring : Retires stage count next)
    (acknowledgment : packet.packet.segment.acknowledgment = state.core.sendUna.add count) :
    Endpoint.inOrderCount state packet = count := by
  have bounded : count ≤ state.core.sent.length := by rw [flight.sent]; exact retiring.bounded
  have window := flight.valid.1.2.2.2.1
  have small : count < Seq.modulus := by
    unfold EstablishedReceive.maxSendWindow at window
    unfold Seq.modulus
    omega
  unfold Endpoint.inOrderCount
  rw [acknowledgment, Seq.distance_add, Nat.mod_eq_of_lt small]

theorem Flight.ack_conditions (flight : Flight initial state stage timeouts) (retiring : Retires stage count next)
    (tuple : packet.packet.header = state.core.inbound)
    (controls : EstablishedReceive.control packet.packet.segment = none)
    (ack : Flags.ack packet.packet.segment.flags = true)
    (sequence : packet.packet.segment.sequence = state.core.receiveNext)
    (empty : packet.packet.segment.payload = [])
    (acknowledgment : packet.packet.segment.acknowledgment = state.core.sendUna.add count) :
    Endpoint.AdvancingAckConditions state packet flight.recovery flight.reaction := by
  have counted := flight.ack_counted retiring acknowledgment
  refine ⟨flight.valid, flight.coherent, flight.prepared, flight.storage, flight.runtime, flight.ackRuntime,
    tuple, controls, ack, sequence, empty, ?_, ?_⟩
  · rw [counted]
    exact retiring.positive
  · rw [counted, flight.sent]
    exact retiring.bounded

theorem Flight.ack_enabled (flight : Flight initial state stage timeouts) (retiring : Retires stage count next)
    (tuple : packet.packet.header = state.core.inbound)
    (controls : EstablishedReceive.control packet.packet.segment = none)
    (ack : Flags.ack packet.packet.segment.flags = true)
    (sequence : packet.packet.segment.sequence = state.core.receiveNext)
    (empty : packet.packet.segment.payload = [])
    (acknowledgment : packet.packet.segment.acknowledgment = state.core.sendUna.add count)
    (oldWindow : next.sent.length ≤ state.sendWindow) (incomingWindow : next.sent.length ≤ packet.packet.segment.window.val) :
    ∃ after, Endpoint.AdvancingAck state packet flight.recovery after ∧ Nonempty (Flight initial after next timeouts) := by
  obtain ⟨after, received⟩ := Endpoint.receive_advancing_ack_enabled
    (flight.ack_conditions retiring tuple controls ack sequence empty acknowledgment)
  exact ⟨after, received, ⟨flight.ack_received retiring received (flight.ack_counted retiring acknowledgment) oldWindow incomingWindow⟩⟩

theorem original_ids_distinct (first : Original initial .lower) (second : Original initial .upper) : first.entry.id ≠ second.entry.id := by
  intro same
  change initial.senderState.idle.recovery.nextId + 0 = initial.senderState.idle.recovery.nextId + 1 at same
  omega

theorem Flight.partial_tail_credit (flight : Flight initial state (.both first second head) timeouts)
    (received : Endpoint.AdvancingAck state packet flight.recovery after)
    (counted : Endpoint.inOrderCount state packet = lower.length) :
    let next := Endpoint.advancingAckRecovery state packet flight.recovery
    next.lastTimedOut ≠ some second.entry.id ∧ (Recovery.timeoutState next second.entry []).timeoutCount = 1 := by
  have size : head.count = lower.length := congrArg Recovery.Outstanding.count flight.headFixed
  have fields := received.tail_fields head second.entry [] flight.ledger (counted.trans size.symm)
  have distinct := original_ids_distinct first second
  have fresh : flight.recovery.lastTimedOut ≠ some second.entry.id := by
    rcases flight.timedHead with absent | lower
    · rw [absent]
      intro impossible
      cases impossible
    · rw [lower]
      exact fun same => distinct (Option.some.inj same)
  have nextFresh : (Endpoint.advancingAckRecovery state packet flight.recovery).lastTimedOut ≠ some second.entry.id := by
    rw [fields.2.2.1]
    exact fresh
  exact ⟨nextFresh, timeout_new_head _ _ _ nextFresh⟩

theorem Flight.retired_fields (flight : Flight initial state (.retired first second) timeouts) :
    state.core.sent = [] ∧ state.pending = [] ∧ flight.recovery.outstanding = [] ∧
      flight.recovery.deadline = none ∧ flight.recovery.lastTimedOut = none ∧ flight.recovery.timeoutCount = 0 ∧
      flight.recovery.nextId = initial.senderState.idle.recovery.nextId + 2 ∧
      flight.recovery.frontier = initial.senderState.idle.recovery.frontier + (lower.length + upper.length) := by
  have idle := flight.idle rfl
  exact ⟨flight.sent, flight.pending, flight.ledger, idle.1, idle.2.1, idle.2.2, flight.nextID, flight.frontier⟩

def Flight.zero_ack_received (flight : Flight initial state stage timeouts)
    (received : Endpoint.ZeroAck state packet flight.recovery after) (recovering : stage.preparing = false)
    (incoming : ∀ head, stage.ledger.head? = some head → head.count ≤ packet.packet.segment.window.val) :
    Flight initial after stage timeouts := by
  let recovery := Endpoint.zeroAckRecovery state packet flight.recovery
  have fixed := Endpoint.zeroAckRecovery_fixed state packet flight.recovery
  have ledger := congrArg Recovery.State.outstanding fixed
  have now := congrArg Recovery.State.now fixed
  have deadline := congrArg Recovery.State.deadline fixed
  have timed := congrArg Recovery.State.lastTimedOut fixed
  have count := congrArg Recovery.State.timeoutCount fixed
  change recovery.outstanding = flight.recovery.outstanding at ledger
  change recovery.now = flight.recovery.now at now
  have nextID := congrArg Recovery.State.nextId fixed
  have frontier := congrArg Recovery.State.frontier fixed
  have sameNow : after.now = state.now := by
    simp only [Endpoint.State.now, received.runtime, flight.runtime, Option.map_some, Option.getD_some]
    exact now
  refine {
    recovery
    reaction := flight.reaction
    runtime := received.runtime
    ackRuntime := received.ack_reaction.trans flight.ackRuntime
    fixed := ?_
    core := received.core.trans flight.core
    pending := received.pending.trans flight.pending
    ledger := ledger.trans flight.ledger
    headFixed := flight.headFixed
    nextID := nextID.trans flight.nextID
    frontier := frontier.trans flight.frontier
    counter := count.symm ▸ flight.counter
    timedHead := timed.symm ▸ flight.timedHead
    retried := by simpa only [ledger] using flight.retried
    quiet := flight.quiet
    advertised := by rw [received.offeredWindow]; exact flight.advertised
    originalWindow := ?_
    headWindow := fun head present => received.window_space (flight.headWindow head present) (incoming head present)
    armed := fun nonempty => deadline.symm ▸ flight.armed nonempty
    idle := ?_
    valid := received.valid
    coherent := received.coherent
    prepared := received.prepared
    storage := received.storage
    clocked := ?_
    positive := ?_
    monotone := sameNow.symm ▸ flight.monotone }
  · rw [received.afterEq]
    unfold parameters Endpoint.zeroAckState Endpoint.windowState
    split <;> exact flight.fixed
  · intro preparing
    rw [recovering] at preparing
    cases preparing
  · intro empty
    obtain ⟨timer, last, counter⟩ := flight.idle empty
    exact ⟨deadline.trans timer, timed.trans last, count.trans counter⟩
  · simpa only [Recovery.State.Clocked, ledger, now] using flight.clocked
  · simpa only [Recovery.State.Positive, ledger] using flight.positive

theorem Flight.zero_ack_enabled (flight : Flight initial state stage timeouts)
    (recovering : stage.preparing = false)
    (incoming : ∀ head, stage.ledger.head? = some head → head.count ≤ packet.packet.segment.window.val)
    (tuple : packet.packet.header = state.core.inbound)
    (controls : EstablishedReceive.control packet.packet.segment = none)
    (ack : Flags.ack packet.packet.segment.flags = true)
    (sequence : packet.packet.segment.sequence = state.core.receiveNext)
    (empty : packet.packet.segment.payload = [])
    (acknowledgment : packet.packet.segment.acknowledgment = state.core.sendUna)
    (credit : Endpoint.qualifyingDuplicate state packet.packet.segment 0 = true → flight.recovery.duplicateAcks < 2) :
    ∃ after, Endpoint.ZeroAck state packet flight.recovery after ∧ Nonempty (Flight initial after stage timeouts) := by
  have conditions : Endpoint.ZeroAckConditions state packet flight.recovery flight.reaction :=
    ⟨flight.valid, flight.coherent, flight.prepared, flight.storage, flight.runtime, flight.ackRuntime,
      tuple, controls, ack, sequence, empty, acknowledgment, credit⟩
  obtain ⟨after, received⟩ := Endpoint.receive_zero_ack_enabled conditions
  exact ⟨after, received, ⟨flight.zero_ack_received received recovering incoming⟩⟩

end Netlib.Check.CampusTCPTwoProgressSender
