import Netlib.Check.CampusTCPTwoProgressRead
import Netlib.Check.CampusTCPWriteEnabled

/-!
# Endpoint facts for the reverse write

The forward read keeps its actual ACK work and recovery history.
The reverse write changes only that endpoint's pending bytes.
The full exchange must derive these current reserves from its initial reserves.
-/

namespace Netlib.Check.CampusTCPTwoReverseEndpoints

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressRead (Completed ReceiverClosed)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {first : CampusTCPTwoProgressSender.Original initial .lower}
variable {second : CampusTCPTwoProgressSender.Original initial .upper} {timeouts : Nat}
variable {state : Endpoint.State}

def closed_idle (closed : ReceiverClosed initial state) : IdleEndpoint state where
  recovery := { closed.facts.recovery with now := state.now }
  reaction := AckReaction.read closed.facts.reaction closed.before.now closed.before.core.receiveNext
    closed.before.core.capacity closed.before.core.window
    (Endpoint.readState closed.before (lower ++ upper).length).core.window closed.before.effectiveMSS
  runtime := closed.runtime
  ackRuntime := closed.ackRuntime
  outstanding := closed.facts.outstanding
  sent := by rw [closed.core]; exact closed.facts.sent
  deadline := (congrArg Recovery.State.deadline closed.recovery_fields).trans initial.receiverState.idle.deadline
  timedOut := (congrArg Recovery.State.lastTimedOut closed.recovery_fields).trans initial.receiverState.idle.timedOut
  timeoutCount := (congrArg Recovery.State.timeoutCount closed.recovery_fields).trans initial.receiverState.idle.timeoutCount
  duplicate := closed.facts.duplicate
  valid := closed.valid
  coherent := closed.coherent
  prepared := closed.prepared
  storage := closed.storage

theorem closed_recovery (closed : ReceiverClosed initial state) :
    (closed_idle closed).recovery = { initial.receiverState.idle.recovery with now := state.now } :=
  closed.recovery_fields

theorem closed_pending (closed : ReceiverClosed initial state) : state.pending = [] :=
  closed.pending.trans (closed.facts.pending.trans initial.receiverState.pending)

theorem closed_capacity (closed : ReceiverClosed initial state) :
    state.core.capacity = (endpoint cut.endpoints sender.other).core.capacity := by
  rw [closed.core]
  exact closed.facts.capacity

theorem closed_pendingLimit (closed : ReceiverClosed initial state) :
    state.pendingLimit = (endpoint cut.endpoints sender.other).pendingLimit :=
  closed.frame.pendingLimit.trans closed.facts.pendingLimit

theorem closed_mss (closed : ReceiverClosed initial state) :
    state.effectiveMSS = (endpoint cut.endpoints sender.other).effectiveMSS :=
  closed.frame.effectiveMSS.trans closed.facts.effectiveMSS

def receiver_idle (done : Completed initial current first second timeouts) :
    IdleEndpoint (endpoint current.endpoints sender.other) := closed_idle done.receiver

def sender_idle (done : Completed initial current first second timeouts)
    (zero : done.senderFlight.recovery.duplicateAcks = 0) : IdleEndpoint (endpoint current.endpoints sender) where
  recovery := done.senderFlight.recovery
  reaction := done.senderFlight.reaction
  runtime := done.senderFlight.runtime
  ackRuntime := done.senderFlight.ackRuntime
  outstanding := done.senderFlight.ledger
  sent := by rw [done.senderFlight.core]; rfl
  deadline := (done.senderFlight.idle rfl).1
  timedOut := (done.senderFlight.idle rfl).2.1
  timeoutCount := (done.senderFlight.idle rfl).2.2
  duplicate := zero
  valid := done.senderFlight.valid
  coherent := done.senderFlight.coherent
  prepared := done.senderFlight.prepared
  storage := done.senderFlight.storage

theorem sender_pending (done : Completed initial current first second timeouts) :
    (endpoint current.endpoints sender).pending = [] := done.senderFlight.pending

theorem sender_unread (done : Completed initial current first second timeouts)
    (unread : (endpoint cut.endpoints sender).core.received = []) :
    (endpoint current.endpoints sender).core.received = [] := by
  rw [done.senderFlight.core]
  exact unread

theorem sender_store (done : Completed initial current first second timeouts) :
    (endpoint current.endpoints sender).receiveStore = (endpoint cut.endpoints sender).receiveStore :=
  congrArg CampusTCPTwoProgressSender.Parameters.receiveStore done.senderFlight.fixed

theorem sender_held (done : Completed initial current first second timeouts) :
    (endpoint current.endpoints sender).receiveStore.held = [] := by
  rw [sender_store done]
  exact initial.senderState.held

theorem sender_capacity (done : Completed initial current first second timeouts) :
    (endpoint current.endpoints sender).core.capacity = (endpoint cut.endpoints sender).core.capacity := by
  rw [done.senderFlight.core]
  rfl

structure Reserves (current : Cut input complete) (sender : Actor) (lower upper : List UInt8) : Prop where
  pending : (lower ++ upper).length ≤ (endpoint current.endpoints sender.other).pendingLimit
  window : lower.length + upper.length ≤ (endpoint current.endpoints sender.other).sendWindow
  mss : lower.length + upper.length ≤ (endpoint current.endpoints sender.other).effectiveMSS
  receiveSpace : (lower ++ upper).length ≤ Endpoint.offeredWindow (endpoint current.endpoints sender)

variable {reverseLower reverseUpper : List UInt8}

def empty_receiver (done : Completed initial current first second timeouts)
    (unread : (endpoint cut.endpoints sender).core.received = [])
    (zero : done.senderFlight.recovery.duplicateAcks = 0)
    (space : (reverseLower ++ reverseUpper).length ≤ Endpoint.offeredWindow (endpoint current.endpoints sender)) :
    EmptyReceiver current sender (reverseLower ++ reverseUpper) where
  idle := sender_idle done zero
  pending := sender_pending done
  unread := sender_unread done unread
  held := sender_held done
  space := space

def written_idle (idle : IdleEndpoint state) (bytes : List UInt8)
    (fits : state.pending.length + bytes.length ≤ state.pendingLimit) : IdleEndpoint (Endpoint.writeState state bytes) where
  recovery := idle.recovery
  reaction := idle.reaction
  runtime := idle.runtime
  ackRuntime := idle.ackRuntime
  outstanding := idle.outstanding
  sent := idle.sent
  deadline := idle.deadline
  timedOut := idle.timedOut
  timeoutCount := idle.timeoutCount
  duplicate := idle.duplicate
  valid := Endpoint.writeState_valid state bytes idle.valid fits
  coherent := idle.coherent
  prepared := Endpoint.writeState_ackPrepared state bytes idle.prepared
  storage := idle.storage

theorem write_enabled (done : Completed initial current first second timeouts)
    (reserve : Reserves current sender reverseLower reverseUpper) :
    Endpoint.write (endpoint current.endpoints sender.other) (reverseLower ++ reverseUpper) =
      ⟨Endpoint.writeState (endpoint current.endpoints sender.other) (reverseLower ++ reverseUpper),
        .accepted (.write (reverseLower ++ reverseUpper).length), none, [], none⟩ := by
  apply Endpoint.write_of_fits _ _ done.receiver.valid
  rw [closed_pending done.receiver, List.length_nil, Nat.zero_add]
  exact reserve.pending

variable {actual : Step input}

def after_write_sender (done : Completed initial current first second timeouts)
    (reserve : Reserves current sender reverseLower reverseUpper)
    (write : CampusTCPWriteEnabled.WriteMove current sender.other (reverseLower ++ reverseUpper) actual) :
    WrittenSender write.move.after sender.other reverseLower reverseUpper where
  idle := by
    rw [write.selected]
    exact written_idle (receiver_idle done) _ (by
      rw [closed_pending done.receiver, List.length_nil, Nat.zero_add]
      exact reserve.pending)
  pending := by rw [write.selected]; simp only [Endpoint.writeState, closed_pending done.receiver, List.nil_append]
  held := by rw [write.selected]; exact done.receiver.held
  window := by rw [write.selected]; exact reserve.window
  mss := by rw [write.selected]; exact reserve.mss

def after_write_receiver (done : Completed initial current first second timeouts)
    (reserve : Reserves current sender reverseLower reverseUpper)
    (unread : (endpoint cut.endpoints sender).core.received = [])
    (zero : done.senderFlight.recovery.duplicateAcks = 0)
    (write : CampusTCPWriteEnabled.WriteMove current sender.other (reverseLower ++ reverseUpper) actual) :
    EmptyReceiver write.move.after sender (reverseLower ++ reverseUpper) := by
  have peer : endpoint write.move.after.endpoints sender = endpoint current.endpoints sender := by
    have other : sender.other.other = sender := by cases sender <;> rfl
    simpa only [other] using write.peer
  let before := empty_receiver done unread zero reserve.receiveSpace
  exact {
    idle := by rw [peer]; exact before.idle
    pending := by rw [peer]; exact before.pending
    unread := by rw [peer]; exact before.unread
    held := by rw [peer]; exact before.held
    space := by rw [peer]; exact before.space }

theorem after_write_ack (write : CampusTCPWriteEnabled.WriteMove current sender.other (reverseLower ++ reverseUpper) actual) :
    (endpoint write.move.after.endpoints sender.other).ackReaction = (endpoint current.endpoints sender.other).ackReaction := by
  rw [write.selected]
  rfl

theorem after_write_recovery (write : CampusTCPWriteEnabled.WriteMove current sender.other (reverseLower ++ reverseUpper) actual) :
    (endpoint write.move.after.endpoints sender.other).recovery = (endpoint current.endpoints sender.other).recovery := by
  rw [write.selected]
  rfl

end Netlib.Check.CampusTCPTwoReverseEndpoints
