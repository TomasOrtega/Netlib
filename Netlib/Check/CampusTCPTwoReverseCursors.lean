import Netlib.Check.CampusTCPTwoReverseWrite

/-!
# Endpoint cursors at the actual reverse write

Both directions retain their sequence history.
The write preserves the two endpoint cursor equalities.
-/

namespace Netlib.Check.CampusTCPTwoReverseCursors

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressRead (ReceiverClosed)
open CampusTCPTwoProgressEvidence (Complete)
open CampusTCPTwoReverseWrite (Boundary)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : CampusTCPTwoProgressMonitor.Monitor} {reverseLower reverseUpper : List UInt8}

theorem closed_sendNext (closed : ReceiverClosed initial state) :
    state.core.sendNext = (endpoint cut.endpoints sender.other).core.sendNext := by
  rw [closed.core]
  exact closed.facts.sendNext

theorem closed_receiveNext (closed : ReceiverClosed initial state) :
    state.core.receiveNext = (endpoint cut.endpoints sender.other).core.receiveNext.add (lower ++ upper).length := by
  rw [closed.core]
  exact closed.facts.receiveNext

variable {actual : Step input}
variable {forward : Complete initial native quantum allowance current monitor}

theorem receiver_cursor (boundary : Boundary forward reverseLower reverseUpper actual) :
    (endpoint boundary.write.move.after.endpoints sender).core.receiveNext =
      (endpoint boundary.write.move.after.endpoints sender.other).core.sendNext := by
  have other : sender.other.other = sender := by cases sender <;> rfl
  have peer := boundary.write.peer
  rw [other] at peer
  rw [peer, boundary.write.selected]
  change (endpoint current.endpoints sender).core.receiveNext =
    (endpoint current.endpoints sender.other).core.sendNext
  rw [forward.completed.senderFlight.receiveNext, closed_sendNext forward.completed.receiver]
  exact (CampusTCPTwoProgressWire.receiver_sequence initial).symm

theorem sender_cursor (boundary : Boundary forward reverseLower reverseUpper actual) :
    (endpoint boundary.write.move.after.endpoints sender.other).core.receiveNext =
      (endpoint boundary.write.move.after.endpoints sender).core.sendNext := by
  have other : sender.other.other = sender := by cases sender <;> rfl
  have peer := boundary.write.peer
  rw [other] at peer
  rw [boundary.write.selected, peer]
  change (endpoint current.endpoints sender.other).core.receiveNext =
    (endpoint current.endpoints sender).core.sendNext
  rw [closed_receiveNext forward.completed.receiver, forward.completed.senderFlight.sendNext,
    initial.geometry.receiverCursor]
  simp only [List.length_append, CampusTCPTwoProgressSender.source, CampusTCPTwoProgressSender.Stage.issued]

theorem gateway_sender_cursor (boundary : Boundary forward reverseLower reverseUpper actual) :
    (endpoint boundary.write.move.after.endpoints sender.other).core.sendNext =
      (boundary.gatewayState.session.lane sender.other.direction).base.add
        (boundary.gatewayState.session.lane sender.other.direction).highEnd := by
  rw [boundary.write.selected]
  change (endpoint current.endpoints sender.other).core.sendNext = _
  rw [closed_sendNext forward.completed.receiver, initial.geometry.receiverSequence, boundary.session]
  have lane : ∀ session : Admission.Session,
      session.lane sender.other.direction = session.peer sender.direction := by
    intro session
    cases sender <;> rfl
  rw [lane, forward.completed.gatewayState.peer_base, forward.completed.gatewayState.peer_highEnd]

end Netlib.Check.CampusTCPTwoReverseCursors
