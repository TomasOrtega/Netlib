import Netlib.Check.CampusTCPTwoReverseCursors

/-!
# The reverse initial state from actual forward completion

Initial numeric reserves supply the reverse window and sequence bounds.
The forward report supplies the endpoint, gateway, writer, and native facts.
-/

namespace Netlib.Check.CampusTCPTwoReverseGeometry

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressEvidence (Complete)
open CampusTCPTwoReverseWrite (Boundary)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : CampusTCPTwoProgressMonitor.Monitor} {reverseLower reverseUpper : List UInt8}

def reversePrefix (initial : TwoWriteInitial cut sender gateway lower upper) : Nat :=
  (initial.gatewayState.session.peer sender.direction).observed

structure Initial (initial : TwoWriteInitial cut sender gateway lower upper) (reverseLower reverseUpper : List UInt8) : Prop where
  window : reverseLower.length + reverseUpper.length ≤ (initial.gatewayState.session.peer sender.direction).peerWindow.val
  epoch : reversePrefix initial + reverseLower.length + reverseUpper.length + 2 < Seq.halfSpace

private theorem other_lane (session : Admission.Session) (sender : Actor) :
    session.lane sender.other.direction = session.peer sender.direction := by cases sender <;> rfl

private theorem other_peer (session : Admission.Session) (sender : Actor) :
    session.peer sender.other.direction = session.lane sender.direction := by cases sender <;> rfl

private theorem other_other (sender : Actor) : sender.other.other = sender := by cases sender <;> rfl

variable {actual : Step input}
variable {forward : Complete initial native quantum allowance current monitor}

def at_write (boundary : Boundary forward reverseLower reverseUpper actual)
    (endpointReserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (gatewayReserve : Initial initial reverseLower reverseUpper) :
    Geometry boundary.gatewayState sender.other reverseLower reverseUpper where
  «prefix» := reversePrefix initial
  acknowledged := by
    rw [other_lane, boundary.session, forward.gatewayComplete.peerAck, forward.completed.gatewayState.peer_observed]
    rfl
  observed := by
    rw [other_lane, boundary.session, forward.completed.gatewayState.peer_observed]
    rfl
  highEnd := by
    rw [other_lane, boundary.session, forward.completed.gatewayState.peer_highEnd, ← initial.geometry.peerComplete]
    rfl
  senderCursor := by
    rw [CampusTCPTwoReverseCursors.gateway_sender_cursor boundary, other_lane, boundary.session,
      forward.completed.gatewayState.peer_highEnd, ← initial.geometry.peerComplete]
    rfl
  receiverCursor := by
    simpa only [other_other] using CampusTCPTwoReverseCursors.receiver_cursor boundary
  senderAck := by
    rw [other_peer, boundary.session, forward.gatewayComplete.main_observed, forward.completed.gatewayState.gateway.identity.base]
    rw [boundary.write.selected]
    change (endpoint current.endpoints sender.other).core.receiveNext = _
    rw [CampusTCPTwoReverseCursors.closed_receiveNext forward.completed.receiver,
      initial.geometry.receiverCursor, initial.geometry.senderCursor, Seq.add_add]
  receiverSequence := by
    rw [other_other, other_peer, boundary.session, forward.gatewayComplete.main_highEnd,
      forward.completed.gatewayState.gateway.identity.base]
    have peer := boundary.write.peer
    rw [other_other] at peer
    rw [peer, forward.completed.senderFlight.sendNext]
    change (endpoint cut.endpoints sender).core.sendNext.add (lower.length + upper.length) = _
    rw [initial.geometry.senderCursor, Seq.add_add, List.length_append]
  peerComplete := by
    rw [other_peer, boundary.session, forward.gatewayComplete.main_observed, forward.gatewayComplete.main_highEnd]
  window := by
    rw [other_lane, boundary.session]
    have reserve : reverseLower.length + reverseUpper.length ≤ CampusTCPTwoProgressGatewayPeerWindow.floor initial :=
      Nat.le_min.mpr ⟨gatewayReserve.window, by simpa only [List.length_append] using endpointReserve.receive⟩
    exact Nat.le_trans reserve forward.gatewayComplete.peerWindow
  epoch := gatewayReserve.epoch

structure Started (forward : Complete initial native quantum allowance current monitor)
    (reverseLower reverseUpper : List UInt8) (actual : Step input) where
  boundary : Boundary forward reverseLower reverseUpper actual
  lowerNonempty : reverseLower ≠ []
  upperNonempty : reverseUpper ≠ []
  geometry : Geometry boundary.gatewayState sender.other reverseLower reverseUpper

def Started.reverseInitial (start : Started forward reverseLower reverseUpper actual) :
    TwoWriteInitial start.boundary.write.move.after sender.other gateway reverseLower reverseUpper where
  basis := start.boundary.basis
  lowerNonempty := start.lowerNonempty
  upperNonempty := start.upperNonempty
  write := start.boundary.batch
  senderState := start.boundary.senderState
  receiverState := by simpa only [other_other] using start.boundary.receiverState
  gatewayState := start.boundary.gatewayState
  geometry := start.geometry

def Started.reverseNative (start : Started forward reverseLower reverseUpper actual) :
    NativeEnv start.boundary.write.move.after gateway start.reverseInitial.gatewayState.session.entry := start.boundary.native

theorem Started.reverse_ingress (start : Started forward reverseLower reverseUpper actual) :
    start.reverseNative.ingress = native.ingress := start.boundary.nativeIngress

theorem Started.reverse_recovery (start : Started forward reverseLower reverseUpper actual) :
    start.reverseInitial.senderState.idle.recovery =
      { initial.receiverState.idle.recovery with now := (endpoint current.endpoints sender.other).now } := by
  apply Option.some.inj
  exact start.reverseInitial.senderState.idle.runtime.symm.trans (start.boundary.recovery.trans
    (forward.completed.receiver.runtime.trans
      (congrArg (fun recovery : Recovery.State => some recovery) forward.completed.receiver.recovery_fields)))

theorem Started.reverse_rto (start : Started forward reverseLower reverseUpper actual) :
    start.reverseInitial.senderState.idle.recovery.rto = initial.receiverState.idle.recovery.rto := by
  have same := congrArg Recovery.State.rto start.reverse_recovery
  exact same

theorem Started.reverse_estimator (start : Started forward reverseLower reverseUpper actual) :
    start.reverseInitial.senderState.idle.recovery.estimator = initial.receiverState.idle.recovery.estimator := by
  have same := congrArg Recovery.State.estimator start.reverse_recovery
  exact same

theorem start_at (forward : Complete initial native quantum allowance current monitor)
    (endpointReserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (gatewayReserve : Initial initial reverseLower reverseUpper)
    (lowerNonempty : reverseLower ≠ []) (upperNonempty : reverseUpper ≠ []) :
    ∃ actual : Step input, Nonempty (Started forward reverseLower reverseUpper actual) := by
  obtain ⟨actual, ⟨boundary⟩⟩ := CampusTCPTwoReverseWrite.write_initial forward endpointReserve
  exact ⟨actual, ⟨⟨boundary, lowerNonempty, upperNonempty, at_write boundary endpointReserve gatewayReserve⟩⟩⟩

theorem start_actual (forward : Complete initial native quantum allowance current monitor)
    (endpointReserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (gatewayReserve : Initial initial reverseLower reverseUpper)
    (lowerNonempty : reverseLower ≠ []) (upperNonempty : reverseUpper ≠ [])
    (actual : Step input) (before : actual.before = current.report.final)
    (event : actual.event = .write sender.other (reverseLower ++ reverseUpper)) :
    Nonempty (Started forward reverseLower reverseUpper actual) := by
  obtain ⟨boundary⟩ := CampusTCPTwoReverseWrite.write_actual forward endpointReserve actual before event
  exact ⟨⟨boundary, lowerNonempty, upperNonempty, at_write boundary endpointReserve gatewayReserve⟩⟩

end Netlib.Check.CampusTCPTwoReverseGeometry
