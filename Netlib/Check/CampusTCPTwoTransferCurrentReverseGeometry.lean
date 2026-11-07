import Netlib.Check.CampusTCPTwoTransferCurrentReverseWrite
import Netlib.Check.CampusTCPTwoReverseGeometry

/-!
# Reverse initialization from the current post-read boundary

The completed gateway counts and endpoint cursors derive reverse geometry.
Intervening actual clocks retain the original numeric reserves and read lineage.
-/

namespace Netlib.Check.CampusTCPTwoTransferCurrentReverseGeometry

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferEvidence (Evidence ReadAdvanced)
open CampusTCPTwoTransferCurrentReverseWrite (Boundary)
open CampusTCPTwoTransferPostRead (After)

export CampusTCPTwoReverseGeometry (Initial reversePrefix)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut readBefore current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {readMonitor monitor : CampusTCPTwoTransferMonitor.Monitor} {readActual actual : Step input}
variable {evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper readBefore readMonitor location}
variable {forward : ReadAdvanced evidence readActual}
variable {value : After forward current monitor}

private theorem other_lane (session : Admission.Session) (sender : Actor) :
    session.lane sender.other.direction = session.peer sender.direction := by cases sender <;> rfl

private theorem other_peer (session : Admission.Session) (sender : Actor) :
    session.peer sender.other.direction = session.lane sender.direction := by cases sender <;> rfl

private theorem other_other (sender : Actor) : sender.other.other = sender := by cases sender <;> rfl


theorem receiver_cursor (boundary : Boundary value actual) :
    (endpoint boundary.write.move.after.endpoints sender).core.receiveNext =
      (endpoint boundary.write.move.after.endpoints sender.other).core.sendNext := by
  have peer := boundary.write.peer
  rw [other_other] at peer
  rw [peer, boundary.write.selected]
  change (endpoint current.endpoints sender).core.receiveNext =
    (endpoint current.endpoints sender.other).core.sendNext
  rw [value.senderFlight.receiveNext, CampusTCPTwoReverseCursors.closed_sendNext value.receiver]
  exact (CampusTCPTwoProgressWire.receiver_sequence initial).symm


theorem sender_cursor (boundary : Boundary value actual) :
    (endpoint boundary.write.move.after.endpoints sender.other).core.receiveNext =
      (endpoint boundary.write.move.after.endpoints sender).core.sendNext := by
  have peer := boundary.write.peer
  rw [other_other] at peer
  rw [boundary.write.selected, peer]
  change (endpoint current.endpoints sender.other).core.receiveNext =
    (endpoint current.endpoints sender).core.sendNext
  rw [CampusTCPTwoReverseCursors.closed_receiveNext value.receiver, value.senderFlight.sendNext,
    initial.geometry.receiverCursor]
  simp only [List.length_append, CampusTCPTwoProgressSender.source, CampusTCPTwoProgressSender.Stage.issued]


theorem gateway_sender_cursor (boundary : Boundary value actual) :
    (endpoint boundary.write.move.after.endpoints sender.other).core.sendNext =
      (boundary.gatewayState.session.lane sender.other.direction).base.add
        (boundary.gatewayState.session.lane sender.other.direction).highEnd := by
  rw [boundary.write.selected]
  change (endpoint current.endpoints sender.other).core.sendNext = _
  rw [CampusTCPTwoReverseCursors.closed_sendNext value.receiver, initial.geometry.receiverSequence, boundary.session,
    other_lane, value.gatewayState.peer_base, value.gatewayState.peer_highEnd]


def at_write (boundary : Boundary value actual)
    (endpointReserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (gatewayReserve : Initial initial reverseLower reverseUpper) :
    Geometry boundary.gatewayState sender.other reverseLower reverseUpper where
  «prefix» := reversePrefix initial
  acknowledged := by
    rw [other_lane, boundary.session, value.gatewayComplete.peerAck, value.gatewayState.peer_observed]
    rfl
  observed := by
    rw [other_lane, boundary.session, value.gatewayState.peer_observed]
    rfl
  highEnd := by
    rw [other_lane, boundary.session, value.gatewayState.peer_highEnd, ← initial.geometry.peerComplete]
    rfl
  senderCursor := by
    rw [gateway_sender_cursor boundary, other_lane, boundary.session,
      value.gatewayState.peer_highEnd, ← initial.geometry.peerComplete]
    rfl
  receiverCursor := by simpa only [other_other] using receiver_cursor boundary
  senderAck := by
    rw [other_peer, boundary.session, value.gatewayComplete.main_observed, value.gatewayState.gateway.identity.base]
    rw [boundary.write.selected]
    change (endpoint current.endpoints sender.other).core.receiveNext = _
    rw [CampusTCPTwoReverseCursors.closed_receiveNext value.receiver,
      initial.geometry.receiverCursor, initial.geometry.senderCursor, Seq.add_add]
  receiverSequence := by
    rw [other_other, other_peer, boundary.session, value.gatewayComplete.main_highEnd,
      value.gatewayState.gateway.identity.base]
    have peer := boundary.write.peer
    rw [other_other] at peer
    rw [peer, value.senderFlight.sendNext]
    change (endpoint cut.endpoints sender).core.sendNext.add (lower.length + upper.length) = _
    rw [initial.geometry.senderCursor, Seq.add_add, List.length_append]
  peerComplete := by
    rw [other_peer, boundary.session, value.gatewayComplete.main_observed, value.gatewayComplete.main_highEnd]
  window := by
    rw [other_lane, boundary.session]
    have reserve : reverseLower.length + reverseUpper.length ≤ CampusTCPTwoProgressGatewayPeerWindow.floor initial :=
      Nat.le_min.mpr ⟨gatewayReserve.window, by simpa only [List.length_append] using endpointReserve.receive⟩
    exact Nat.le_trans reserve value.gatewayComplete.peerWindow
  epoch := gatewayReserve.epoch

structure Started (value : After forward current monitor) (actual : Step input) where
  boundary : Boundary value actual
  lowerNonempty : reverseLower ≠ []
  upperNonempty : reverseUpper ≠ []
  geometry : Geometry boundary.gatewayState sender.other reverseLower reverseUpper


def Started.reverseInitial (start : Started value actual) :
    TwoWriteInitial start.boundary.write.move.after sender.other .standby reverseLower reverseUpper where
  basis := start.boundary.basis
  lowerNonempty := start.lowerNonempty
  upperNonempty := start.upperNonempty
  write := start.boundary.batch
  senderState := start.boundary.senderState
  receiverState := by simpa only [other_other] using start.boundary.receiverState
  gatewayState := start.boundary.gatewayState
  geometry := start.geometry


def Started.reverseNative (start : Started value actual) :
    NativeEnv start.boundary.write.move.after .standby start.reverseInitial.gatewayState.session.entry := start.boundary.native


theorem Started.reverse_ingress (start : Started value actual) :
    start.reverseNative.ingress = checks.ingress .standby := start.boundary.nativeIngress


theorem Started.writer (start : Started value actual) : start.reverseInitial.write.writer = start.boundary.write.operation :=
  start.boundary.batchWriter


theorem Started.reverse_recovery (start : Started value actual) :
    start.reverseInitial.senderState.idle.recovery =
      { initial.receiverState.idle.recovery with now := (endpoint current.endpoints sender.other).now } := by
  apply Option.some.inj
  exact start.reverseInitial.senderState.idle.runtime.symm.trans (start.boundary.recovery.trans
    (value.receiver.runtime.trans
      (congrArg (fun recovery : Recovery.State => some recovery) value.receiver.recovery_fields)))


theorem Started.reverse_rto (start : Started value actual) :
    start.reverseInitial.senderState.idle.recovery.rto = initial.receiverState.idle.recovery.rto := by
  have same := congrArg Recovery.State.rto start.reverse_recovery
  exact same


theorem Started.reverse_estimator (start : Started value actual) :
    start.reverseInitial.senderState.idle.recovery.estimator = initial.receiverState.idle.recovery.estimator := by
  have same := congrArg Recovery.State.estimator start.reverse_recovery
  exact same


theorem Started.receiver_recovery (start : Started value actual) :
    start.reverseInitial.receiverState.idle.recovery = value.senderFlight.recovery := by
  apply Option.some.inj
  have peer := start.boundary.write.peer
  rw [other_other] at peer
  have selected : (endpoint start.boundary.write.move.after.endpoints sender).recovery = some value.senderFlight.recovery := by
    rw [peer]
    exact value.senderFlight.runtime
  have runtime : (endpoint start.boundary.write.move.after.endpoints sender).recovery =
      some start.reverseInitial.receiverState.idle.recovery := by
    simpa only [other_other] using start.reverseInitial.receiverState.idle.runtime
  exact runtime.symm.trans selected


theorem start_at (value : After forward current monitor)
    (endpointReserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (gatewayReserve : Initial initial reverseLower reverseUpper)
    (lowerNonempty : reverseLower ≠ []) (upperNonempty : reverseUpper ≠ []) :
    ∃ actual, Nonempty (Started value actual) := by
  obtain ⟨actual, ⟨boundary⟩⟩ := CampusTCPTwoTransferCurrentReverseWrite.write_at value endpointReserve
  exact ⟨actual, ⟨⟨boundary, lowerNonempty, upperNonempty, at_write boundary endpointReserve gatewayReserve⟩⟩⟩


theorem start_actual (value : After forward current monitor)
    (endpointReserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (gatewayReserve : Initial initial reverseLower reverseUpper)
    (lowerNonempty : reverseLower ≠ []) (upperNonempty : reverseUpper ≠ [])
    (actual : Step input) (before : actual.before = current.report.final)
    (event : actual.event = .write sender.other (reverseLower ++ reverseUpper)) : Nonempty (Started value actual) := by
  obtain ⟨boundary⟩ := CampusTCPTwoTransferCurrentReverseWrite.write_actual value endpointReserve actual before event
  exact ⟨⟨boundary, lowerNonempty, upperNonempty, at_write boundary endpointReserve gatewayReserve⟩⟩

end Netlib.Check.CampusTCPTwoTransferCurrentReverseGeometry
