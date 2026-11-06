import Netlib.Check.CampusTCPTwoProgressEvidence
import Netlib.Check.CampusTCPTwoReverseEndpoints

/-!
# Initial reserves for the reverse bytes

Actual sender and receiver histories retain the initial window reserves.
Static endpoint fields retain the other current guards.
-/

namespace Netlib.Check.CampusTCPTwoReverseReserves

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressEvidence (Complete)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : CampusTCPTwoProgressMonitor.Monitor} {reverseLower reverseUpper : List UInt8}

structure Initial (initial : TwoWriteInitial cut sender gateway lower upper) (reverseLower reverseUpper : List UInt8) : Prop where
  unread : (endpoint cut.endpoints sender).core.received = []
  pending : (reverseLower ++ reverseUpper).length ≤ (endpoint cut.endpoints sender.other).pendingLimit
  mss : reverseLower.length + reverseUpper.length ≤ (endpoint cut.endpoints sender.other).effectiveMSS
  window : reverseLower.length + reverseUpper.length ≤ (endpoint cut.endpoints sender.other).sendWindow
  receive : (reverseLower ++ reverseUpper).length ≤ Endpoint.offeredWindow (endpoint cut.endpoints sender)

def receiverFloor (_initial : TwoWriteInitial cut sender gateway lower upper) : Nat :=
  min (endpoint cut.endpoints sender.other).sendWindow (Endpoint.offeredWindow (endpoint cut.endpoints sender))

variable (forward : Complete initial native quantum allowance current monitor)
variable (reserve : Initial initial reverseLower reverseUpper)

include forward reserve in
theorem current_pending : (reverseLower ++ reverseUpper).length ≤ (endpoint current.endpoints sender.other).pendingLimit := by
  rw [CampusTCPTwoReverseEndpoints.closed_pendingLimit forward.completed.receiver]
  exact reserve.pending

include forward reserve in
theorem current_mss : reverseLower.length + reverseUpper.length ≤ (endpoint current.endpoints sender.other).effectiveMSS := by
  rw [CampusTCPTwoReverseEndpoints.closed_mss forward.completed.receiver]
  exact reserve.mss

include forward reserve in
theorem current_receive : (reverseLower ++ reverseUpper).length ≤ Endpoint.offeredWindow (endpoint current.endpoints sender) :=
  Nat.le_trans reserve.receive forward.completed.senderFlight.advertised

include reserve in
theorem bytes_le_floor : reverseLower.length + reverseUpper.length ≤ receiverFloor initial := by
  apply Nat.le_min.mpr
  exact ⟨reserve.window, by simpa only [List.length_append] using reserve.receive⟩

include forward reserve in
theorem at_receiver_floor
    (floor : receiverFloor initial ≤ (endpoint current.endpoints sender.other).sendWindow) :
    CampusTCPTwoReverseEndpoints.Reserves current sender reverseLower reverseUpper := {
  pending := current_pending forward reserve
  window := Nat.le_trans (bytes_le_floor reserve) floor
  mss := current_mss forward reserve
  receiveSpace := current_receive forward reserve }

include forward reserve in
theorem current_window :
    reverseLower.length + reverseUpper.length ≤ (endpoint current.endpoints sender.other).sendWindow :=
  Nat.le_trans (bytes_le_floor reserve) forward.completed.receiver.sendWindow_floor

include forward reserve in
theorem at_current : CampusTCPTwoReverseEndpoints.Reserves current sender reverseLower reverseUpper := {
  pending := current_pending forward reserve
  window := current_window forward reserve
  mss := current_mss forward reserve
  receiveSpace := current_receive forward reserve }

end Netlib.Check.CampusTCPTwoReverseReserves
