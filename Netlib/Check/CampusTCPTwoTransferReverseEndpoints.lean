import Netlib.Check.CampusTCPTwoTransferEvidenceRead
import Netlib.Check.CampusTCPTwoReverseEndpoints
import Netlib.Check.CampusTCPTwoReverseReserves

/-!
# Reverse endpoint guards after the same actual forward read

Initial scalar reserves reach the changed endpoint states.
The reverse write retains their actual recovery and receive histories.
-/

namespace Netlib.Check.CampusTCPTwoTransferReverseEndpoints

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferEvidence (Evidence ReadAdvanced)
open CampusTCPTwoReverseEndpoints (Reserves closed_idle closed_pending closed_pendingLimit closed_mss written_idle)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : CampusTCPTwoTransferMonitor.Monitor} {readActual actual : Step input}
variable {evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location}


def flight (forward : ReadAdvanced evidence readActual) :
    CampusTCPTwoProgressSender.Flight initial (endpoint forward.value.finalCut.endpoints sender)
      (.retired forward.first forward.second) monitor.exchange.forward.retries := forward.value.value.senderFlight


def closed (forward : ReadAdvanced evidence readActual) :
    CampusTCPTwoProgressRead.ReceiverClosed initial (endpoint forward.value.finalCut.endpoints sender.other) := forward.value.value.receiver


def sender_idle (forward : ReadAdvanced evidence readActual) :
    IdleEndpoint (endpoint forward.value.finalCut.endpoints sender) where
  recovery := (flight forward).recovery
  reaction := (flight forward).reaction
  runtime := (flight forward).runtime
  ackRuntime := (flight forward).ackRuntime
  outstanding := (flight forward).ledger
  sent := by rw [(flight forward).core]; rfl
  deadline := ((flight forward).idle rfl).1
  timedOut := ((flight forward).idle rfl).2.1
  timeoutCount := ((flight forward).idle rfl).2.2
  duplicate := forward.sender_duplicate
  valid := (flight forward).valid
  coherent := (flight forward).coherent
  prepared := (flight forward).prepared
  storage := (flight forward).storage


theorem reserves (forward : ReadAdvanced evidence readActual)
    (reserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper) :
    Reserves forward.value.finalCut sender reverseLower reverseUpper where
  pending := by rw [closed_pendingLimit (closed forward)]; exact reserve.pending
  mss := by rw [closed_mss (closed forward)]; exact reserve.mss
  window := by
    apply Nat.le_trans _ (closed forward).sendWindow_floor
    exact Nat.le_min.mpr ⟨reserve.window, by simpa only [List.length_append, CampusTCPTwoProgressReceiver.advertisedFloor] using reserve.receive⟩
  receiveSpace := Nat.le_trans reserve.receive (flight forward).advertised


def after_write_sender (forward : ReadAdvanced evidence readActual)
    (reserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (write : CampusTCPWriteEnabled.WriteMove forward.value.finalCut sender.other (reverseLower ++ reverseUpper) actual) :
    WrittenSender write.move.after sender.other reverseLower reverseUpper where
  idle := by
    rw [write.selected]
    exact written_idle (closed_idle (closed forward)) _ (by
      rw [closed_pending (closed forward), List.length_nil, Nat.zero_add]
      exact (reserves forward reserve).pending)
  pending := by rw [write.selected]; simp only [Endpoint.writeState, closed_pending (closed forward), List.nil_append]
  held := by rw [write.selected]; exact (closed forward).held
  window := by rw [write.selected]; exact (reserves forward reserve).window
  mss := by rw [write.selected]; exact (reserves forward reserve).mss


def after_write_receiver (forward : ReadAdvanced evidence readActual)
    (reserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (write : CampusTCPWriteEnabled.WriteMove forward.value.finalCut sender.other (reverseLower ++ reverseUpper) actual) :
    EmptyReceiver write.move.after sender (reverseLower ++ reverseUpper) := by
  have peer : endpoint write.move.after.endpoints sender = endpoint forward.value.finalCut.endpoints sender := by
    have other : sender.other.other = sender := by cases sender <;> rfl
    simpa only [other] using write.peer
  exact {
    idle := by rw [peer]; exact sender_idle forward
    pending := by rw [peer]; exact (flight forward).pending
    unread := by rw [peer, (flight forward).core]; exact reserve.unread
    held := by
      rw [peer]
      have store := congrArg CampusTCPTwoProgressSender.Parameters.receiveStore (flight forward).fixed
      change (endpoint forward.value.finalCut.endpoints sender).receiveStore = (endpoint cut.endpoints sender).receiveStore at store
      rw [store]
      exact initial.senderState.held
    space := by rw [peer]; exact (reserves forward reserve).receiveSpace }

end Netlib.Check.CampusTCPTwoTransferReverseEndpoints
