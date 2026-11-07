import Netlib.Check.CampusTCPTwoTransferLossHistory
import Netlib.Check.CampusTCPTwoTransferQueue
import Netlib.Check.CampusTCPTwoTransferSources
import Netlib.Check.CampusTCPTwoTransferAdmission
import Netlib.Check.CampusTCPTwoExchangeSetup
import Netlib.Check.CampusTCPTwoProgressPhaseBase

/-!
# Current TCP progress facts at the actual gateway

The original write, recovery state, and complete suffix remain fixed references.
Gateway location and ownership can change without a new initial task.
-/

namespace Netlib.Check.CampusTCPTwoTransferLocatedCore

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferState (LiveAt)
open CampusTCPTwoTransferAdmission (rangeAt)
open CampusTCPTwoProgressPhaseBase (emitted OriginalTimes Arrived)

namespace S
export CampusTCPTwoProgressSender (Stage Part)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
namespace W
export CampusTCPTwoTransferMonitor (Monitor)
end W

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}

def sourceNative (initial : TwoWriteInitial cut sender gateway lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (routing : Routing cut gateway) :
    NativeEnv cut gateway initial.gatewayState.session.entry :=
  checks.native_env (CampusTCPTwoTransferState.Retained.refl cut) routing

def config (initial : TwoWriteInitial cut sender gateway lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (routing : Routing cut gateway)
    (quantum allowance : Nat) (reverseLower reverseUpper : List UInt8) : CampusTCPTwoTransferMonitor.Config :=
  checks.monitorConfig (CampusTCPTwoExchangeSetup.config initial (sourceNative initial checks routing)
    quantum allowance reverseLower reverseUpper)

structure Core (initial : TwoWriteInitial cut sender gateway lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (routing : Routing cut gateway)
    (quantum allowance : Nat) (reverseLower reverseUpper : List UInt8)
    (current : Cut input complete) (monitor : W.Monitor) (location : Gateway)
    (sent : S.Stage initial) (received : R.Stage) where
  live : LiveAt initial current location sent monitor.exchange.forward.retries received
  senderWindow : CampusTCPTwoProgressSenderWindow.Reserved initial (endpoint current.endpoints sender) sent
  originals : CampusTCPTwoProgressSourceHistory.Originals initial current sent
  originalTimes : OriginalTimes initial sent
  writer : CampusTCPTwoProgressWriteHistory.History initial current (emitted initial sent)
  losses : CampusTCPTwoTransferLossHistory.History initial
    (config initial checks routing quantum allowance reverseLower reverseUpper) current monitor
  lossBound : monitor.exchange.forward.drops.length ≤ allowance
  primaryQueue : CampusTCPTwoTransferQueue.Closed current.report.final monitor.exchange.forward
  retired : sent.retiredBytes ≤ (received.bytes lower upper).length
  gatewayAck : (live.gatewayState.gateway.session.lane sender.direction).acknowledged ≤
    initial.geometry.«prefix» + (received.bytes lower upper).length
  peerSettled : CampusTCPTwoTransferState.Settled live.gatewayState
  peerWindow : CampusTCPTwoTransferState.PeerReserved live.gatewayState
  covered : ∀ part, Arrived received part → (rangeAt live.gatewayState part).isSome = true
  duplicates : live.senderFlight.recovery.duplicateAcks ≤ 1
  emptyDuplicate : received = .empty → live.senderFlight.recovery.duplicateAcks = 0
  deadline : RecoveryDeadline.Bound live.senderFlight.recovery
  estimatorBeforeRetire : sent.retiredBytes = 0 → live.senderFlight.recovery.estimator = initial.senderState.idle.recovery.estimator
  rtoBeforeRetire : sent.retiredBytes = 0 →
    live.senderFlight.recovery.rto = 2 ^ monitor.exchange.forward.retries * initial.senderState.idle.recovery.rto
  rtoPending : sent.ledger ≠ [] → RTOEnvelope.Bound initial.senderState.idle.recovery.rto initial.senderState.idle.recovery.estimator
    (endpoint cut.endpoints sender).now monitor.exchange.forward.retries live.senderFlight.recovery

variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {sent : S.Stage initial} {received : R.Stage}

def Core.ofInitial (initial : TwoWriteInitial cut sender gateway lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (routing : Routing cut gateway)
    (quantum allowance : Nat) (reverseLower reverseUpper : List UInt8)
    (primaryEmpty : cut.report.final.outstanding .primary = 0) :
    Core initial checks routing quantum allowance reverseLower reverseUpper cut .initial gateway .written .empty := by
  let previous := CampusTCPTwoProgressPhaseBase.Core.ofInitial initial (sourceNative initial checks routing) quantum allowance
  exact {
    live := LiveAt.ofLive previous.live
    senderWindow := previous.senderWindow
    originals := previous.originals
    originalTimes := previous.originalTimes
    writer := previous.writer
    losses := CampusTCPTwoTransferLossHistory.History.empty initial
      (config initial checks routing quantum allowance reverseLower reverseUpper)
    lossBound := previous.lossBound
    primaryQueue := CampusTCPTwoTransferQueue.Closed.of_zero primaryEmpty
    retired := previous.retired
    gatewayAck := previous.gatewayAck
    peerSettled := previous.peerSettled
    peerWindow := previous.peerWindow
    covered := previous.covered
    duplicates := previous.duplicates
    emptyDuplicate := previous.emptyDuplicate
    deadline := previous.deadline
    estimatorBeforeRetire := previous.estimatorBeforeRetire
    rtoBeforeRetire := previous.rtoBeforeRetire
    rtoPending := previous.rtoPending }

theorem Core.retained (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received) : cut.report.steps <+: current.report.steps := core.live.anchor.retained

theorem Core.timeout_credit (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received) (role : S.Part) (position : Nat)
    (chosen : core.losses.book.cause role = some position) : monitor.exchange.forward.retries < allowance :=
  Nat.lt_of_lt_of_le (core.losses.credit chosen) core.lossBound

theorem Core.actual_budget (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received) :
    (core.losses.suffix.filter CampusTCPTwoExchangeLoss.isTimeoutOutput).length ≤
        (core.losses.suffix.filter CampusTCPTwoProgressLossHistory.isDrop).length ∧
      (core.losses.suffix.filter CampusTCPTwoProgressLossHistory.isDrop).length ≤ allowance :=
  core.losses.actual_budget (by rw [core.losses.wholeDropIDs, ← core.losses.dropIDs]; exact core.lossBound)

theorem Core.gateway_observed (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received) :
    initial.geometry.«prefix» + (received.bytes lower upper).length ≤
      (core.live.gatewayState.gateway.session.lane sender.direction).observed := by
  have observed := core.live.gatewayState.observed
  cases received with
  | empty | upperHeld =>
    simp only [CampusTCPTwoProgressReceiver.Stage.bytes, List.length_nil, Nat.add_zero]
    rw [observed]
    split <;> omega
  | lowerReleased =>
    have first := core.covered .lower trivial
    simp only [rangeAt] at first
    rw [observed, first]
    simp only [CampusTCPTwoProgressReceiver.Stage.bytes, ite_true]
    omega
  | allReleased =>
    have first := core.covered .lower trivial
    have second := core.covered .upper trivial
    simp only [rangeAt] at first second
    rw [observed, first, second]
    simp only [CampusTCPTwoProgressReceiver.Stage.bytes, List.length_append, ite_true]
    omega

end Netlib.Check.CampusTCPTwoTransferLocatedCore
