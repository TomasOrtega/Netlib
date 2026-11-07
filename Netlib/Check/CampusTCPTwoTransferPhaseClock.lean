import Netlib.Check.CampusTCPTwoTransferPhaseState
import Netlib.Check.CampusTCPTwoTransferPreparationState
import Netlib.Check.CampusTCPTwoTransferLocatedClock
import Netlib.Check.CampusTCPTwoProgressGatewayRanges

namespace Netlib.Check.CampusTCPTwoTransferPhaseState

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferWork
open CampusTCPTwoTransferAdmission (rangeAt)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : CampusTCPTwoTransferMonitor.Monitor}
variable {sent : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
variable {actual : Step input} {actor : Actor} {millis : Nat}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}
variable {part : CampusTCPTwoProgressSender.Part} {lane : CampusTCPTwoProgressMonitor.Lane}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

variable (clocked : CampusTCPTwoTransferLocatedClock.Clocked core actor millis actual)

include clocked in
theorem clock_forward :
    (CampusTCPTwoTransferMonitor.observe cfg monitor actual).exchange.forward = monitor.exchange.forward := by
  rw [clocked.observed]

theorem clock_sender_recovery : clocked.next.live.senderFlight.recovery =
    { core.live.senderFlight.recovery with now := (endpoint clocked.move.after.endpoints sender).now } := by
  exact Option.some.inj (clocked.next.live.senderFlight.runtime.symm.trans
    ((clocked.placement.frame.endpointFrame sender).runtime core.live.senderFlight.runtime))

theorem clock_receiver_reaction : clocked.next.live.receiverFacts.reaction = core.live.receiverFacts.reaction := by
  exact Option.some.inj (clocked.next.live.receiverFacts.ackRuntime.symm.trans
    ((clocked.placement.frame.endpointFrame sender.other).ackReaction.trans core.live.receiverFacts.ackRuntime))

theorem clock_session : clocked.next.live.gatewayState.gateway.session = core.live.gatewayState.gateway.session := by
  have phase := clocked.next.live.gatewayState.gateway.phase
  rw [clocked.placement.frame.beforeService location, core.live.gatewayState.gateway.phase] at phase
  exact (Admission.Phase.data.inj phase).symm

theorem clock_range (part : CampusTCPTwoProgressSender.Part) :
    rangeAt clocked.next.live.gatewayState part = rangeAt core.live.gatewayState part := by
  have ranges := clocked.next.live.gatewayState.ranges.unique core.live.gatewayState.ranges initial.lowerNonempty
    (by rw [clock_session clocked])
  cases part
  · exact ranges.1
  · exact ranges.2

private def data_clock (work : DataWork initial checks current core.live.gatewayState part lane) :
    DataWork initial checks clocked.move.after clocked.next.live.gatewayState part lane := by
  cases work with
  | ingress path source => exact .ingress (path.clock clocked.placement) (source.clock clocked.placement)
  | ticket path located source => exact .ticket (path.clock clocked.placement) located (source.clock clocked.placement)
  | link path source covered =>
    exact .link (path.clock clocked.placement) (source.clock clocked.placement)
      (by rw [clock_range clocked]; exact covered)

private def original_clock (value : OriginalLane initial checks current core.live.gatewayState received part lane) :
    OriginalLane initial checks clocked.move.after clocked.next.live.gatewayState received part lane := by
  cases value with
  | active work missing => exact .active (data_clock clocked work) missing
  | done phase => exact .done phase

private def retry_clock (value : RetryLane initial checks current core.live.gatewayState sent lane) :
    RetryLane initial checks clocked.move.after clocked.next.live.gatewayState sent lane := by
  cases value with
  | active part head rest selected work => exact .active part head rest selected (data_clock clocked work)
  | done phase => exact .done phase

private def ack_clock (value : AckWork checks core.live lane) : AckWork checks clocked.next.live lane := by
  cases value with
  | pending phase queue => exact .pending phase (by rw [clock_receiver_reaction clocked]; exact queue)
  | ingress path => exact .ingress (path.clock clocked.placement)
  | ticket path located => exact .ticket (path.clock clocked.placement) located
  | link path => exact .link (path.clock clocked.placement)

def Debt.clock (debt : Debt core part) : Debt clocked.next part := by
  cases debt with
  | cause position chosen => exact .cause position (by rw [clocked.book]; exact chosen)
  | lower same work => exact .lower same (by rw [congrArg (·.lower) (clock_forward clocked)]; exact work.clock clocked.placement)
  | upper same work => exact .upper same (by rw [congrArg (·.upper) (clock_forward clocked)]; exact work.clock clocked.placement)
  | retry work => exact .retry (by rw [congrArg (·.retry) (clock_forward clocked)]; exact work.clock clocked.placement)
  | ack lane pending work covered =>
    exact .ack lane (by rw [congrArg (·.ack) (clock_forward clocked)]; exact pending) (ack_clock clocked work) covered

def Active.clock (value : Active core) : Active clocked.next := by
  have forward := clock_forward clocked
  have duplicates : clocked.next.live.senderFlight.recovery.duplicateAcks = core.live.senderFlight.recovery.duplicateAcks := by
    rw [clock_sender_recovery clocked]
  refine {
    exchange := by rw [clocked.observed]; exact value.exchange
    mode := by rw [forward]; exact value.mode
    preparing := value.preparing
    nonempty := value.nonempty
    lowerLane := by rw [congrArg (·.lower) forward]; exact original_clock clocked value.lowerLane
    upperLane := by rw [congrArg (·.upper) forward]; exact original_clock clocked value.upperLane
    retry := by rw [congrArg (·.retry) forward]; exact retry_clock clocked value.retry
    ack := ?_
    originals := by rw [forward]; exact value.originals
    recovery := by rw [forward]; exact value.recovery
    recoveryHead := by rw [forward]; exact value.recoveryHead
    serial := by rw [forward]; exact value.serial
    ackNonempty := by rw [forward]; exact value.ackNonempty
    ackGateway := by rw [congrArg (·.ack) forward, clock_session clocked]; exact value.ackGateway
    waiting := by rw [forward]; exact value.waiting
    runnable := by rw [forward]; exact value.runnable
    originalOpen := by rw [forward]; exact value.originalOpen
    debt := fun part head rest selected => ?_
    upperMissing := by rw [forward, clocked.book]; exact value.upperMissing
    zeroAck := by rw [congrArg (·.ack) forward, duplicates]; exact value.zeroAck
    sources := value.sources.non_delivery clocked.move (by rw [clocked.event]; trivial) }
  · rw [congrArg (·.ack) forward]
    cases selected : monitor.exchange.forward.ack with
    | none => exact PUnit.unit
    | some lane =>
      have work : AckWork checks core.live lane := by simpa only [AckState, selected] using value.ack
      exact ack_clock clocked work
  · obtain ⟨debt⟩ := value.debt part head rest selected
    exact ⟨debt.clock clocked⟩

end Netlib.Check.CampusTCPTwoTransferPhaseState

namespace Netlib.Check.CampusTCPTwoTransferPreparationState

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current next : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : CampusTCPTwoTransferMonitor.Monitor} {actual : Step input} {actor : Actor} {millis : Nat}
variable {first : CampusTCPTwoProgressSender.Original initial .lower}
variable {lane : CampusTCPTwoProgressMonitor.Lane} {book : CampusTCPTwoTransferLoss.Book initial cfg}

local notation "config" => CampusTCPTwoTransferLocatedCore.config initial checks routing quantum allowance reverseLower reverseUpper

def LowerPath.clock (path : LowerPath initial current first lane book)
    (placement : CampusTCPRecoveryRoundPhaseBase.At current next) : LowerPath initial next first lane book := by
  cases path with
  | ingress path produced => exact .ingress (path.clock placement) produced
  | lost phase position loss found produced cause => exact .lost phase position loss found produced cause

def Written.clock
    (state : Written initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (clocked : CampusTCPTwoTransferLocatedClock.Clocked state.core actor millis actual) :
    Written initial checks routing quantum allowance reverseLower reverseUpper clocked.move.after
      (CampusTCPTwoTransferMonitor.observe config monitor actual) location := by
  have observed := clocked.observed
  exact {
    core := clocked.next
    exchange := by rw [observed]; exact state.exchange
    mode := by rw [observed]; exact state.mode
    lowerPending := by rw [observed]; exact state.lowerPending
    upperPending := by rw [observed]; exact state.upperPending
    ack := by rw [observed]; exact state.ack
    waiting := by rw [observed]; exact state.waiting
    retry := by rw [observed]; exact state.retry
    retries := by rw [observed]; exact state.retries
    sources := state.sources.non_delivery clocked.move (by rw [clocked.event]; trivial) }

def PendingUpper.clock
    (state : PendingUpper initial checks routing quantum allowance reverseLower reverseUpper current monitor location first)
    (clocked : CampusTCPTwoTransferLocatedClock.Clocked state.core actor millis actual) :
    PendingUpper initial checks routing quantum allowance reverseLower reverseUpper clocked.move.after
      (CampusTCPTwoTransferMonitor.observe config monitor actual) location first := by
  have observed := clocked.observed
  refine {
    core := clocked.next
    exchange := by rw [observed]; exact state.exchange
    mode := by rw [observed]; exact state.mode
    lowerPath := ?_
    upperPending := by rw [observed]; exact state.upperPending
    ack := by rw [observed]; exact state.ack
    waiting := by rw [observed]; exact state.waiting
    retry := by rw [observed]; exact state.retry
    retries := by rw [observed]; exact state.retries
    sources := state.sources.non_delivery clocked.move (by rw [clocked.event]; trivial) }
  have lowerEq := congrArg (fun updated => updated.exchange.forward.lower) observed
  rw [lowerEq, clocked.book]
  exact state.lowerPath.clock clocked.placement

end Netlib.Check.CampusTCPTwoTransferPreparationState
