import Netlib.Check.CampusTCPTwoTransferLocatedCore
import Netlib.Check.CampusTCPTwoTransferWork

/-!
# Current forward phases at the actual gateway

Each outstanding head has current packet work, a covering ACK, or an actual loss.
Waiting removes the work alternatives and exposes unspent loss credit.
-/

namespace Netlib.Check.CampusTCPTwoTransferPhaseState

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferWork (Work DataWork OriginalLane RetryLane AckWork AckState)
open CampusTCPTwoProgressPhaseBase (Arrived)

namespace S
export CampusTCPTwoProgressSender (Part Stage)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane)
end M
namespace W
export CampusTCPTwoTransferMonitor (Monitor)
end W
namespace L
export CampusTCPTwoTransferLoss (Loss Supports)
end L

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {sent : S.Stage initial} {received : R.Stage}

inductive Debt (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (role : S.Part) where
  | cause (position : Nat) (chosen : core.losses.book.cause role = some position)
  | lower (same : role = .lower) (work : Work initial checks current location .lower monitor.exchange.forward.lower)
  | upper (same : role = .upper) (work : Work initial checks current location .upper monitor.exchange.forward.upper)
  | retry (work : Work initial checks current location role monitor.exchange.forward.retry)
  | ack (lane : M.Lane) (pending : monitor.exchange.forward.ack = some lane)
      (work : AckWork checks core.live lane)
      (covered : role.offset lower + (role.bytes lower upper).length ≤ (received.bytes lower upper).length)

variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}
variable {part : S.Part}

theorem Debt.waiting_cause (debt : Debt core part)
    (lowerDone : monitor.exchange.forward.lower.phase = .done) (upperDone : monitor.exchange.forward.upper.phase = .done)
    (retryDone : monitor.exchange.forward.retry.phase = .done) (ackNone : monitor.exchange.forward.ack = none) :
    ∃ position, core.losses.book.cause part = some position := by
  cases debt with
  | cause position chosen => exact ⟨position, chosen⟩
  | lower _ work => exact False.elim (work.not_done lowerDone)
  | upper _ work => exact False.elim (work.not_done upperDone)
  | retry work => exact False.elim (work.not_done retryDone)
  | ack lane pending _ _ => rw [ackNone] at pending; cases pending

theorem Debt.waiting_loss (debt : Debt core part)
    (lowerDone : monitor.exchange.forward.lower.phase = .done) (upperDone : monitor.exchange.forward.upper.phase = .done)
    (retryDone : monitor.exchange.forward.retry.phase = .done) (ackNone : monitor.exchange.forward.ack = none) :
    ∃ position loss, core.losses.book.cause part = some position ∧ core.losses.book.losses[position]? = some loss ∧
      L.Supports loss part ∧ position ∉ core.losses.book.positions := by
  obtain ⟨position, chosen⟩ := debt.waiting_cause lowerDone upperDone retryDone ackNone
  obtain ⟨loss, found, support, unused⟩ := core.losses.valid.cause position chosen
  exact ⟨position, loss, chosen, found, support, unused⟩

theorem Debt.waiting_credit (debt : Debt core part)
    (lowerDone : monitor.exchange.forward.lower.phase = .done) (upperDone : monitor.exchange.forward.upper.phase = .done)
    (retryDone : monitor.exchange.forward.retry.phase = .done) (ackNone : monitor.exchange.forward.ack = none) :
    monitor.exchange.forward.retries < allowance := by
  obtain ⟨position, chosen⟩ := debt.waiting_cause lowerDone upperDone retryDone ackNone
  exact core.timeout_credit part position chosen

structure Active (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received) where
  exchange : monitor.exchange.mode = .forward
  mode : monitor.exchange.forward.mode = .originals ∨ monitor.exchange.forward.mode = .recovery
  preparing : sent.preparing = false
  nonempty : sent.ledger ≠ []
  lowerLane : OriginalLane initial checks current core.live.gatewayState received .lower monitor.exchange.forward.lower
  upperLane : OriginalLane initial checks current core.live.gatewayState received .upper monitor.exchange.forward.upper
  retry : RetryLane initial checks current core.live.gatewayState sent monitor.exchange.forward.retry
  ack : AckState checks core.live monitor.exchange.forward.ack
  originals : monitor.exchange.forward.mode = .originals →
    monitor.exchange.forward.retry.phase = .done ∧ monitor.exchange.forward.waiting = false ∧ monitor.exchange.forward.retries = 0
  recovery : monitor.exchange.forward.mode = .recovery →
    monitor.exchange.forward.lower.phase = .done ∧ monitor.exchange.forward.upper.phase = .done
  recoveryHead : monitor.exchange.forward.mode = .recovery → monitor.exchange.forward.waiting = false →
    ∀ part head rest, CampusTCPTwoProgressRetry.HeadRange sent part head rest → head.retried = true
  serial : monitor.exchange.forward.ack.isSome = true → monitor.exchange.forward.retry.phase = .done
  ackNonempty : monitor.exchange.forward.ack.isSome = true → received ≠ .empty
  ackGateway : ∀ lane, monitor.exchange.forward.ack = some lane → lane.phase = .ackLink →
    (core.live.gatewayState.gateway.session.lane sender.direction).acknowledged =
      initial.geometry.«prefix» + (received.bytes lower upper).length
  waiting : monitor.exchange.forward.waiting = true →
    monitor.exchange.forward.ack = none ∧ monitor.exchange.forward.retry.phase = .done
  runnable : monitor.exchange.forward.mode = .recovery → monitor.exchange.forward.waiting = false →
    monitor.exchange.forward.ack = none → monitor.exchange.forward.retry.phase ≠ .done
  originalOpen : monitor.exchange.forward.mode = .originals → monitor.exchange.forward.ack = none →
    ¬(monitor.exchange.forward.lower.phase = .done ∧ monitor.exchange.forward.upper.phase = .done)
  debt : ∀ part head rest, CampusTCPTwoProgressRetry.HeadRange sent part head rest → Nonempty (Debt core part)
  upperMissing : sent.retiredBytes = 0 → ¬Arrived received .upper → monitor.exchange.forward.upper.phase = .done →
    ∃ position, core.losses.book.cause .upper = some position
  zeroAck : ∀ lane, monitor.exchange.forward.ack = some lane → sent.retiredBytes = (received.bytes lower upper).length →
    core.live.senderFlight.recovery.duplicateAcks = 0
  sources : CampusTCPTwoProgressReceiptSources.History initial current

theorem Active.waiting_mode (value : Active core) (waiting : monitor.exchange.forward.waiting = true) :
    monitor.exchange.forward.mode = .recovery := by
  rcases value.mode with original | recovery
  · have quiet := (value.originals original).2.1
    rw [quiet] at waiting
    cases waiting
  · exact recovery

theorem Active.waiting_cause (value : Active core) (waiting : monitor.exchange.forward.waiting = true)
    (part : S.Part) (head : Recovery.Outstanding) (rest : List Recovery.Outstanding)
    (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest) :
    ∃ position, core.losses.book.cause part = some position := by
  obtain ⟨lowerDone, upperDone⟩ := value.recovery (value.waiting_mode waiting)
  obtain ⟨ackNone, retryDone⟩ := value.waiting waiting
  obtain ⟨debt⟩ := value.debt part head rest selected
  exact debt.waiting_cause lowerDone upperDone retryDone ackNone

theorem Active.waiting_credit (value : Active core) (waiting : monitor.exchange.forward.waiting = true)
    (part : S.Part) (head : Recovery.Outstanding) (rest : List Recovery.Outstanding)
    (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest) : monitor.exchange.forward.retries < allowance := by
  obtain ⟨position, chosen⟩ := value.waiting_cause waiting part head rest selected
  exact core.timeout_credit part position chosen

theorem Active.current_head (value : Active core) :
    ∃ part head rest, CampusTCPTwoProgressRetry.HeadRange sent part head rest := by
  cases sent with
  | written | lower => cases value.preparing
  | both first second head => exact ⟨.lower, head, [second.entry], .lower first second head⟩
  | tail first second head => exact ⟨.upper, head, [], .upper first second head⟩
  | retired first second => exact False.elim (value.nonempty rfl)

theorem Active.waiting_credit_current (value : Active core) (waiting : monitor.exchange.forward.waiting = true) :
    monitor.exchange.forward.retries < allowance := by
  obtain ⟨part, head, rest, selected⟩ := value.current_head
  exact value.waiting_credit waiting part head rest selected

theorem Active.lower_not_needSend (value : Active core) : monitor.exchange.forward.lower.phase ≠ .needSend :=
  value.lowerLane.not_needSend

theorem Active.upper_not_needSend (value : Active core) : monitor.exchange.forward.upper.phase ≠ .needSend :=
  value.upperLane.not_needSend

theorem Active.retry_not_needSend (value : Active core) : monitor.exchange.forward.retry.phase ≠ .needSend :=
  value.retry.not_needSend

end Netlib.Check.CampusTCPTwoTransferPhaseState
