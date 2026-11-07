import Netlib.Check.CampusTCPTwoTransferLocatedCore
import Netlib.Check.CampusTCPTwoTransferWork
import Netlib.Check.CampusTCPTwoProgressOriginalPath

/-!
# Preparation state across a planned transfer

An early lower ingress loss retains its actual source and cause.
The upper bytes remain pending until their actual send.
-/

namespace Netlib.Check.CampusTCPTwoTransferPreparationState

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)

namespace M
export CampusTCPTwoProgressMonitor (Lane)
end M
namespace W
export CampusTCPTwoTransferMonitor (Monitor)
end W
namespace S
export CampusTCPTwoProgressSender (Original)
end S
namespace L
export CampusTCPTwoTransferLoss (Book Loss)
end L
namespace O
export CampusTCPTwoProgressOriginalPath (source)
end O
namespace P
export CampusTCPTwoTransferPaths (DataIngress)
end P

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor}

structure Written (initial : TwoWriteInitial cut sender gateway lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (routing : Routing cut gateway)
    (quantum allowance : Nat) (reverseLower reverseUpper : List UInt8)
    (current : Cut input complete) (monitor : W.Monitor) (location : Gateway) where
  core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location .written .empty
  exchange : monitor.exchange.mode = .forward
  mode : monitor.exchange.forward.mode = .originals
  lowerPending : monitor.exchange.forward.lower.phase = .needSend
  upperPending : monitor.exchange.forward.upper.phase = .needSend
  ack : monitor.exchange.forward.ack = none
  waiting : monitor.exchange.forward.waiting = false
  retry : monitor.exchange.forward.retry.phase = .done
  retries : monitor.exchange.forward.retries = 0
  sources : CampusTCPTwoProgressReceiptSources.History initial current

def Written.ofInitial (initial : TwoWriteInitial cut sender gateway lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (routing : Routing cut gateway)
    (quantum allowance : Nat) (reverseLower reverseUpper : List UInt8)
    (primaryEmpty : cut.report.final.outstanding .primary = 0) :
    Written initial checks routing quantum allowance reverseLower reverseUpper cut .initial gateway :=
  ⟨Core.ofInitial initial checks routing quantum allowance reverseLower reverseUpper primaryEmpty,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, CampusTCPTwoProgressReceiptSources.History.ofInitial initial⟩

theorem Written.pending_bytes (value : Written initial checks routing quantum allowance reverseLower reverseUpper current monitor location) :
    (endpoint current.endpoints sender).pending = lower ++ upper := value.core.live.senderFlight.pending

theorem Written.first_send_ready (value : Written initial checks routing quantum allowance reverseLower reverseUpper current monitor location) :
    Endpoint.SendReady (endpoint current.endpoints sender) lower.length := value.core.live.senderFlight.first_send_ready

inductive LowerPath (initial : TwoWriteInitial cut sender gateway lower upper)
    (current : Cut input complete) (first : S.Original initial .lower) (lane : M.Lane) (book : L.Book initial cfg) where
  | ingress (path : P.DataIngress initial current .lower lane) (produced : path.output.produced = O.source first)
  | lost (phase : lane.phase = .done) (position : Nat) (loss : L.Loss initial cfg)
      (found : book.losses[position]? = some loss) (produced : loss.source = O.source first)
      (cause : book.cause .lower = some position)

variable {first : S.Original initial .lower}

structure PendingUpper (initial : TwoWriteInitial cut sender gateway lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (routing : Routing cut gateway)
    (quantum allowance : Nat) (reverseLower reverseUpper : List UInt8)
    (current : Cut input complete) (monitor : W.Monitor) (location : Gateway) (first : S.Original initial .lower) where
  core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location (.lower first) .empty
  exchange : monitor.exchange.mode = .forward
  mode : monitor.exchange.forward.mode = .originals
  lowerPath : LowerPath initial current first monitor.exchange.forward.lower core.losses.book
  upperPending : monitor.exchange.forward.upper.phase = .needSend
  ack : monitor.exchange.forward.ack = none
  waiting : monitor.exchange.forward.waiting = false
  retry : monitor.exchange.forward.retry.phase = .done
  retries : monitor.exchange.forward.retries = 0
  sources : CampusTCPTwoProgressReceiptSources.History initial current

variable {cfg : CampusTCPTwoTransferMonitor.Config} {lane : M.Lane} {book : L.Book initial cfg}

def LowerPath.control (path : LowerPath initial current first lane book)
    (value : CampusTCPTransferEnabled.Control current event actual) : LowerPath initial value.move.after first lane book := by
  cases path with
  | ingress path produced => exact .ingress (CampusTCPTwoTransferPaths.dataIngress_control path value) produced
  | lost phase position loss found produced cause => exact .lost phase position loss found produced cause

theorem LowerPath.phase (path : LowerPath initial current first lane book) :
    lane.phase = .dataIngress ∨ lane.phase = .done := by
  cases path with
  | ingress path _ => exact Or.inl path.phase
  | lost phase _ _ _ _ _ => exact Or.inr phase

theorem LowerPath.done_loss (path : LowerPath initial current first lane book) (done : lane.phase = .done) :
    ∃ position loss, book.losses[position]? = some loss ∧ loss.source = O.source first ∧ book.cause .lower = some position := by
  cases path with
  | ingress path _ => rw [path.phase] at done; cases done
  | lost _ position loss found produced cause => exact ⟨position, loss, found, produced, cause⟩

theorem PendingUpper.pending_bytes
    (value : PendingUpper initial checks routing quantum allowance reverseLower reverseUpper current monitor location first) :
    (endpoint current.endpoints sender).pending = upper := value.core.live.senderFlight.pending

theorem PendingUpper.sent_bytes
    (value : PendingUpper initial checks routing quantum allowance reverseLower reverseUpper current monitor location first) :
    (endpoint current.endpoints sender).core.sent = lower := value.core.live.senderFlight.sent

theorem PendingUpper.second_send_ready
    (value : PendingUpper initial checks routing quantum allowance reverseLower reverseUpper current monitor location first) :
    Endpoint.SendReady (endpoint current.endpoints sender) upper.length := value.core.live.senderFlight.second_send_ready

def PendingUpper.issued
    (value : PendingUpper initial checks routing quantum allowance reverseLower reverseUpper current monitor location first) :
    CampusTCPTwoProgressSourceHistory.Issued initial current .lower first := value.core.originals

theorem PendingUpper.lower_done_cause
    (value : PendingUpper initial checks routing quantum allowance reverseLower reverseUpper current monitor location first)
    (done : monitor.exchange.forward.lower.phase = .done) : ∃ position, value.core.losses.book.cause .lower = some position := by
  obtain ⟨position, _, _, _, chosen⟩ := value.lowerPath.done_loss done
  exact ⟨position, chosen⟩

theorem PendingUpper.lower_loss_recorded
    (value : PendingUpper initial checks routing quantum allowance reverseLower reverseUpper current monitor location first)
    (done : monitor.exchange.forward.lower.phase = .done) :
    ∃ position loss, value.core.losses.book.losses[position]? = some loss ∧ loss.source = O.source first ∧
      value.core.losses.book.cause .lower = some position ∧ loss.actual ∈ value.core.losses.suffix := by
  obtain ⟨position, loss, found, produced, chosen⟩ := value.lowerPath.done_loss done
  refine ⟨position, loss, found, produced, chosen, ?_⟩
  have member : loss.actual ∈ value.core.losses.suffix.filter CampusTCPTwoProgressLossHistory.isDrop := by
    rw [value.core.losses.dropSteps]
    exact List.mem_map.mpr ⟨loss, List.mem_of_getElem? found, rfl⟩
  exact (List.mem_filter.mp member).1

theorem PendingUpper.primary_empty
    (value : PendingUpper initial checks routing quantum allowance reverseLower reverseUpper current monitor location first) :
    current.report.final.outstanding .primary = 0 := by
  apply value.core.primaryQueue.no_tickets_zero (CampusTCPOrigins.Report.work_valid current.report)
  · rcases value.lowerPath.phase with ingress | lost
    · rw [ingress]; decide
    · rw [lost]; decide
  · rw [value.upperPending]
    decide

end Netlib.Check.CampusTCPTwoTransferPreparationState
