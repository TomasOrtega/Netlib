import Netlib.Check.CampusTCPTwoTransferHandoffRTO
import Netlib.Check.CampusTCPTwoTransferEvidenceStep
import Netlib.Check.CampusTCPTwoProgressSuffixAge
import Netlib.Check.CampusTCPTwoProgressTimer

/-!
# Fixed pending cap through quiet steps, clocks and timeouts

The actual timeout doubles RTO and advances the global retry count.
Clock changes retain the current RTO.
-/

namespace Netlib.Check.CampusTCPTwoTransferRecoveryCap

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferHandoffRTO (PendingCap at_core of_core)
open CampusTCPTwoTransferEvidence (Evidence Advanced)

namespace W
export CampusTCPTwoTransferMonitor (Monitor observe)
end W
namespace G
export CampusTCPGapProgressMonitor (senderRecovery)
end G

def QuietEvent : Event → Prop
  | .assign .. | .serve .. | .dropPacket .. => True
  | _ => False

private theorem quiet_application (before : State input) (event : Event) (effect : Effect input)
    (quiet : QuietEvent event) (computed : processCore input before event = .ok effect) : effect.application = none := by
  cases event with
  | assign index ingress | serve id observed | dropPacket id =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed; rfl)
      | (cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, Except.mapError, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)
  | _ => cases quiet

private theorem Step.quiet_application (actual : Step input) (quiet : QuietEvent actual.event) : actual.result.application = none := by
  obtain ⟨effect, custody, computed, result⟩ := actual.processed
  simpa only [result] using CampusTCPTwoTransferRecoveryCap.quiet_application actual.before actual.event effect quiet computed

private theorem chain_empty {before after : Endpoint.State} (chain : ApplicationTrace.Chain before [] after) : after = before := by
  cases chain
  rfl

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance capacity : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {sent : CampusTCPTwoProgressSender.Stage initial}
variable {received : CampusTCPTwoProgressReceiver.Stage} {actual : Step input}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}
variable {evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

theorem advanced_retries (advance : Advanced evidence actual)
    (quiet : CampusTCPTwoExchangeLoss.isTimeoutOutput actual = false) :
    (W.observe cfg monitor actual).exchange.forward.retries = monitor.exchange.forward.retries := by
  have whole := (CampusTCPTwoTransferAccounting.observe_counters cfg monitor actual advance.next.healthy).2.1
  simp only [quiet, Bool.false_eq_true, ite_false, Nat.add_zero] at whole
  exact (advance.next.core.losses.wholeTimeouts.trans advance.next.core.losses.retries).symm.trans
    (whole.trans (evidence.core.losses.wholeTimeouts.trans evidence.core.losses.retries))

theorem quiet_runtime (move : Move current actual) (taskConfig : CampusTCPTwoTransferMonitor.Config)
    (quiet : QuietEvent actual.event) :
    G.senderRecovery taskConfig.exchange.forward.toConfig move.after.report.final =
      G.senderRecovery taskConfig.exchange.forward.toConfig current.report.final := by
  have chain := CampusTCPTwoProgressSuffixAge.Move.application_chain move taskConfig.exchange.forward.sender
  rw [Step.quiet_application actual quiet] at chain
  simp only [CampusTCPRecoveryRoundOrigins.localSteps] at chain
  have same := chain_empty chain
  simp only [G.senderRecovery, move.after.connection, current.connection, same]

theorem quiet_cap (prior : PendingCap cfg capacity current.report.final monitor) (move : Move current actual)
    (quiet : QuietEvent actual.event)
    (counts : (W.observe cfg monitor actual).exchange.forward.retries = monitor.exchange.forward.retries) :
    PendingCap cfg capacity move.after.report.final (W.observe cfg monitor actual) :=
  prior.same_runtime (quiet_runtime move cfg quiet) counts

theorem clock_cap {actor : Actor} {millis : Nat}
    (value : CampusTCPTwoTransferLocatedClock.Clocked core actor millis actual)
    (prior : PendingCap cfg capacity current.report.final monitor) :
    PendingCap cfg capacity value.move.after.report.final (W.observe cfg monitor actual) := by
  apply of_core value.next
  intro pending
  have runtime := CampusTCPTwoProgressTimer.clock_recovery (value.placement.frame.endpointFrame sender)
    core.live.senderFlight.runtime value.next.live.senderFlight.runtime
  rw [runtime.1, value.observed]
  exact at_core core prior pending

theorem retried_cap {part : CampusTCPTwoProgressSender.Part} {head : Recovery.Outstanding}
    {rest : List Recovery.Outstanding} {position : Nat}
    (value : CampusTCPTwoTransferTimeoutProgress.Retried core part head rest position actual)
    (prior : PendingCap cfg capacity current.report.final monitor) :
    PendingCap cfg capacity value.value.move.after.report.final (W.observe cfg monitor actual) := by
  apply of_core value.next
  intro _
  have pending : sent.ledger ≠ [] := by rw [value.value.selection.ledger]; simp
  have beforeBound := at_core core prior pending
  have runtime : value.next.live.senderFlight.recovery = Recovery.timeoutState core.live.senderFlight.recovery head rest := by
    apply Option.some.inj
    exact value.next.live.senderFlight.runtime.symm.trans (by rw [value.value.endpointsEq]; exact value.value.facts.runtime)
  rw [runtime, value.observed]
  change 2 * core.live.senderFlight.recovery.rto ≤ 2 ^ (monitor.exchange.forward.retries + 1) * capacity
  calc
    _ ≤ 2 * (2 ^ monitor.exchange.forward.retries * capacity) := Nat.mul_le_mul_left _ beforeBound
    _ = _ := by rw [Nat.pow_succ]; simp only [Nat.mul_assoc, Nat.mul_left_comm]

end Netlib.Check.CampusTCPTwoTransferRecoveryCap
