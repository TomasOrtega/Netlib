import Netlib.Check.CampusTCPTwoTransferPreparationSend
import Netlib.Check.CampusTCPTwoTransferPhaseState

/-!
# Active state after the actual upper send

The same send retains the lower ingress path or its earlier loss.
Both original sources and the complete receipt history remain selected.
-/

namespace Netlib.Check.CampusTCPTwoTransferPreparationSend

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)
open CampusTCPTwoTransferPreparationState (PendingUpper)
open CampusTCPTwoTransferPhaseState (Active Debt)
open CampusTCPTwoTransferWork (OriginalLane AckState)
open CampusTCPTwoProgressReadWriter (SelectedOutput)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : CampusTCPTwoTransferMonitor.Monitor} {actual : Step input}
variable {first : CampusTCPTwoProgressSender.Original initial .lower}
variable {before : PendingUpper initial checks routing quantum allowance reverseLower reverseUpper current monitor location first}

def Second.active (value : Second before actual) : Active value.next := by
  have mode : (CampusTCPTwoTransferMonitor.observe
      (config initial checks routing quantum allowance reverseLower reverseUpper) monitor actual).exchange.forward.mode = .originals := by
    rw [value.observed]
    exact before.mode
  have ack : (CampusTCPTwoTransferMonitor.observe
      (config initial checks routing quantum allowance reverseLower reverseUpper) monitor actual).exchange.forward.ack = none := by
    rw [value.observed]
    exact before.ack
  have waiting : (CampusTCPTwoTransferMonitor.observe
      (config initial checks routing quantum allowance reverseLower reverseUpper) monitor actual).exchange.forward.waiting = false := by
    rw [value.observed]
    exact before.waiting
  have retry : (CampusTCPTwoTransferMonitor.observe
      (config initial checks routing quantum allowance reverseLower reverseUpper) monitor actual).exchange.forward.retry.phase = .done := by
    rw [value.observed]
    exact before.retry
  have retries : (CampusTCPTwoTransferMonitor.observe
      (config initial checks routing quantum allowance reverseLower reverseUpper) monitor actual).exchange.forward.retries = 0 := by
    rw [value.observed]
    exact before.retries
  have lower : OriginalLane initial checks value.facts.move.after value.next.live.gatewayState .empty .lower
      (CampusTCPTwoTransferMonitor.observe
        (config initial checks routing quantum allowance reverseLower reverseUpper) monitor actual).exchange.forward.lower := by
    cases value.lowerPath with
    | ingress path produced =>
      exact .active (.ingress path ((SelectedOutput.ofIssued value.next.originals.1).reindex produced.symm))
        (by intro impossible; cases impossible)
    | lost phase _ _ _ _ _ => exact .done phase
  have upper : OriginalLane initial checks value.facts.move.after value.next.live.gatewayState .empty .upper
      (CampusTCPTwoTransferMonitor.observe
        (config initial checks routing quantum allowance reverseLower reverseUpper) monitor actual).exchange.forward.upper :=
    .active (.ingress value.path ((SelectedOutput.ofIssued value.next.originals.2).reindex value.pathSource.symm))
      (by intro impossible; cases impossible)
  refine {
    exchange := by rw [value.observed]; exact before.exchange
    mode := Or.inl mode
    preparing := rfl
    nonempty := by simp only [CampusTCPTwoProgressSender.Stage.ledger, ne_eq, List.cons_ne_nil, not_false_eq_true]
    lowerLane := lower
    upperLane := upper
    retry := .done retry
    ack := ?_
    originals := fun _ => ⟨retry, waiting, retries⟩
    recovery := ?_
    recoveryHead := ?_
    serial := ?_
    ackNonempty := ?_
    ackGateway := ?_
    waiting := ?_
    runnable := ?_
    originalOpen := ?_
    debt := ?_
    upperMissing := ?_
    zeroAck := ?_
    sources := value.sources }
  · unfold AckState
    rw [ack]
    exact PUnit.unit
  · intro recovery
    rw [mode] at recovery
    cases recovery
  · intro recovery
    rw [mode] at recovery
    cases recovery
  · intro pending
    rw [ack] at pending
    cases pending
  · intro pending
    rw [ack] at pending
    cases pending
  · intro lane pending _
    rw [ack] at pending
    cases pending
  · intro pending
    rw [waiting] at pending
    cases pending
  · intro recovery
    rw [mode] at recovery
    cases recovery
  · intro _ _ both
    have impossible := value.path.phase.symm.trans both.2
    cases impossible
  · intro part head rest selected
    cases selected
    cases value.lowerPath with
    | ingress path _ => exact ⟨Debt.lower rfl (.ingress path)⟩
    | lost _ position _ _ _ chosen => exact ⟨Debt.cause position chosen⟩
  · intro _ _ done
    have impossible := value.path.phase.symm.trans done
    cases impossible
  · intro lane pending
    rw [ack] at pending
    cases pending

end Netlib.Check.CampusTCPTwoTransferPreparationSend
