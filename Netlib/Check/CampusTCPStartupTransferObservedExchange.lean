import Netlib.Check.CampusTCPTwoTransferExchangeResult

/-!
# Transfer completion at an observed cut

The same native evidence follows every actual step. The selected cut is inside
that history and need not reach the conservative service horizon.
-/

namespace Netlib.Check.CampusTCPStartupTransferObservedExchange

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)
open CampusTCPTwoTransferForwardWriteBounded (ReadWrite)

namespace W
export CampusTCPTwoTransferMonitor (Monitor Allowed monitorAt actions)
end W
namespace F
export CampusTCPTwoTransferEvidenceHandoffTrace (At)
end F
namespace R
export CampusTCPTwoTransferEvidenceTrace (ReadAt)
end R
namespace P
export CampusTCPTwoTransferCurrentReverseBounded (At WriteAt)
end P
namespace V
export CampusTCPTwoTransferCurrentReverseAtTrace (At)
end V
namespace L
export CampusTCPTwoTransferExchangeLoss (remaining Reverse recorded)
end L

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut : Cut input complete} {sender : Actor} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender .primary lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut .primary}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {steps : List (Step input)} {events remaining : List Event} {final : State input}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

private inductive Progress (initial : TwoWriteInitial cut sender .primary lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (routing : Routing cut .primary)
    (quantum allowance : Nat) (reverseLower reverseUpper : List UInt8) (steps : List (Step input)) (slot : Nat) where
  | forward (point : F.At initial checks routing quantum allowance reverseLower reverseUpper steps slot)
  | write (readSlot : Nat) (read : R.ReadAt initial checks routing quantum allowance reverseLower reverseUpper steps readSlot)
      (ordered : readSlot < slot) (point : P.At read.advance steps slot)
  | reverse (written : ReadWrite initial checks routing quantum allowance reverseLower reverseUpper steps)
      (ordered : written.writeSlot < slot) (point : V.At written.written.start steps slot)

private theorem progress_at
    (primaryEmpty : cut.report.final.outstanding .primary = 0)
    (targetEmpty : cut.report.final.standby.transport = Checkpoint.Gateway.initial)
    (targetNS : cut.report.final.standby.guard.source.ns = (input.deployment .standby).executionNS)
    (endpointReserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (gatewayReserve : CampusTCPTwoReverseGeometry.Initial initial reverseLower reverseUpper)
    (lowerNonempty : reverseLower ≠ []) (upperNonempty : reverseUpper ≠ [])
    (budget : allowance ≤ 2) (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ index, index < steps.length → W.Allowed cfg (CampusTCPSchedule.stateAt cut.report.final steps index)
      (W.monitorAt cfg .initial steps index) (CampusTCPSchedule.eventAt steps index))
    (slot : Nat) (within : slot ≤ steps.length) :
    Nonempty (Progress initial checks routing quantum allowance reverseLower reverseUpper steps slot) := by
  induction slot with
  | zero =>
    exact ⟨.forward ⟨cut, .primary,
      by
        simpa only [CampusTCPTwoTransferMonitor.monitorAt_zero] using
          CampusTCPTwoTransferEvidence.Evidence.ofInitial initial checks routing quantum allowance reverseLower reverseUpper
            primaryEmpty targetEmpty targetNS, by simp, by simp⟩⟩
  | succ slot ih =>
    obtain ⟨point⟩ := ih (by omega)
    cases point with
    | forward point =>
      rcases CampusTCPTwoTransferEvidenceTrace.advance_at point budget trace actions (by omega) with next | read
      · obtain ⟨next⟩ := next
        exact ⟨.forward next⟩
      · obtain ⟨read⟩ := read
        exact ⟨.write slot read (by omega) (CampusTCPTwoTransferCurrentReverseBounded.At.of_read read)⟩
    | write readSlot read ordered point =>
      rcases CampusTCPTwoTransferCurrentReverseBounded.advance_at endpointReserve gatewayReserve lowerNonempty
        upperNonempty trace actions point (by omega) with next | written
      · obtain ⟨next⟩ := next
        exact ⟨.write readSlot read (by omega) next⟩
      · obtain ⟨written⟩ := written
        let rw : ReadWrite initial checks routing quantum allowance reverseLower reverseUpper steps :=
          ⟨readSlot, read, slot, written, ordered⟩
        exact ⟨.reverse rw (by dsimp [rw]; omega) (CampusTCPTwoTransferCurrentReverseAtTrace.At.ofWriteAt written)⟩
    | reverse written ordered point =>
      obtain ⟨next⟩ := CampusTCPTwoTransferCurrentReverseAtTrace.advance_at point budget trace actions (by omega)
      exact ⟨.reverse written (by omega) next⟩

structure Result (initial : TwoWriteInitial cut sender .primary lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (routing : Routing cut .primary)
    (quantum allowance : Nat) (reverseLower reverseUpper : List UInt8) (steps : List (Step input)) (slot : Nat) where
  within : slot ≤ steps.length
  readWrite : ReadWrite initial checks routing quantum allowance reverseLower reverseUpper steps
  afterWrite : readWrite.writeSlot < slot
  point : V.At readWrite.written.start steps slot
  value : L.Reverse readWrite point.current (W.monitorAt
    (config initial checks routing quantum allowance reverseLower reverseUpper) .initial steps slot).exchange.reverse
  done : (W.monitorAt (config initial checks routing quantum allowance reverseLower reverseUpper)
    .initial steps slot).exchange.mode = .done

theorem complete_at
    (primaryEmpty : cut.report.final.outstanding .primary = 0)
    (targetEmpty : cut.report.final.standby.transport = Checkpoint.Gateway.initial)
    (targetNS : cut.report.final.standby.guard.source.ns = (input.deployment .standby).executionNS)
    (endpointReserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (gatewayReserve : CampusTCPTwoReverseGeometry.Initial initial reverseLower reverseUpper)
    (lowerNonempty : reverseLower ≠ []) (upperNonempty : reverseUpper ≠ [])
    (budget : allowance ≤ 2) (trace : Trace input cut.report.final events steps final remaining)
    (actions : W.actions cfg cut.report.final .initial steps = true)
    (slot : Nat) (within : slot ≤ steps.length)
    (done : (W.monitorAt cfg .initial steps slot).exchange.mode = .done) :
    Nonempty (Result initial checks routing quantum allowance reverseLower reverseUpper steps slot) := by
  obtain ⟨progress⟩ := progress_at primaryEmpty targetEmpty targetNS endpointReserve gatewayReserve lowerNonempty
    upperNonempty budget trace ((CampusTCPTwoTransferMonitor.actions_correct _ _ _ _).mp actions) slot within
  cases progress with
  | forward point =>
    have mode := point.evidence.forward.exchange
    rw [done] at mode
    cases mode
  | write readSlot read ordered point =>
    have mode := point.value.needWrite
    rw [done] at mode
    cases mode
  | reverse written ordered point =>
    have reverseDone : (W.monitorAt cfg .initial steps slot).exchange.reverse.mode = .done := by
      rcases point.value.phase with ⟨mode, _⟩ | ⟨_, mode⟩
      · rw [done] at mode
        cases mode
      · exact mode
    obtain ⟨value⟩ := CampusTCPTwoProgressInvariant.done_evidence point.value.reverse reverseDone
    refine ⟨⟨within, written, ordered, point, ?_, done⟩⟩
    unfold L.Reverse
    rw [CampusTCPTwoTransferExchangeLoss.remaining_at_write]
    exact value

variable {slot : Nat} (result : Result initial checks routing quantum allowance reverseLower reverseUpper steps slot)

def Result.current : Cut input complete := result.point.current

def Result.monitor (_result : Result initial checks routing quantum allowance reverseLower reverseUpper steps slot) :
    W.Monitor := W.monitorAt cfg .initial steps slot

theorem Result.history : result.current.report.steps = cut.report.steps ++ steps.take slot := result.point.history

theorem Result.streams :
    result.readWrite.read.actual.result.read = lower ++ upper ∧
      result.value.completed.reader.result.read = reverseLower ++ reverseUpper :=
  ⟨result.readWrite.read.advance.value.value.returned, result.value.completed.returned⟩

theorem Result.controls :
    result.monitor.controls.map (·.1) = [.pause, .capture, .install, .clientRoute, .serverRoute, .fence, .resume] :=
  CampusTCPTwoTransferControlTrace.finished_controls result.point.value.recorded result.point.value.finished

theorem Result.recorded_eq : result.point.value.recorded.suffix = L.recorded result.readWrite result.value :=
  CampusTCPTwoTransferExchangeLoss.recorded_eq result.readWrite result.value result.point.value.recorded.history

theorem Result.accounting :
    result.monitor.exchange.drops = (steps.take slot).filterMap CampusTCPTwoProgressLossHistory.dropID ∧
      result.monitor.exchange.timeouts = ((steps.take slot).filter CampusTCPTwoExchangeLoss.isTimeoutOutput).length ∧
      result.monitor.exchange.slots = (steps.take slot).length := by
  have suffix : result.point.value.recorded.suffix = steps.take slot :=
    List.append_cancel_left (result.point.value.recorded.history.symm.trans result.history)
  simpa only [Result.monitor, suffix] using result.point.value.recorded.accounting result.point.healthy

theorem Result.shared_budget :
    result.monitor.exchange.timeouts ≤ result.monitor.exchange.drops.length ∧ result.monitor.exchange.drops.length ≤ allowance := by
  have identityCount : ((L.recorded result.readWrite result.value).filterMap CampusTCPTwoProgressLossHistory.dropID).length =
      ((L.recorded result.readWrite result.value).filter CampusTCPTwoProgressLossHistory.isDrop).length := by
    rw [CampusTCPTwoTransferExchangeLoss.actual_global_ids, CampusTCPTwoTransferExchangeLoss.actual_drop_steps,
      List.length_map, List.length_map]
  have suffix : steps.take slot = L.recorded result.readWrite result.value :=
    CampusTCPTwoTransferExchangeLoss.recorded_eq result.readWrite result.value result.history
  rw [result.accounting.1, result.accounting.2.1, suffix, identityCount]
  exact ⟨CampusTCPTwoTransferExchangeLoss.timeout_le_drops result.readWrite result.value,
    CampusTCPTwoTransferExchangeLoss.drop_budget result.readWrite result.value⟩

end Netlib.Check.CampusTCPStartupTransferObservedExchange
