import Netlib.Check.CampusTCPTwoTransferCurrentReverseProjectionTrace
import Netlib.Check.CampusTCPTwoTransferExchangeLoss
import Netlib.Check.CampusTCPTwoTransferRecordedFacts
import Netlib.Check.CampusTCPTwoProgressBounded

/-!
# Actual reverse completion on the same whole trace

The existing reverse bound supplies the done mode. Current whole-prefix evidence
then derives completion at that same cut, with its actual reader and history.
-/

namespace Netlib.Check.CampusTCPTwoTransferReverseResult

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)
open CampusTCPTwoTransferForwardWriteBounded (ReadWrite)
open CampusTCPTwoTransferCurrentReverseAtTrace (At)

namespace W
export CampusTCPTwoTransferMonitor (Allowed monitorAt Serviced actions check)
end W
namespace P
export CampusTCPTwoTransferCurrentReverseProjection
  (point_at history_at reverse_at local_state local_trace local_actions local_service)
end P

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance bound : Nat} {reverseLower reverseUpper : List UInt8}
variable {steps : List (Step input)} {events remainingEvents : List Event} {final : State input}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

def remaining (rw : ReadWrite initial checks routing quantum allowance reverseLower reverseUpper steps) : Nat :=
  allowance - (W.monitorAt cfg .initial steps rw.writeSlot).exchange.forward.drops.length

def legSlots (rw : ReadWrite initial checks routing quantum allowance reverseLower reverseUpper steps) (bound : Nat) : Nat :=
  CampusTCPTwoProgressBounded.boundSlots rw.written.start.reverseInitial quantum (remaining rw) bound

structure Result (rw : ReadWrite initial checks routing quantum allowance reverseLower reverseUpper steps) (bound : Nat) where
  point : At rw.written.start steps (rw.writeSlot + 1 + legSlots rw bound)
  value : CampusTCPTwoProgressEvidence.Complete rw.written.start.reverseInitial rw.written.start.reverseNative quantum
    (remaining rw) point.current (W.monitorAt cfg .initial steps (rw.writeSlot + 1 + legSlots rw bound)).exchange.reverse
  done : (W.monitorAt cfg .initial steps (rw.writeSlot + 1 + legSlots rw bound)).exchange.mode = .done
  readerRecorded : value.completed.reader ∈ (steps.drop (rw.writeSlot + 1)).take (legSlots rw bound)

variable {rw : ReadWrite initial checks routing quantum allowance reverseLower reverseUpper steps}

theorem complete_by (rw : ReadWrite initial checks routing quantum allowance reverseLower reverseUpper steps)
    (budget : allowance ≤ 2) (positive : 0 < quantum)
    (trace : Trace input cut.report.final events steps final remainingEvents)
    (actions : ∀ slot, slot < steps.length → W.Allowed cfg (CampusTCPSchedule.stateAt cut.report.final steps slot)
      (W.monitorAt cfg .initial steps slot) (CampusTCPSchedule.eventAt steps slot))
    (service : W.Serviced cfg cut.report.final .initial steps bound)
    (enough : rw.writeSlot + 1 + legSlots rw bound ≤ steps.length) : Nonempty (Result rw bound) := by
  have room : legSlots rw bound ≤ (steps.drop (rw.writeSlot + 1)).length := by rw [List.length_drop]; omega
  have localActions : CampusTCPTwoProgressProgress.Actions rw.written.start.reverseInitial rw.written.start.reverseNative
      quantum (remaining rw) (steps.drop (rw.writeSlot + 1)) := P.local_actions rw.written budget trace actions
  obtain ⟨localResult⟩ := CampusTCPTwoProgressBounded.complete_by
    (Nat.le_trans (Nat.sub_le allowance _) budget) positive (P.local_trace rw.written trace) localActions
    (P.local_service rw.written budget trace actions service) room
  obtain ⟨point⟩ := P.point_at rw.written budget trace actions enough
  have actualDone : (W.monitorAt cfg .initial steps (rw.writeSlot + 1 + legSlots rw bound)).exchange.reverse.mode = .done := by
    rw [P.reverse_at rw.written budget trace actions enough]
    exact localResult.value.mode
  obtain ⟨value⟩ := CampusTCPTwoProgressInvariant.done_evidence point.value.reverse actualDone
  have wholeDone : (W.monitorAt cfg .initial steps (rw.writeSlot + 1 + legSlots rw bound)).exchange.mode = .done := by
    rcases point.value.phase with ⟨_, active⟩ | ⟨done, _⟩
    · exact False.elim (active actualDone)
    · exact done
  exact ⟨⟨point, value, wholeDone,
    CampusTCPTwoProgressRecorded.reader_recorded value (P.history_at rw.written point)⟩⟩

theorem complete_by_checked (rw : ReadWrite initial checks routing quantum allowance reverseLower reverseUpper steps)
    (budget : allowance ≤ 2) (positive : 0 < quantum)
    (trace : Trace input cut.report.final events steps final remainingEvents)
    (actions : W.actions cfg cut.report.final .initial steps = true)
    (service : W.check cfg cut.report.final .initial steps bound = true)
    (enough : rw.writeSlot + 1 + legSlots rw bound ≤ steps.length) : Nonempty (Result rw bound) :=
  complete_by rw budget positive trace ((CampusTCPTwoTransferMonitor.actions_correct _ _ _ _).mp actions)
    ((CampusTCPTwoTransferMonitor.check_correct _ _ _ _ _).mp service) enough

theorem Result.history (result : Result rw bound) :
    result.point.current.report.steps = cut.report.steps ++ steps.take (rw.writeSlot + 1 + legSlots rw bound) :=
  result.point.history

theorem Result.reverse_history (result : Result rw bound) :
    result.point.current.report.steps = rw.written.start.boundary.write.move.after.report.steps ++
      (steps.drop (rw.writeSlot + 1)).take (legSlots rw bound) := P.history_at rw.written result.point

def Result.mixed (result : Result rw bound) :
    CampusTCPTwoTransferExchangeLoss.Reverse rw result.point.current
      (W.monitorAt cfg .initial steps (rw.writeSlot + 1 + legSlots rw bound)).exchange.reverse := by
  unfold CampusTCPTwoTransferExchangeLoss.Reverse
  rw [CampusTCPTwoTransferExchangeLoss.remaining_at_write]
  exact result.value

theorem Result.reader_slot (result : Result rw bound) :
    ∃ slot, rw.writeSlot < slot ∧ slot < rw.writeSlot + 1 + legSlots rw bound ∧
      steps[slot]? = some result.value.completed.reader := by
  obtain ⟨slot, selected⟩ := List.mem_iff_getElem?.mp result.readerRecorded
  rw [List.getElem?_take] at selected
  by_cases inside : slot < legSlots rw bound
  · rw [ite_eq_left inside, List.getElem?_drop] at selected
    exact ⟨rw.writeSlot + 1 + slot, by omega, by omega, selected⟩
  · rw [ite_eq_right inside] at selected
    cases selected

theorem Result.read_bytes (result : Result rw bound) :
    result.value.completed.reader.result.read = reverseLower ++ reverseUpper := result.value.completed.returned

theorem Result.read_event (result : Result rw bound) :
    result.value.completed.reader.event = .read sender (reverseLower ++ reverseUpper).length := by
  have other : sender.other.other = sender := by cases sender <;> rfl
  simpa only [other] using result.value.completed.event

theorem start_compliant (prior : cut.report.compliant = true) :
    rw.written.start.boundary.write.move.after.report.compliant = true := by
  have healthy : (CampusTCPTwoTransferMonitor.observe cfg
      (W.monitorAt cfg .initial steps rw.writeSlot) rw.written.actual).mode ≠ .invalid := by
    rw [rw.written.start.boundary.observed]
    exact rw.written.point.value.finished ▸ (by decide)
  exact rw.written.start.boundary.recorded.compliant healthy prior

theorem Result.read_permissions (result : Result rw bound) (prior : cut.report.compliant = true)
    (index : Nat) (byte : UInt8) (selected : (reverseLower ++ reverseUpper)[index]? = some byte) :
    ∃ origin : CampusTCPTwoProgressReadSuffix.SuffixReadOrigin result.value.completed index byte,
      Nonempty (CampusTCPTwoProgressWriteOrigins.SelectedWriteOrigin rw.written.start.reverseInitial
        origin.attempt origin.read.origin.localIndex byte) ∧
        CampusTCPRoundOrigins.ServicePermissions origin.delivery.service.joint.step origin.delivery.receive.receipt.served :=
  result.value.read_permissions (start_compliant prior) index byte selected

end Netlib.Check.CampusTCPTwoTransferReverseResult
