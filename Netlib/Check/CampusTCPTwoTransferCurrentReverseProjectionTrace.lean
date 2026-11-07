import Netlib.Check.CampusTCPTwoTransferCurrentReverseProjection
import Netlib.Check.CampusTCPTwoTransferCurrentReverseAtTrace

/-!
# Local reverse actions and service from the whole trace

The actual write fixes the suffix offset and local initial state.
Current evidence derives every projection through reverse and done.
-/

namespace Netlib.Check.CampusTCPTwoTransferCurrentReverseProjection

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferEvidence (Evidence ReadAdvanced)
open CampusTCPTwoTransferCurrentReverseBounded (WriteAt)
open CampusTCPTwoTransferCurrentReverseAt (reverseConfig)
open CampusTCPTwoTransferCurrentReverseAtTrace (At)
open CampusTCPTwoTransferLocatedCore (config)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut readBefore : Cut input complete} {sender : Actor} {gateway location : Gateway}
variable {lower upper : List UInt8} {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {readMonitor : W.Monitor} {readActual : Step input}
variable {evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper readBefore readMonitor location}
variable {forward : ReadAdvanced evidence readActual}
variable {steps : List (Step input)} {writeSlot slot bound : Nat}
variable {events remaining : List Event} {final : State input}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

variable (write : WriteAt forward steps writeSlot)

include write in
theorem offset_le : writeSlot + 1 ≤ steps.length := by
  obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp write.found
  omega

theorem point_at (budget : allowance ≤ 2) (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ index, index < steps.length → W.Allowed cfg (S.stateAt cut.report.final steps index)
      (W.monitorAt cfg .initial steps index) (S.eventAt steps index)) (within : writeSlot + 1 + slot ≤ steps.length) :
    Nonempty (At write.start steps (writeSlot + 1 + slot)) :=
  CampusTCPTwoTransferCurrentReverseAtTrace.prefix_at (At.ofWriteAt write) budget trace actions (by omega) within

theorem history_at (point : At write.start steps (writeSlot + 1 + slot)) :
    point.current.report.steps = write.start.boundary.write.move.after.report.steps ++ (steps.drop (writeSlot + 1)).take slot := by
  rw [point.history, write.history, List.append_assoc, ← List.take_add]

theorem reverse_at (budget : allowance ≤ 2) (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ index, index < steps.length → W.Allowed cfg (S.stateAt cut.report.final steps index)
      (W.monitorAt cfg .initial steps index) (S.eventAt steps index)) (within : writeSlot + 1 + slot ≤ steps.length) :
    (W.monitorAt cfg .initial steps (writeSlot + 1 + slot)).exchange.reverse =
      L.monitorAt (reverseConfig write.start) .initial (steps.drop (writeSlot + 1)) slot := by
  obtain ⟨point⟩ := point_at write budget trace actions within
  exact CampusTCPTwoTransferCurrentReverseProjectionHistory.local_monitorAt point.value.reverse write.history point.history within

theorem local_state (slot : Nat) :
    S.stateAt write.start.boundary.write.move.after.report.final (steps.drop (writeSlot + 1)) slot =
      S.stateAt cut.report.final steps (writeSlot + 1 + slot) := by
  rw [write.final, CampusTCPTraceSlices.stateAt_drop]

theorem local_trace (trace : Trace input cut.report.final events steps final remaining) :
    Trace input write.start.boundary.write.move.after.report.final
      ((steps.drop (writeSlot + 1)).map (·.event)) (steps.drop (writeSlot + 1)) final [] := by
  have selected := CampusTCPTraceSlices.Trace.drop trace (offset_le write)
  rw [← write.final] at selected
  exact selected

theorem pending_at (budget : allowance ≤ 2) (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ index, index < steps.length → W.Allowed cfg (S.stateAt cut.report.final steps index)
      (W.monitorAt cfg .initial steps index) (S.eventAt steps index)) (within : writeSlot + 1 + slot ≤ steps.length) :
    W.pendingAt cfg cut.report.final .initial steps (writeSlot + 1 + slot) =
      (L.pendingAt (reverseConfig write.start) write.start.boundary.write.move.after.report.final .initial
        (steps.drop (writeSlot + 1)) slot).map tag := by
  obtain ⟨point⟩ := point_at write budget trace actions within
  have selected := pending_current point.value
  rw [point.final, reverse_at write budget trace actions within] at selected
  unfold W.pendingAt L.pendingAt
  rw [local_state write]
  exact selected

theorem local_actions (budget : allowance ≤ 2) (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ index, index < steps.length → W.Allowed cfg (S.stateAt cut.report.final steps index)
      (W.monitorAt cfg .initial steps index) (S.eventAt steps index)) :
    ∀ index, index < (steps.drop (writeSlot + 1)).length →
      L.Allowed (reverseConfig write.start)
        (S.stateAt write.start.boundary.write.move.after.report.final (steps.drop (writeSlot + 1)) index)
        (L.monitorAt (reverseConfig write.start) .initial (steps.drop (writeSlot + 1)) index)
        (S.eventAt (steps.drop (writeSlot + 1)) index) := by
  intro index inside
  have globalInside : writeSlot + 1 + index < steps.length := by rw [List.length_drop] at inside; omega
  obtain ⟨point⟩ := point_at write budget trace actions (by omega : writeSlot + 1 + index ≤ steps.length)
  obtain ⟨actual, _, _, event, _⟩ := CampusTCPSchedule.Trace.at trace (writeSlot + 1 + index) globalInside
  have currentAllowed : W.Allowed cfg point.current.report.final
      (W.monitorAt cfg .initial steps (writeSlot + 1 + index)) actual.event := by
    rw [point.final, event]
    exact actions _ globalInside
  have selected := point.value.local_allowed currentAllowed
  rw [point.final, event, reverse_at write budget trace actions (by omega : writeSlot + 1 + index ≤ steps.length)] at selected
  rw [local_state write, CampusTCPTraceSlices.eventAt_drop]
  exact selected

theorem local_service (budget : allowance ≤ 2) (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ index, index < steps.length → W.Allowed cfg (S.stateAt cut.report.final steps index)
      (W.monitorAt cfg .initial steps index) (S.eventAt steps index))
    (service : W.Serviced cfg cut.report.final .initial steps bound) :
    L.Serviced (reverseConfig write.start) write.start.boundary.write.move.after.report.final .initial
      (steps.drop (writeSlot + 1)) bound := by
  change Theory.BoundedServiceCheck.Serviced (steps.drop (writeSlot + 1)).length _ _ _ bound
  apply Theory.BoundedServiceRestriction.restrict service (offset := writeSlot + 1)
    (by rw [List.length_drop]; have within := offset_le write; omega) tag tag_injective id
  · intro index inside
    exact pending_at write budget trace actions (by rw [List.length_drop] at inside; have within := offset_le write; omega)
  · intro index _
    exact (CampusTCPTraceSlices.eventAt_drop steps (writeSlot + 1) index).symm
  · intro demand event
    exact serves_tag cfg demand event

theorem local_actions_checked (budget : allowance ≤ 2) (trace : Trace input cut.report.final events steps final remaining)
    (actions : W.actions cfg cut.report.final .initial steps = true) :
    L.actions (reverseConfig write.start) write.start.boundary.write.move.after.report.final .initial
      (steps.drop (writeSlot + 1)) = true :=
  (CampusTCPTwoProgressMonitor.actions_correct _ _ _ _).mpr
    (local_actions write budget trace ((CampusTCPTwoTransferMonitor.actions_correct _ _ _ _).mp actions))

theorem local_service_checked (budget : allowance ≤ 2) (trace : Trace input cut.report.final events steps final remaining)
    (actions : W.actions cfg cut.report.final .initial steps = true)
    (service : W.check cfg cut.report.final .initial steps bound = true) :
    L.check (reverseConfig write.start) write.start.boundary.write.move.after.report.final .initial
      (steps.drop (writeSlot + 1)) bound = true :=
  (CampusTCPTwoProgressMonitor.check_correct _ _ _ _ _).mpr
    (local_service write budget trace ((CampusTCPTwoTransferMonitor.actions_correct _ _ _ _).mp actions)
      ((CampusTCPTwoTransferMonitor.check_correct _ _ _ _ _).mp service))

end Netlib.Check.CampusTCPTwoTransferCurrentReverseProjection
