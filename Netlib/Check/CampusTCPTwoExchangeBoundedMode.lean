import Netlib.Check.CampusTCPTwoExchangeForwardBounded
import Netlib.Check.CampusTCPTwoExchangeWriteBounded
import Netlib.Check.CampusTCPTwoExchangeReverseBounded
import Netlib.Check.CampusTCPTwoExchangeBoundSetup
import Netlib.Check.CampusTCPTwoExchangeRecorded
import Netlib.Check.CampusTCPTwoExchangeSlices
import Netlib.Check.CampusTCPTwoExchangePhaseOrder
import Netlib.Check.CampusTCPTwoExchangeWriteHandoff

/-!
# One deadline for the actual forward/write/reverse trace

Each phase uses a restriction of the one whole service condition.
The reverse initial state comes from the actual intervening write.
-/

namespace Netlib.Check.CampusTCPTwoExchangeBoundedMode

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart

namespace M
export CampusTCPTwoExchangeMonitor (Monitor monitorAt observe Allowed Serviced)
end M
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance bound : Nat}
variable {reverseLower reverseUpper : List UInt8}
variable {events remaining : List Event} {steps : List (Step input)} {final : State input}

local notation "cfg" => CampusTCPTwoExchangeSetup.config initial native quantum allowance reverseLower reverseUpper
local notation "NF" => CampusTCPTwoExchangeBoundSetup.forwardSlots initial quantum allowance bound
local notation "NR" => CampusTCPTwoExchangeBoundSetup.reverseSlots initial quantum allowance bound
local notation "N" => CampusTCPTwoExchangeBoundSetup.boundSlots initial quantum allowance bound

theorem done_by (budget : allowance ≤ 2) (positive : 0 < quantum)
    (endpointReserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (gatewayReserve : CampusTCPTwoReverseGeometry.Initial initial reverseLower reverseUpper)
    (lowerNonempty : reverseLower ≠ []) (upperNonempty : reverseUpper ≠ [])
    (trace : Trace input cut.report.final events steps final remaining)
    (actions : CampusTCPTwoExchangeRecorded.Actions initial native quantum allowance reverseLower reverseUpper steps)
    (service : M.Serviced cfg cut.report.final .initial steps bound) (enough : N ≤ steps.length) :
    (M.monitorAt cfg .initial steps N).mode = .done := by
  have total : NF + bound + NR ≤ steps.length := enough
  have healthy := CampusTCPTwoExchangeRecorded.trace_healthy budget endpointReserve gatewayReserve
    lowerNonempty upperNonempty trace actions
  obtain ⟨f, fBound, fExit, fFirst⟩ := CampusTCPTwoExchangeForwardBounded.first_exit_by budget positive
    trace actions service (by omega : NF ≤ steps.length)
  change f ≤ NF at fBound
  have fWithin : f ≤ steps.length := by omega
  obtain ⟨_, fMode⟩ := CampusTCPTwoExchangePhaseOrder.forward_first_exit trace rfl fWithin fExit fFirst (healthy f fWithin)
  have fTrace := CampusTCPTraceSlices.Trace.drop trace fWithin
  have fService := CampusTCPTwoExchangeSlices.service_drop fWithin service
  have writeRoom : bound ≤ (steps.drop f).length := by rw [List.length_drop]; omega
  obtain ⟨w, wBound, wExit, wFirst⟩ := CampusTCPTwoExchangeWriteBounded.first_exit_by fMode fTrace fService writeRoom
  have wWithin : w ≤ (steps.drop f).length := by omega
  have wHealthy : (M.monitorAt cfg (M.monitorAt cfg .initial steps f) (steps.drop f) w).mode ≠ .invalid := by
    rw [CampusTCPTwoExchangeSlices.monitorAt_drop]
    exact healthy (f + w) (by omega)
  obtain ⟨wPositive, wMode⟩ := CampusTCPTwoExchangePhaseOrder.write_first_exit fTrace fMode wWithin wExit wFirst wHealthy
  rw [CampusTCPTwoExchangeSlices.monitorAt_drop] at wMode
  let g := f + w
  let p := f + (w - 1)
  have nextSlot : p + 1 = g := by dsimp only [p, g]; omega
  have gWithin : g ≤ steps.length := by dsimp only [g]; omega
  have pWithin : p < steps.length := by omega
  have pMode : (M.monitorAt cfg .initial steps p).mode = .needWrite := by
    have selected := wFirst (w - 1) (by omega)
    rw [CampusTCPTwoExchangeSlices.monitorAt_drop] at selected
    exact selected
  obtain ⟨beforeCut, beforeFinal, _, ⟨beforeEvidence⟩⟩ := CampusTCPTwoExchangeRecorded.trace_at budget
    endpointReserve gatewayReserve lowerNonempty upperNonempty trace actions p (by omega)
  obtain ⟨forward⟩ := CampusTCPTwoExchangeRecorded.needWrite_value beforeEvidence pMode
  obtain ⟨actual, found, actualBefore, actualEvent, actualAfter⟩ := CampusTCPSchedule.Trace.at trace p pWithin
  have allowed : M.Allowed cfg beforeCut.report.final (M.monitorAt cfg .initial steps p) actual.event := by
    rw [beforeFinal, actualEvent]
    exact actions p pWithin
  have afterMode : (M.observe cfg (M.monitorAt cfg .initial steps p) actual).mode = .reverse := by
    rw [← CampusTCPTwoExchangeMonitor.monitorAt_next _ _ _ found, nextSlot]
    exact wMode
  obtain ⟨start, forwardFrame, reverseInitial⟩ := CampusTCPTwoExchangeWriteHandoff.starts_of_exit forward pMode
    endpointReserve gatewayReserve lowerNonempty upperNonempty actual (actualBefore.trans beforeFinal.symm) allowed afterMode
  have observedAt : M.observe cfg (M.monitorAt cfg .initial steps p) actual = M.monitorAt cfg .initial steps g := by
    rw [← CampusTCPTwoExchangeMonitor.monitorAt_next _ _ _ found, nextSlot]
  have startFinal : start.boundary.write.move.after.report.final = S.stateAt cut.report.final steps g := by
    rw [start.boundary.write.move.final, actualAfter, nextSlot]
  have placed : (M.monitorAt cfg .initial steps g).mode = .reverse ∧
      (M.monitorAt cfg .initial steps g).forward = (M.monitorAt cfg .initial steps p).forward ∧
      (M.monitorAt cfg .initial steps g).reverse = .initial :=
    ⟨wMode, by rw [← observedAt]; exact forwardFrame, by rw [← observedAt]; exact reverseInitial⟩
  have reverseTrace : Trace input start.boundary.write.move.after.report.final
      ((steps.drop g).map (·.event)) (steps.drop g) final [] := by
    rw [startFinal]
    exact CampusTCPTraceSlices.Trace.drop trace gWithin
  have reverseActions : ∀ slot, slot < (steps.drop g).length → M.Allowed cfg
      (S.stateAt start.boundary.write.move.after.report.final (steps.drop g) slot)
      (M.monitorAt cfg (M.monitorAt cfg .initial steps g) (steps.drop g) slot) (S.eventAt (steps.drop g) slot) := by
    rw [startFinal]
    exact CampusTCPTwoExchangeSlices.actions_drop gWithin actions
  have reverseService : M.Serviced cfg start.boundary.write.move.after.report.final
      (M.monitorAt cfg .initial steps g) (steps.drop g) bound := by
    rw [startFinal]
    exact CampusTCPTwoExchangeSlices.service_drop gWithin service
  have reverseBound := CampusTCPTwoExchangeBoundSetup.actual_reverse_le (bound := bound) start
  have reverseRoom : CampusTCPTwoProgressRecoveryBounded.boundSlots start.reverseInitial quantum
      (allowance - (M.monitorAt cfg .initial steps p).forward.drops.length) bound ≤ (steps.drop g).length := by
    rw [List.length_drop]
    dsimp only [g]
    omega
  obtain ⟨r, rBound, rExit, rFirst⟩ := CampusTCPTwoExchangeReverseBounded.first_exit_by start placed budget positive
    reverseTrace reverseActions reverseService reverseRoom
  have rWithin : r ≤ (steps.drop g).length := by omega
  have rHealthy : (M.monitorAt cfg (M.monitorAt cfg .initial steps g) (steps.drop g) r).mode ≠ .invalid := by
    rw [CampusTCPTwoExchangeSlices.monitorAt_drop]
    exact healthy (g + r) (by rw [List.length_drop] at rWithin; omega)
  obtain ⟨_, done⟩ := CampusTCPTwoExchangePhaseOrder.reverse_first_exit reverseTrace placed.1 rWithin rExit rFirst rHealthy
  rw [CampusTCPTwoExchangeSlices.monitorAt_drop] at done
  apply CampusTCPTwoExchangePhaseOrder.done_persistent trace (first := g + r) (last := N) _ enough done (healthy N enough)
  change g + r ≤ NF + bound + NR
  dsimp only [g]
  omega

end Netlib.Check.CampusTCPTwoExchangeBoundedMode
