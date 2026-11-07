import Netlib.Check.CampusTCPTwoTransferSlices
import Netlib.Check.CampusTCPTwoProgressEvidenceTrace

/-!
# The local reverse fold uses the same stored suffix

Exact report histories identify the local loss suffix.
The local evidence retains its observation through reverse and done.
-/

namespace Netlib.Check.CampusTCPTwoTransferCurrentReverseProjectionHistory

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressEvidence (Evidence)
open CampusTCPTwoProgressSetup (config)

namespace L
export CampusTCPTwoProgressMonitor (Monitor observe monitorAt)
end L

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {wholeCut reverseCut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial reverseCut sender gateway lower upper}
variable {native : NativeEnv reverseCut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : L.Monitor} {steps : List (Step input)} {offset count : Nat}

theorem suffix_eq (evidence : Evidence initial native quantum allowance current monitor)
    (startHistory : reverseCut.report.steps = wholeCut.report.steps ++ steps.take offset)
    (history : current.report.steps = wholeCut.report.steps ++ steps.take (offset + count)) :
    evidence.losses.suffix = (steps.drop offset).take count := by
  have exactHistory := evidence.losses.steps
  rw [history, startHistory, List.append_assoc] at exactHistory
  have same := List.append_cancel_left exactHistory
  rw [List.take_add] at same
  exact (List.append_cancel_left same).symm

theorem local_fold (evidence : Evidence initial native quantum allowance current monitor)
    (startHistory : reverseCut.report.steps = wholeCut.report.steps ++ steps.take offset)
    (history : current.report.steps = wholeCut.report.steps ++ steps.take (offset + count)) :
    monitor = ((steps.drop offset).take count).foldl (L.observe (config initial native quantum allowance)) .initial := by
  rw [← suffix_eq evidence startHistory history]
  exact evidence.losses.observed.symm

theorem local_monitorAt (evidence : Evidence initial native quantum allowance current monitor)
    (startHistory : reverseCut.report.steps = wholeCut.report.steps ++ steps.take offset)
    (history : current.report.steps = wholeCut.report.steps ++ steps.take (offset + count))
    (within : offset + count ≤ steps.length) :
    monitor = L.monitorAt (config initial native quantum allowance) .initial (steps.drop offset) count := by
  have length : ((steps.drop offset).take count).length = count := by
    rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega)]
  rw [local_fold evidence startHistory history, ← CampusTCPTwoProgressMonitor.monitorAt_length,
    length, CampusTCPTwoExchangeProjection.local_monitorAt_take _ _ _ (Nat.le_refl _)]

end Netlib.Check.CampusTCPTwoTransferCurrentReverseProjectionHistory
