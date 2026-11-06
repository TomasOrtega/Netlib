import Netlib.Check.CampusTCPTwoExchangeRecorded
import Netlib.Check.CampusTCPTwoExchangeLoss

/-!
# Actual completion of both exchange directions

The two local completions share the stored reverse write.
-/

namespace Netlib.Check.CampusTCPTwoExchangeComplete

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoExchangeEvidence (Evidence)

namespace L
export CampusTCPTwoProgressEvidence (Complete)
end L
namespace M
export CampusTCPTwoExchangeMonitor (Monitor)
end M

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}

structure Complete (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (quantum allowance : Nat)
    (reverseLower reverseUpper : List UInt8) (current : Cut input complete) (monitor : M.Monitor) where
  before : Cut input complete
  forward : L.Complete initial native quantum allowance before monitor.forward
  actual : Step input
  start : CampusTCPTwoReverseGeometry.Started forward reverseLower reverseUpper actual
  reverse : L.Complete start.reverseInitial start.reverseNative quantum
    (allowance - monitor.forward.drops.length) current monitor.reverse
  mode : monitor.mode = .done

variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {reverseLower reverseUpper : List UInt8} {monitor : M.Monitor}

theorem of_done (value : Evidence initial native quantum allowance reverseLower reverseUpper current monitor)
    (mode : monitor.mode = .done) : Nonempty (Complete initial native quantum allowance reverseLower reverseUpper current monitor) := by
  obtain ⟨before, forward, actual, start, ⟨reverse⟩⟩ := CampusTCPTwoExchangeRecorded.done_value value mode
  exact ⟨⟨before, forward, actual, start, reverse, mode⟩⟩

def Complete.recorded (value : Complete initial native quantum allowance reverseLower reverseUpper current monitor) : List (Step input) :=
  CampusTCPTwoExchangeLoss.recorded value.forward.losses value.reverse.losses [value.actual]

theorem Complete.joined (value : Complete initial native quantum allowance reverseLower reverseUpper current monitor) :
    CampusTCPTwoExchangeLoss.Joined value.before value.start.boundary.write.move.after [value.actual] :=
  CampusTCPTwoExchangeLoss.Joined.of_write value.start.boundary.write.move sender.other (reverseLower ++ reverseUpper)
    value.start.boundary.write.event

theorem Complete.report_steps (value : Complete initial native quantum allowance reverseLower reverseUpper current monitor) :
    current.report.steps = cut.report.steps ++ value.recorded :=
  CampusTCPTwoExchangeLoss.report_steps (forward := value.forward.losses) (reverse := value.reverse.losses) value.joined

theorem Complete.recorded_eq (value : Complete initial native quantum allowance reverseLower reverseUpper current monitor)
    {supplied : List (Step input)} (history : current.report.steps = cut.report.steps ++ supplied) : supplied = value.recorded :=
  List.append_cancel_left (history.symm.trans value.report_steps)

theorem Complete.drop_ids (value : Complete initial native quantum allowance reverseLower reverseUpper current monitor) :
    value.recorded.filterMap CampusTCPTwoProgressLossHistory.dropID = monitor.forward.drops ++ monitor.reverse.drops :=
  CampusTCPTwoExchangeLoss.actual_drop_ids (forward := value.forward.losses) (reverse := value.reverse.losses) value.joined

theorem Complete.drop_count (value : Complete initial native quantum allowance reverseLower reverseUpper current monitor) :
    (value.recorded.filter CampusTCPTwoProgressLossHistory.isDrop).length = monitor.forward.drops.length + monitor.reverse.drops.length :=
  CampusTCPTwoExchangeLoss.actual_drop_count (forward := value.forward.losses) (reverse := value.reverse.losses) value.joined

theorem Complete.drop_bound (value : Complete initial native quantum allowance reverseLower reverseUpper current monitor) :
    (value.recorded.filter CampusTCPTwoProgressLossHistory.isDrop).length ≤ allowance :=
  CampusTCPTwoExchangeLoss.actual_drop_budget (forward := value.forward.losses) (reverse := value.reverse.losses)
    value.joined allowance value.forward.lossBound value.reverse.lossBound

theorem Complete.timeout_count (value : Complete initial native quantum allowance reverseLower reverseUpper current monitor) :
    (value.recorded.filter CampusTCPTwoExchangeLoss.isTimeoutOutput).length = monitor.forward.retries + monitor.reverse.retries :=
  CampusTCPTwoExchangeLoss.actual_timeout_count_of_healthy (forward := value.forward.losses) (reverse := value.reverse.losses)
    value.joined (by rw [value.forward.mode]; decide) (by rw [value.reverse.mode]; decide) rfl rfl

theorem Complete.timeout_le_drops (value : Complete initial native quantum allowance reverseLower reverseUpper current monitor) :
    (value.recorded.filter CampusTCPTwoExchangeLoss.isTimeoutOutput).length ≤
      (value.recorded.filter CampusTCPTwoProgressLossHistory.isDrop).length :=
  CampusTCPTwoExchangeLoss.timeout_le_actual_drops_of_healthy (forward := value.forward.losses) (reverse := value.reverse.losses)
    value.joined (by rw [value.forward.mode]; decide) (by rw [value.reverse.mode]; decide) rfl rfl

theorem Complete.timeout_bound (value : Complete initial native quantum allowance reverseLower reverseUpper current monitor) :
    (value.recorded.filter CampusTCPTwoExchangeLoss.isTimeoutOutput).length ≤ allowance :=
  Nat.le_trans value.timeout_le_drops value.drop_bound

theorem Complete.recorded_budget (value : Complete initial native quantum allowance reverseLower reverseUpper current monitor)
    {supplied : List (Step input)} (history : current.report.steps = cut.report.steps ++ supplied) :
    (supplied.filter CampusTCPTwoExchangeLoss.isTimeoutOutput).length ≤
        (supplied.filter CampusTCPTwoProgressLossHistory.isDrop).length ∧
      (supplied.filter CampusTCPTwoProgressLossHistory.isDrop).length ≤ allowance := by
  rw [value.recorded_eq history]
  exact ⟨value.timeout_le_drops, value.drop_bound⟩

end Netlib.Check.CampusTCPTwoExchangeComplete
