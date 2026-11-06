import Netlib.Check.CampusTCPTwoExchangeEvidence

namespace Netlib.Check.CampusTCPTwoExchangeEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart

namespace W
export CampusTCPTwoExchangeMonitor (Allowed observe)
end W

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {reverseLower reverseUpper : List UInt8} {monitor : M.Monitor}

private theorem local_mode_beq (left right : CampusTCPTwoProgressMonitor.Mode) :
    (left == right) = decide (left = right) := by cases left <;> cases right <;> rfl

theorem forward_step (value : L.Evidence initial native quantum allowance current monitor.forward)
    (mode : monitor.mode = .forward) (budget : allowance ≤ 2) (actual : Step input)
    (before : actual.before = current.report.final)
    (allowed : W.Allowed (CampusTCPTwoExchangeSetup.config initial native quantum allowance reverseLower reverseUpper)
      current.report.final monitor actual.event) :
    ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance reverseLower reverseUpper move.after
      (W.observe (CampusTCPTwoExchangeSetup.config initial native quantum allowance reverseLower reverseUpper) monitor actual)) := by
  let cfg := CampusTCPTwoExchangeSetup.config initial native quantum allowance reverseLower reverseUpper
  have localAllowed : CampusTCPTwoProgressMonitor.Allowed cfg.forward current.report.final monitor.forward actual.event := by
    simpa only [W.Allowed, CampusTCPTwoExchangeMonitor.allowed, mode, CampusTCPTwoProgressMonitor.Allowed] using allowed
  obtain ⟨move, ⟨next⟩⟩ := value.step budget actual before localAllowed
  have nextValue : L.Evidence initial native quantum allowance move.after
      (CampusTCPTwoProgressMonitor.observe cfg.forward monitor.forward actual) := next
  have checked : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoExchangeMonitor.allowed cfg actual.before monitor actual.event) = true := by
    rw [move.supported, move.passed, before]
    exact allowed
  have healthy := nextValue.healthy
  change ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance reverseLower reverseUpper move.after
    (CampusTCPTwoExchangeMonitor.observe cfg monitor actual))
  refine ⟨move, ?_⟩
  cases nextMode : (CampusTCPTwoProgressMonitor.observe cfg.forward monitor.forward actual).mode with
  | invalid => exact False.elim (healthy nextMode)
  | done =>
    obtain ⟨finished⟩ := CampusTCPTwoProgressInvariant.done_evidence nextValue nextMode
    simp only [CampusTCPTwoExchangeMonitor.observe, checked, mode, nextMode, local_mode_beq,
      reduceCtorEq, decide_false, decide_true, Bool.false_eq_true, ite_true, ite_false]
    exact ⟨.needWrite finished rfl⟩
  | originals | recovery | needRead =>
    simp only [CampusTCPTwoExchangeMonitor.observe, checked, mode, nextMode, local_mode_beq,
      reduceCtorEq, decide_false, Bool.false_eq_true, ite_true, ite_false]
    exact ⟨.forward nextValue (by change monitor.mode = .forward; exact mode) (by rw [nextMode]; decide)⟩

end Netlib.Check.CampusTCPTwoExchangeEvidence
