import Netlib.Check.CampusTCPTwoTransferOriginalRank
import Netlib.Check.CampusTCPTwoTransferOrdinaryPhase

/-!
# Original rank on ordinary actual steps

The current owner's configuration supplies the local observation.
The reserved transfer work stays fixed in ordinary control phases.
-/

namespace Netlib.Check.CampusTCPTwoTransferOriginalRank

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)
open CampusTCPTwoTransferEvidence (Evidence)

namespace W
export CampusTCPTwoTransferMonitor (Config Monitor Allowed observe ordinary controlDemand drainTicket)
end W
namespace M
export CampusTCPTwoProgressMonitor (Monitor Allowed observe nextDemand)
end M
namespace X
export CampusTCPTwoExchangeMonitor (Allowed observe)
end X

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {actual : Step input} {cfg : W.Config}

private theorem mode_beq (left right : CampusTCPTwoProgressMonitor.Mode) :
    (left == right) = decide (left = right) := by cases left <;> cases right <;> rfl

theorem ordinary_allowed (valid : monitor.mode ≠ .invalid)
    (drainless : W.drainTicket current.report.final monitor = none)
    (control : W.controlDemand monitor = none) (allowed : W.Allowed cfg current.report.final monitor actual.event) :
    X.Allowed (cfg.at current.report.final) current.report.final monitor.exchange actual.event := by
  simpa only [W.Allowed, CampusTCPTwoTransferMonitor.allowed, valid, decide_false, Bool.false_eq_true,
    ite_false, drainless, control, X.Allowed] using allowed

theorem ordinary_observe (move : Move current actual)
    (drainless : W.drainTicket current.report.final monitor = none)
    (control : W.controlDemand monitor = none) (allowed : W.Allowed cfg current.report.final monitor actual.event) :
    W.observe cfg monitor actual = W.ordinary cfg monitor actual := by
  have checked : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoTransferMonitor.allowed cfg actual.before monitor actual.event) = true := by
    rw [move.supported, move.passed, move.beforeEq]
    exact allowed
  rw [W.observe, ite_eq_left checked, move.beforeEq, drainless, control]

theorem ordinary_frame (move : Move current actual) (valid : monitor.mode ≠ .invalid)
    (forward : monitor.exchange.mode = .forward)
    (drainless : W.drainTicket current.report.final monitor = none)
    (control : W.controlDemand monitor = none) (allowed : W.Allowed cfg current.report.final monitor actual.event) :
    (W.observe cfg monitor actual).mode = .invalid ∨
      ((W.observe cfg monitor actual).mode = monitor.mode ∧
        (W.observe cfg monitor actual).exchange.forward = M.observe (cfg.at actual.before).forward monitor.exchange.forward actual) := by
  have exchangeAllowed := ordinary_allowed valid drainless control allowed
  have checked : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoExchangeMonitor.allowed (cfg.at actual.before) actual.before monitor.exchange actual.event) = true := by
    rw [move.supported, move.passed, move.beforeEq]
    exact exchangeAllowed
  rw [ordinary_observe move drainless control allowed, W.ordinary, X.observe, ite_eq_left checked, forward]
  cases localMode : (M.observe (cfg.at actual.before).forward monitor.exchange.forward actual).mode <;>
    simp only [mode_beq, localMode, reduceCtorEq, decide_false, decide_true, ite_false, ite_true]
  all_goals first
    | (solve | simp only [or_true, and_true])
    | (solve | exact Or.inl rfl)
    | (solve | exact Or.inr ⟨rfl, rfl⟩)
    | (split <;> first | exact Or.inl rfl | exact Or.inr ⟨rfl, rfl⟩)

private theorem reserve_ordinary (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (control : W.controlDemand monitor = none) (state : State input) (updated : W.Monitor)
    (same : updated.mode = monitor.mode) : reserve state updated = reserve current.report.final monitor := by
  rcases evidence.controls.ordinary_modes control with armed | finished
  · simp only [reserve, same, armed]
  · simp only [reserve, same, finished]

local notation "taskConfig" => config initial checks routing quantum allowance reverseLower reverseUpper

theorem ordinary_nonincrease
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (move : Move current actual) (drainless : W.drainTicket current.report.final monitor = none)
    (control : W.controlDemand monitor = none) (allowed : W.Allowed taskConfig current.report.final monitor actual.event) :
    rank move.after.report.final (W.observe taskConfig monitor actual) ≤ rank current.report.final monitor := by
  rcases ordinary_frame move evidence.healthy evidence.forward.exchange drainless control allowed with invalid | ⟨sameMode, sameForward⟩
  · simp only [rank, invalid, ne_eq, not_true_eq_false, false_and, ite_false]
    exact Nat.zero_le _
  · by_cases originals : monitor.exchange.forward.mode = .originals
    · have nonincrease := CampusTCPTwoProgressOriginalRank.observe_nonincrease
        ((taskConfig).at actual.before).forward monitor.exchange.forward actual (shape evidence originals)
      have reserveEq := reserve_ordinary evidence control move.after.report.final _ sameMode
      rw [current_rank evidence originals]
      unfold rank
      split
      · rw [sameForward, reserveEq]
        omega
      · exact Nat.zero_le _
    · have remains := CampusTCPTwoProgressOriginalRank.observe_nonoriginal
        ((taskConfig).at actual.before).forward monitor.exchange.forward actual originals
      have after : (W.observe taskConfig monitor actual).exchange.forward.mode ≠ .originals := by
        rw [sameForward]
        exact remains
      simp only [rank, after, and_false, ite_false]
      exact Nat.zero_le _

theorem ordinary_action_strict
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (mode : monitor.exchange.forward.mode = .originals) (move : Move current actual)
    (drainless : W.drainTicket current.report.final monitor = none) (control : W.controlDemand monitor = none)
    (allowed : W.Allowed taskConfig current.report.final monitor actual.event)
    (pending : M.nextDemand ((taskConfig).at actual.before).forward actual.before monitor.exchange.forward = some demand)
    (action : CampusTCPRoundMonitor.Action) (event : actual.event = action.event) :
    rank move.after.report.final (W.observe taskConfig monitor actual) < rank current.report.final monitor := by
  have localAllowed : M.Allowed ((taskConfig).at actual.before).forward actual.before monitor.exchange.forward actual.event := by
    have ordinary := ordinary_allowed evidence.healthy drainless control allowed
    simpa only [X.Allowed, CampusTCPTwoExchangeMonitor.allowed, evidence.forward.exchange,
      M.Allowed, move.beforeEq] using ordinary
  have strict := CampusTCPTwoProgressOriginalRank.action_strict ((taskConfig).at actual.before).forward
    monitor.exchange.forward actual (shape evidence mode) mode pending move.supported move.passed localAllowed action event
  have positive := positive evidence mode
  rcases ordinary_frame move evidence.healthy evidence.forward.exchange drainless control allowed with invalid | ⟨sameMode, sameForward⟩
  · simpa only [rank, invalid, ne_eq, not_true_eq_false, false_and, ite_false] using positive
  · have reserveEq := reserve_ordinary evidence control move.after.report.final _ sameMode
    rw [current_rank evidence mode]
    unfold rank
    split
    · rw [sameForward, reserveEq]
      omega
    · have original := local_positive evidence mode
      omega

end Netlib.Check.CampusTCPTwoTransferOriginalRank
