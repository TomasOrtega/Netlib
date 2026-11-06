import Netlib.Check.CampusTCPTwoExchangeEvidence
import Netlib.Check.CampusTCPTwoExchangeReverseConfig

/-!
# Actual reverse and completed exchange steps

The local reverse proof uses the same selector configuration and stored step.
-/

namespace Netlib.Check.CampusTCPTwoExchangeEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart

namespace ReverseM
export CampusTCPTwoExchangeMonitor (Allowed observe)
end ReverseM

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current beforeCut : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {reverseLower reverseUpper : List UInt8} {monitor : M.Monitor} {written : Step input}

private theorem local_mode_beq (left right : CampusTCPTwoProgressMonitor.Mode) :
    (left == right) = decide (left = right) := by cases left <;> cases right <;> rfl

theorem reverse_step (forward : L.Complete initial native quantum allowance beforeCut monitor.forward)
    (start : R.Started forward reverseLower reverseUpper written)
    (value : L.Evidence start.reverseInitial start.reverseNative quantum
      (allowance - monitor.forward.drops.length) current monitor.reverse)
    (mode : monitor.mode = .reverse) (budget : allowance ≤ 2) (actual : Step input)
    (before : actual.before = current.report.final)
    (allowed : ReverseM.Allowed (CampusTCPTwoExchangeSetup.config initial native quantum allowance reverseLower reverseUpper)
      current.report.final monitor actual.event) :
    ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance reverseLower reverseUpper move.after
      (ReverseM.observe (CampusTCPTwoExchangeSetup.config initial native quantum allowance reverseLower reverseUpper) monitor actual)) := by
  let cfg := CampusTCPTwoExchangeSetup.config initial native quantum allowance reverseLower reverseUpper
  have configEq := CampusTCPTwoExchangeReverseConfig.config_eq start monitor.forward.drops.length
  have localAllowed : CampusTCPTwoProgressMonitor.Allowed (cfg.reverse monitor.forward.drops.length)
      current.report.final monitor.reverse actual.event := by
    simpa only [ReverseM.Allowed, CampusTCPTwoExchangeMonitor.allowed, mode, CampusTCPTwoProgressMonitor.Allowed] using allowed
  have typedAllowed : CampusTCPTwoProgressMonitor.Allowed
      (CampusTCPTwoProgressSetup.config start.reverseInitial start.reverseNative quantum (allowance - monitor.forward.drops.length))
      current.report.final monitor.reverse actual.event := by
    rw [configEq]
    exact localAllowed
  have remaining : allowance - monitor.forward.drops.length ≤ 2 := Nat.le_trans (Nat.sub_le _ _) budget
  obtain ⟨move, ⟨next⟩⟩ := value.step remaining actual before typedAllowed
  have nextValue : L.Evidence start.reverseInitial start.reverseNative quantum
      (allowance - monitor.forward.drops.length) move.after
      (CampusTCPTwoProgressMonitor.observe (cfg.reverse monitor.forward.drops.length) monitor.reverse actual) := by
    simpa only [configEq] using next
  have checked : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoExchangeMonitor.allowed cfg actual.before monitor actual.event) = true := by
    rw [move.supported, move.passed, before]
    exact allowed
  have healthy := nextValue.healthy
  change ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance reverseLower reverseUpper move.after
    (CampusTCPTwoExchangeMonitor.observe cfg monitor actual))
  refine ⟨move, ?_⟩
  cases nextMode : (CampusTCPTwoProgressMonitor.observe (cfg.reverse monitor.forward.drops.length) monitor.reverse actual).mode with
  | invalid => exact False.elim (healthy nextMode)
  | done =>
    obtain ⟨finished⟩ := CampusTCPTwoProgressInvariant.done_evidence nextValue nextMode
    simp only [CampusTCPTwoExchangeMonitor.observe, checked, mode, nextMode, local_mode_beq,
      reduceCtorEq, decide_false, decide_true, Bool.false_eq_true, ite_true, ite_false]
    exact ⟨.done forward start finished rfl⟩
  | originals | recovery | needRead =>
    simp only [CampusTCPTwoExchangeMonitor.observe, checked, mode, nextMode, local_mode_beq,
      reduceCtorEq, decide_false, Bool.false_eq_true, ite_true, ite_false]
    exact ⟨.reverse forward start nextValue (by change monitor.mode = .reverse; exact mode) (by rw [nextMode]; decide)⟩

theorem done_step (forward : L.Complete initial native quantum allowance beforeCut monitor.forward)
    (start : R.Started forward reverseLower reverseUpper written)
    (value : L.Complete start.reverseInitial start.reverseNative quantum
      (allowance - monitor.forward.drops.length) current monitor.reverse)
    (mode : monitor.mode = .done) (budget : allowance ≤ 2) (actual : Step input)
    (before : actual.before = current.report.final)
    (allowed : ReverseM.Allowed (CampusTCPTwoExchangeSetup.config initial native quantum allowance reverseLower reverseUpper)
      current.report.final monitor actual.event) :
    ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance reverseLower reverseUpper move.after
      (ReverseM.observe (CampusTCPTwoExchangeSetup.config initial native quantum allowance reverseLower reverseUpper) monitor actual)) := by
  let cfg := CampusTCPTwoExchangeSetup.config initial native quantum allowance reverseLower reverseUpper
  have configEq := CampusTCPTwoExchangeReverseConfig.config_eq start monitor.forward.drops.length
  have clock : ∃ actor millis, actual.event = .advanceClock actor millis ∧
      CampusTCPTwoProgressMonitor.Allowed (cfg.reverse monitor.forward.drops.length)
        current.report.final monitor.reverse actual.event := by
    cases event : actual.event with
    | advanceClock actor millis =>
      refine ⟨actor, millis, rfl, ?_⟩
      simpa only [ReverseM.Allowed, CampusTCPTwoExchangeMonitor.allowed, mode, event,
        CampusTCPTwoProgressMonitor.Allowed] using allowed
    | _ => simp only [ReverseM.Allowed, CampusTCPTwoExchangeMonitor.allowed, mode, event, Bool.false_eq_true] at allowed
  obtain ⟨actor, millis, event, localAllowed⟩ := clock
  have typedAllowed : CampusTCPTwoProgressMonitor.Allowed
      (CampusTCPTwoProgressSetup.config start.reverseInitial start.reverseNative quantum (allowance - monitor.forward.drops.length))
      current.report.final monitor.reverse actual.event := by
    rw [configEq]
    exact localAllowed
  have remaining : allowance - monitor.forward.drops.length ≤ 2 := Nat.le_trans (Nat.sub_le _ _) budget
  have oldValue : L.Evidence start.reverseInitial start.reverseNative quantum
      (allowance - monitor.forward.drops.length) current monitor.reverse := .done value
  obtain ⟨move, ⟨next⟩⟩ := oldValue.step remaining actual before typedAllowed
  have observed : CampusTCPTwoProgressMonitor.observe
      (CampusTCPTwoProgressSetup.config start.reverseInitial start.reverseNative quantum (allowance - monitor.forward.drops.length))
      monitor.reverse actual = monitor.reverse :=
    CampusTCPTwoProgressMonitorFacts.observe_clock _ _ actual move.supported move.passed
      (by rw [before]; exact typedAllowed) event
  have nextValue : L.Evidence start.reverseInitial start.reverseNative quantum
      (allowance - monitor.forward.drops.length) move.after monitor.reverse := by
    simpa only [observed] using next
  obtain ⟨finished⟩ := CampusTCPTwoProgressInvariant.done_evidence nextValue value.mode
  have checked : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoExchangeMonitor.allowed cfg actual.before monitor actual.event) = true := by
    rw [move.supported, move.passed, before]
    exact allowed
  change ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance reverseLower reverseUpper move.after
    (CampusTCPTwoExchangeMonitor.observe cfg monitor actual))
  refine ⟨move, ?_⟩
  simp only [CampusTCPTwoExchangeMonitor.observe, checked, mode, ite_true]
  exact ⟨.done forward start finished (by change monitor.mode = .done; exact mode)⟩

end Netlib.Check.CampusTCPTwoExchangeEvidence
