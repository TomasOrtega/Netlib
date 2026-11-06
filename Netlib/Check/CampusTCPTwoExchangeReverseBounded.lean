import Netlib.Check.CampusTCPTwoExchangeReverseProjection
import Netlib.Check.CampusTCPTwoExchangeReverseConfig
import Netlib.Check.CampusTCPTwoProgressRecoveryBounded

/-!
# The reverse selector exits within its actual leg bound

The reverse leg starts at the same actual write boundary.
Its stopped prefix inherits the one whole-exchange service condition.
-/

namespace Netlib.Check.CampusTCPTwoExchangeReverseBounded

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressEvidence (Complete)
open CampusTCPTwoReverseGeometry (Started)

namespace X
export CampusTCPTwoExchangeMonitor (Config Monitor observe monitorAt Allowed Serviced actions check)
end X
namespace L
export CampusTCPTwoProgressMonitor (Monitor observe monitorAt)
end L
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

variable {input : Input}

theorem reverse_not_done_at {cfg : X.Config} {monitor : X.Monitor} {steps : List (Step input)} {count : Nat}
    (initial : monitor.reverse.mode ≠ .done) (within : count ≤ steps.length)
    (stays : ∀ slot, slot ≤ count → (X.monitorAt cfg monitor steps slot).mode = .reverse) :
    (X.monitorAt cfg monitor steps count).reverse.mode ≠ .done := by
  cases count with
  | zero => simpa only [CampusTCPTwoExchangeMonitor.monitorAt_zero] using initial
  | succ count =>
    have available : count < steps.length := by omega
    have found : steps[count]? = some steps[count] := List.getElem?_eq_some_iff.mpr ⟨available, rfl⟩
    rw [CampusTCPTwoExchangeMonitor.monitorAt_next _ _ _ found]
    apply CampusTCPTwoExchangeReverseProjection.observe_reverse_active (stays count (by omega))
    rw [← CampusTCPTwoExchangeMonitor.monitorAt_next _ _ _ found]
    exact stays (count + 1) (Nat.le_refl _)

theorem first_exit {cfg : X.Config} {monitor : X.Monitor} {steps : List (Step input)} {limit : Nat}
    (found : ∃ slot, slot ≤ limit ∧ (X.monitorAt cfg monitor steps slot).mode ≠ .reverse) :
    ∃ slot, slot ≤ limit ∧ (X.monitorAt cfg monitor steps slot).mode ≠ .reverse ∧
      ∀ prior, prior < slot → (X.monitorAt cfg monitor steps prior).mode = .reverse := by
  induction limit with
  | zero =>
    obtain ⟨slot, within, exited⟩ := found
    have zero : slot = 0 := by omega
    subst slot
    exact ⟨0, Nat.le_refl _, exited, by intro prior impossible; omega⟩
  | succ limit ih =>
    by_cases earlier : ∃ slot, slot ≤ limit ∧ (X.monitorAt cfg monitor steps slot).mode ≠ .reverse
    · obtain ⟨slot, within, exited, first⟩ := ih earlier
      exact ⟨slot, by omega, exited, first⟩
    · obtain ⟨slot, within, exited⟩ := found
      have last : slot = limit + 1 := by
        by_cases before : slot ≤ limit
        · exact False.elim (earlier ⟨slot, before, exited⟩)
        · omega
      refine ⟨slot, within, exited, ?_⟩
      intro prior before
      by_cases mode : (X.monitorAt cfg monitor steps prior).mode = .reverse
      · exact mode
      · exact False.elim (earlier ⟨prior, by omega, mode⟩)

variable {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance bound : Nat}
variable {forwardMonitor : L.Monitor} {monitor : X.Monitor} {reverseLower reverseUpper : List UInt8}
variable {actual : Step input} {forward : Complete initial native quantum allowance current forwardMonitor}
variable {events remaining : List Event} {steps : List (Step input)} {final : State input}

local notation "cfg" => CampusTCPTwoExchangeSetup.config initial native quantum allowance reverseLower reverseUpper

theorem exits_by (start : Started forward reverseLower reverseUpper actual)
    (placed : monitor.mode = .reverse ∧ monitor.forward = forwardMonitor ∧ monitor.reverse = .initial)
    (budget : allowance ≤ 2) (positive : 0 < quantum)
    (trace : Trace input start.boundary.write.move.after.report.final events steps final remaining)
    (actions : ∀ slot, slot < steps.length → X.Allowed cfg
      (S.stateAt start.boundary.write.move.after.report.final steps slot)
      (X.monitorAt cfg monitor steps slot) (S.eventAt steps slot))
    (service : X.Serviced cfg start.boundary.write.move.after.report.final monitor steps bound)
    (enough : CampusTCPTwoProgressRecoveryBounded.boundSlots start.reverseInitial quantum
      (allowance - forwardMonitor.drops.length) bound ≤ steps.length) :
    ∃ slot, slot ≤ CampusTCPTwoProgressRecoveryBounded.boundSlots start.reverseInitial quantum
      (allowance - forwardMonitor.drops.length) bound ∧ (X.monitorAt cfg monitor steps slot).mode ≠ .reverse := by
  let limit := CampusTCPTwoProgressRecoveryBounded.boundSlots start.reverseInitial quantum
    (allowance - forwardMonitor.drops.length) bound
  have configuration : (cfg).reverse monitor.forward.drops.length =
      CampusTCPTwoProgressSetup.config start.reverseInitial start.reverseNative quantum (allowance - forwardMonitor.drops.length) := by
    rw [placed.2.1]
    exact (CampusTCPTwoExchangeReverseConfig.config_eq start forwardMonitor.drops.length).symm
  by_cases exits : ∃ slot, slot ≤ limit ∧ (X.monitorAt cfg monitor steps slot).mode ≠ .reverse
  · exact exits
  · have stays : ∀ slot, slot ≤ limit → (X.monitorAt cfg monitor steps slot).mode = .reverse := by
      intro slot within
      by_cases mode : (X.monitorAt cfg monitor steps slot).mode = .reverse
      · exact mode
      · exact False.elim (exits ⟨slot, within, mode⟩)
    have localActions : CampusTCPTwoProgressProgress.Actions start.reverseInitial start.reverseNative quantum
        (allowance - forwardMonitor.drops.length) (steps.take limit) := by
      simpa only [configuration, placed.2.2, CampusTCPTwoProgressProgress.Actions] using
        CampusTCPTwoExchangeReverseProjection.reverse_actions enough stays actions
    have localService : CampusTCPTwoProgressMonitor.Serviced
        (CampusTCPTwoProgressSetup.config start.reverseInitial start.reverseNative quantum (allowance - forwardMonitor.drops.length))
        start.boundary.write.move.after.report.final .initial (steps.take limit) bound := by
      simpa only [configuration, placed.2.2] using
        CampusTCPTwoExchangeReverseProjection.reverse_service enough stays service
    have room : limit ≤ (steps.take limit).length := by
      rw [List.length_take, Nat.min_eq_left enough]
      exact Nat.le_refl _
    obtain ⟨_, _, ⟨completed⟩⟩ := CampusTCPTwoProgressRecoveryBounded.completes_by
      (Nat.le_trans (Nat.sub_le allowance _) budget) positive
      (CampusTCPSchedule.Trace.take trace limit enough) localActions localService room
    have done : (L.monitorAt
        (CampusTCPTwoProgressSetup.config start.reverseInitial start.reverseNative quantum (allowance - forwardMonitor.drops.length))
        .initial steps limit).mode = .done := by
      have done := completed.mode
      change (L.monitorAt _ .initial (steps.take limit) limit).mode = .done at done
      rw [CampusTCPTwoExchangeProjection.local_monitorAt_take _ _ _ (Nat.le_refl _)] at done
      exact done
    have notDone : (X.monitorAt cfg monitor steps limit).reverse.mode ≠ .done :=
      reverse_not_done_at (by rw [placed.2.2]; decide) enough stays
    rw [CampusTCPTwoExchangeReverseProjection.reverse_at enough stays (Nat.le_refl _),
      configuration, placed.2.2] at notDone
    exact False.elim (notDone done)

theorem exits_by_checked (start : Started forward reverseLower reverseUpper actual)
    (placed : monitor.mode = .reverse ∧ monitor.forward = forwardMonitor ∧ monitor.reverse = .initial)
    (budget : allowance ≤ 2) (positive : 0 < quantum)
    (trace : Trace input start.boundary.write.move.after.report.final events steps final remaining)
    (actions : X.actions cfg start.boundary.write.move.after.report.final monitor steps = true)
    (service : X.check cfg start.boundary.write.move.after.report.final monitor steps bound = true)
    (enough : CampusTCPTwoProgressRecoveryBounded.boundSlots start.reverseInitial quantum
      (allowance - forwardMonitor.drops.length) bound ≤ steps.length) :
    ∃ slot, slot ≤ CampusTCPTwoProgressRecoveryBounded.boundSlots start.reverseInitial quantum
      (allowance - forwardMonitor.drops.length) bound ∧ (X.monitorAt cfg monitor steps slot).mode ≠ .reverse :=
  exits_by start placed budget positive trace ((CampusTCPTwoExchangeMonitor.actions_correct _ _ _ _).mp actions)
    ((CampusTCPTwoExchangeMonitor.check_correct _ _ _ _ _).mp service) enough

theorem first_exit_by (start : Started forward reverseLower reverseUpper actual)
    (placed : monitor.mode = .reverse ∧ monitor.forward = forwardMonitor ∧ monitor.reverse = .initial)
    (budget : allowance ≤ 2) (positive : 0 < quantum)
    (trace : Trace input start.boundary.write.move.after.report.final events steps final remaining)
    (actions : ∀ slot, slot < steps.length → X.Allowed cfg
      (S.stateAt start.boundary.write.move.after.report.final steps slot)
      (X.monitorAt cfg monitor steps slot) (S.eventAt steps slot))
    (service : X.Serviced cfg start.boundary.write.move.after.report.final monitor steps bound)
    (enough : CampusTCPTwoProgressRecoveryBounded.boundSlots start.reverseInitial quantum
      (allowance - forwardMonitor.drops.length) bound ≤ steps.length) :
    ∃ slot, slot ≤ CampusTCPTwoProgressRecoveryBounded.boundSlots start.reverseInitial quantum
      (allowance - forwardMonitor.drops.length) bound ∧ (X.monitorAt cfg monitor steps slot).mode ≠ .reverse ∧
      ∀ prior, prior < slot → (X.monitorAt cfg monitor steps prior).mode = .reverse :=
  first_exit (exits_by start placed budget positive trace actions service enough)

end Netlib.Check.CampusTCPTwoExchangeReverseBounded
