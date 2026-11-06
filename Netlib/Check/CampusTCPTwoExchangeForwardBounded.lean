import Netlib.Check.CampusTCPTwoExchangeProjection
import Netlib.Check.CampusTCPTwoExchangeSetup
import Netlib.Check.CampusTCPTwoProgressRecoveryBounded

/-!
# The forward selector exits within its actual leg bound

A prefix that stays forward inherits the one exchange service condition.
The existing local completion theorem then forces that selector to exit.
-/

namespace Netlib.Check.CampusTCPTwoExchangeForwardBounded

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart

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

theorem observe_forward_not_done {cfg : X.Config} {monitor : X.Monitor} (mode : monitor.mode = .forward)
    (actual : Step input) (stays : (X.observe cfg monitor actual).mode = .forward) :
    (X.observe cfg monitor actual).forward.mode ≠ .done := by
  intro done
  rw [CampusTCPTwoExchangeProjection.observe_forward mode actual stays] at done
  unfold X.observe at stays
  split at stays
  · simp only [mode, done,
      show (CampusTCPTwoProgressMonitor.Mode.done == .invalid) = false by decide,
      show (CampusTCPTwoProgressMonitor.Mode.done == .done) = true by rfl,
      Bool.false_eq_true, ite_false, ite_true] at stays
    cases stays
  · cases stays

theorem forward_not_done_at {cfg : X.Config} {monitor : X.Monitor} {steps : List (Step input)} {count : Nat}
    (initial : monitor.forward.mode ≠ .done) (within : count ≤ steps.length)
    (stays : ∀ slot, slot ≤ count → (X.monitorAt cfg monitor steps slot).mode = .forward) :
    (X.monitorAt cfg monitor steps count).forward.mode ≠ .done := by
  cases count with
  | zero => simpa only [CampusTCPTwoExchangeMonitor.monitorAt_zero] using initial
  | succ count =>
    have available : count < steps.length := by omega
    have found : steps[count]? = some steps[count] := List.getElem?_eq_some_iff.mpr ⟨available, rfl⟩
    rw [CampusTCPTwoExchangeMonitor.monitorAt_next _ _ _ found]
    apply observe_forward_not_done (stays count (by omega))
    rw [← CampusTCPTwoExchangeMonitor.monitorAt_next _ _ _ found]
    exact stays (count + 1) (Nat.le_refl _)

theorem first_exit {cfg : X.Config} {monitor : X.Monitor} {steps : List (Step input)} {limit : Nat}
    (found : ∃ slot, slot ≤ limit ∧ (X.monitorAt cfg monitor steps slot).mode ≠ .forward) :
    ∃ slot, slot ≤ limit ∧ (X.monitorAt cfg monitor steps slot).mode ≠ .forward ∧
      ∀ prior, prior < slot → (X.monitorAt cfg monitor steps prior).mode = .forward := by
  induction limit with
  | zero =>
    obtain ⟨slot, within, exited⟩ := found
    have zero : slot = 0 := by omega
    subst slot
    exact ⟨0, Nat.le_refl _, exited, by intro prior impossible; omega⟩
  | succ limit ih =>
    by_cases earlier : ∃ slot, slot ≤ limit ∧ (X.monitorAt cfg monitor steps slot).mode ≠ .forward
    · obtain ⟨slot, within, exited, first⟩ := ih earlier
      exact ⟨slot, by omega, exited, first⟩
    · obtain ⟨slot, within, exited⟩ := found
      have last : slot = limit + 1 := by
        by_cases before : slot ≤ limit
        · exact False.elim (earlier ⟨slot, before, exited⟩)
        · omega
      refine ⟨slot, within, exited, ?_⟩
      intro prior before
      by_cases mode : (X.monitorAt cfg monitor steps prior).mode = .forward
      · exact mode
      · exact False.elim (earlier ⟨prior, by omega, mode⟩)

variable {complete : H.Completed input.active input.passive}
variable {cut : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance bound : Nat}
variable {reverseLower reverseUpper : List UInt8}
variable {events remaining : List Event} {steps : List (Step input)} {final : State input}

local notation "cfg" => CampusTCPTwoExchangeSetup.config initial native quantum allowance reverseLower reverseUpper
local notation "NF" => CampusTCPTwoProgressRecoveryBounded.boundSlots initial quantum allowance bound

theorem exits_by (budget : allowance ≤ 2) (positive : 0 < quantum)
    (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ slot, slot < steps.length → X.Allowed cfg (S.stateAt cut.report.final steps slot)
      (X.monitorAt cfg .initial steps slot) (S.eventAt steps slot))
    (service : X.Serviced cfg cut.report.final .initial steps bound) (enough : NF ≤ steps.length) :
    ∃ slot, slot ≤ NF ∧ (X.monitorAt cfg .initial steps slot).mode ≠ .forward := by
  by_cases exits : ∃ slot, slot ≤ NF ∧ (X.monitorAt cfg .initial steps slot).mode ≠ .forward
  · exact exits
  · have stays : ∀ slot, slot ≤ NF → (X.monitorAt cfg .initial steps slot).mode = .forward := by
      intro slot within
      by_cases mode : (X.monitorAt cfg .initial steps slot).mode = .forward
      · exact mode
      · exact False.elim (exits ⟨slot, within, mode⟩)
    have localActions : CampusTCPTwoProgressProgress.Actions initial native quantum allowance (steps.take NF) :=
      CampusTCPTwoExchangeProjection.forward_actions enough stays actions
    have localService : CampusTCPTwoProgressMonitor.Serviced (CampusTCPTwoProgressSetup.config initial native quantum allowance)
        cut.report.final .initial (steps.take NF) bound :=
      CampusTCPTwoExchangeProjection.forward_service enough stays service
    have room : NF ≤ (steps.take NF).length := by
      rw [List.length_take, Nat.min_eq_left enough]
      exact Nat.le_refl _
    obtain ⟨_, _, ⟨completed⟩⟩ := CampusTCPTwoProgressRecoveryBounded.completes_by budget positive
      (CampusTCPSchedule.Trace.take trace NF enough) localActions localService room
    have done : (L.monitorAt (CampusTCPTwoProgressSetup.config initial native quantum allowance) .initial steps NF).mode = .done := by
      have done := completed.mode
      change (L.monitorAt _ .initial (steps.take NF) NF).mode = .done at done
      rw [CampusTCPTwoExchangeProjection.local_monitorAt_take _ _ _ (Nat.le_refl _)] at done
      exact done
    have notDone : (X.monitorAt cfg .initial steps NF).forward.mode ≠ .done :=
      forward_not_done_at (by decide) enough stays
    rw [CampusTCPTwoExchangeProjection.forward_at enough stays (Nat.le_refl _)] at notDone
    exact False.elim (notDone done)

theorem exits_by_checked (budget : allowance ≤ 2) (positive : 0 < quantum)
    (trace : Trace input cut.report.final events steps final remaining)
    (actions : X.actions cfg cut.report.final .initial steps = true)
    (service : X.check cfg cut.report.final .initial steps bound = true) (enough : NF ≤ steps.length) :
    ∃ slot, slot ≤ NF ∧ (X.monitorAt cfg .initial steps slot).mode ≠ .forward :=
  exits_by budget positive trace ((CampusTCPTwoExchangeMonitor.actions_correct _ _ _ _).mp actions)
    ((CampusTCPTwoExchangeMonitor.check_correct _ _ _ _ _).mp service) enough

theorem first_exit_by (budget : allowance ≤ 2) (positive : 0 < quantum)
    (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ slot, slot < steps.length → X.Allowed cfg (S.stateAt cut.report.final steps slot)
      (X.monitorAt cfg .initial steps slot) (S.eventAt steps slot))
    (service : X.Serviced cfg cut.report.final .initial steps bound) (enough : NF ≤ steps.length) :
    ∃ slot, slot ≤ NF ∧ (X.monitorAt cfg .initial steps slot).mode ≠ .forward ∧
      ∀ prior, prior < slot → (X.monitorAt cfg .initial steps prior).mode = .forward :=
  first_exit (exits_by budget positive trace actions service enough)

end Netlib.Check.CampusTCPTwoExchangeForwardBounded
