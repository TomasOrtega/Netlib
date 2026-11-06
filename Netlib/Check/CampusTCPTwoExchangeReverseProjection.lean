import Netlib.Check.CampusTCPTwoExchangeProjection

/-!
# Reverse service on the same exchange prefix

The forward log stays fixed during the reverse leg.
The whole service condition restricts through the reverse demand tag.
-/

namespace Netlib.Check.CampusTCPTwoExchangeReverseProjection

open CampusTCPModel
open CampusTCPTwoExchangeProjection (local_monitorAt_take eventAt_take)

namespace X
export CampusTCPTwoExchangeMonitor
  (Config Monitor Demand observe monitorAt nextDemand pendingAt Allowed Serviced actions check)
end X
namespace L
export CampusTCPTwoProgressMonitor
  (Config Monitor observe monitorAt pendingAt Allowed Serviced actions check)
end L
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

variable {input : Input} {cfg : X.Config} {initial : State input} {monitor : X.Monitor}
variable {steps : List (Step input)} {count slot bound : Nat}

private theorem local_mode_beq (left right : CampusTCPTwoProgressMonitor.Mode) :
    (left == right) = decide (left = right) := by cases left <;> cases right <;> rfl

theorem observe_reverse (mode : monitor.mode = .reverse) (actual : Step input)
    (stays : (X.observe cfg monitor actual).mode = .reverse) :
    (X.observe cfg monitor actual).forward = monitor.forward ∧
      (X.observe cfg monitor actual).reverse = L.observe (cfg.reverse monitor.forward.drops.length) monitor.reverse actual := by
  by_cases accepted : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoExchangeMonitor.allowed cfg actual.before monitor actual.event) = true
  · cases next : (L.observe (cfg.reverse monitor.forward.drops.length) monitor.reverse actual).mode <;>
      simp only [X.observe, accepted, mode, next, local_mode_beq, reduceCtorEq, decide_false,
        decide_true, Bool.false_eq_true, ite_true, ite_false, CampusTCPTwoExchangeMonitor.Monitor.invalid] at stays ⊢
    all_goals exact ⟨rfl, trivial⟩
  · simp only [X.observe, accepted, ite_false, CampusTCPTwoExchangeMonitor.Monitor.invalid, reduceCtorEq] at stays

theorem observe_reverse_active (mode : monitor.mode = .reverse) (actual : Step input)
    (stays : (X.observe cfg monitor actual).mode = .reverse) :
    (X.observe cfg monitor actual).reverse.mode ≠ .done := by
  rw [(observe_reverse mode actual stays).2]
  intro done
  by_cases accepted : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoExchangeMonitor.allowed cfg actual.before monitor actual.event) = true
  · simp only [X.observe, accepted, mode, done, local_mode_beq, reduceCtorEq, decide_false,
      decide_true, Bool.false_eq_true, ite_true, ite_false] at stays
  · simp only [X.observe, accepted, ite_false, CampusTCPTwoExchangeMonitor.Monitor.invalid, reduceCtorEq] at stays

theorem reverse_forward_at (within : count ≤ steps.length)
    (stays : ∀ index, index ≤ count → (X.monitorAt cfg monitor steps index).mode = .reverse)
    (inside : slot ≤ count) : (X.monitorAt cfg monitor steps slot).forward = monitor.forward := by
  induction slot with
  | zero => simp only [CampusTCPTwoExchangeMonitor.monitorAt_zero]
  | succ slot ih =>
    have earlier : slot ≤ count := by omega
    have available : slot < steps.length := by omega
    have found : steps[slot]? = some steps[slot] := List.getElem?_eq_some_iff.mpr ⟨available, rfl⟩
    rw [CampusTCPTwoExchangeMonitor.monitorAt_next _ _ _ found,
      (observe_reverse (stays slot earlier) _ (by
        rw [← CampusTCPTwoExchangeMonitor.monitorAt_next _ _ _ found]
        exact stays (slot + 1) inside)).1, ih earlier]

theorem reverse_at (within : count ≤ steps.length)
    (stays : ∀ index, index ≤ count → (X.monitorAt cfg monitor steps index).mode = .reverse)
    (inside : slot ≤ count) :
    (X.monitorAt cfg monitor steps slot).reverse =
      L.monitorAt (cfg.reverse monitor.forward.drops.length) monitor.reverse steps slot := by
  induction slot with
  | zero => simp only [CampusTCPTwoExchangeMonitor.monitorAt_zero, CampusTCPTwoProgressMonitor.monitorAt_zero]
  | succ slot ih =>
    have earlier : slot ≤ count := by omega
    have available : slot < steps.length := by omega
    have found : steps[slot]? = some steps[slot] := List.getElem?_eq_some_iff.mpr ⟨available, rfl⟩
    rw [CampusTCPTwoExchangeMonitor.monitorAt_next _ _ _ found,
      (observe_reverse (stays slot earlier) _ (by
        rw [← CampusTCPTwoExchangeMonitor.monitorAt_next _ _ _ found]
        exact stays (slot + 1) inside)).2, reverse_forward_at within stays earlier, ih earlier,
      CampusTCPTwoProgressMonitor.monitorAt_next _ _ _ found]

theorem reverse_fold (within : count ≤ steps.length)
    (stays : ∀ index, index ≤ count → (X.monitorAt cfg monitor steps index).mode = .reverse) :
    (X.monitorAt cfg monitor steps count).reverse =
      (steps.take count).foldl (L.observe (cfg.reverse monitor.forward.drops.length)) monitor.reverse := by
  have length : (steps.take count).length = count := by rw [List.length_take, Nat.min_eq_left within]
  rw [← CampusTCPTwoProgressMonitor.monitorAt_length, length, local_monitorAt_take _ _ _ (Nat.le_refl _)]
  exact reverse_at within stays (Nat.le_refl _)

theorem reverse_actions (within : count ≤ steps.length)
    (stays : ∀ index, index ≤ count → (X.monitorAt cfg monitor steps index).mode = .reverse)
    (actions : ∀ index, index < steps.length → X.Allowed cfg (S.stateAt initial steps index)
      (X.monitorAt cfg monitor steps index) (S.eventAt steps index)) :
    ∀ index, index < (steps.take count).length →
      L.Allowed (cfg.reverse monitor.forward.drops.length) (S.stateAt initial (steps.take count) index)
        (L.monitorAt (cfg.reverse monitor.forward.drops.length) monitor.reverse (steps.take count) index)
        (S.eventAt (steps.take count) index) := by
  intro index inside
  have length : (steps.take count).length = count := by rw [List.length_take, Nat.min_eq_left within]
  rw [length] at inside
  have selected := actions index (by omega)
  change CampusTCPTwoExchangeMonitor.allowed _ _ _ _ = true at selected
  simp only [CampusTCPTwoExchangeMonitor.allowed, stays index (by omega)] at selected
  rw [reverse_forward_at within stays (by omega), reverse_at within stays (by omega)] at selected
  rw [CampusTCPTraceSlices.stateAt_take _ _ (by omega : index ≤ count),
    local_monitorAt_take _ _ _ (by omega : index ≤ count), eventAt_take _ inside]
  exact selected

theorem reverse_service (within : count ≤ steps.length)
    (stays : ∀ index, index ≤ count → (X.monitorAt cfg monitor steps index).mode = .reverse)
    (service : X.Serviced cfg initial monitor steps bound) :
    L.Serviced (cfg.reverse monitor.forward.drops.length) initial monitor.reverse (steps.take count) bound := by
  have length : (steps.take count).length = count := by rw [List.length_take, Nat.min_eq_left within]
  change Theory.BoundedServiceCheck.Serviced (steps.take count).length _ _ _ bound
  rw [length]
  apply Theory.BoundedServiceRestriction.restrict service (offset := 0) (by omega)
    CampusTCPTwoExchangeMonitor.Demand.reverse (fun _ _ same => CampusTCPTwoExchangeMonitor.Demand.reverse.inj same) id
  · intro index inside
    simp only [Nat.zero_add, X.pendingAt, L.pendingAt, X.nextDemand, stays index inside]
    rw [reverse_forward_at within stays inside, reverse_at within stays inside,
      CampusTCPTraceSlices.stateAt_take _ _ inside, local_monitorAt_take _ _ _ inside]
  · intro index inside
    change S.eventAt steps (0 + index) = id (S.eventAt (steps.take count) index)
    simpa only [Nat.zero_add, id_eq] using (eventAt_take steps inside).symm
  · intro demand event
    rfl

theorem reverse_actions_checked (within : count ≤ steps.length)
    (stays : ∀ index, index ≤ count → (X.monitorAt cfg monitor steps index).mode = .reverse)
    (actions : X.actions cfg initial monitor steps = true) :
    L.actions (cfg.reverse monitor.forward.drops.length) initial monitor.reverse (steps.take count) = true :=
  (CampusTCPTwoProgressMonitor.actions_correct _ _ _ _).mpr
    (reverse_actions within stays ((CampusTCPTwoExchangeMonitor.actions_correct _ _ _ _).mp actions))

theorem reverse_service_checked (within : count ≤ steps.length)
    (stays : ∀ index, index ≤ count → (X.monitorAt cfg monitor steps index).mode = .reverse)
    (service : X.check cfg initial monitor steps bound = true) :
    L.check (cfg.reverse monitor.forward.drops.length) initial monitor.reverse (steps.take count) bound = true :=
  (CampusTCPTwoProgressMonitor.check_correct _ _ _ _ _).mpr
    (reverse_service within stays ((CampusTCPTwoExchangeMonitor.check_correct _ _ _ _ _).mp service))

end Netlib.Check.CampusTCPTwoExchangeReverseProjection
