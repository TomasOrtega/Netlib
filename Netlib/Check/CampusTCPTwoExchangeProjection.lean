import Netlib.Check.CampusTCPTwoExchangeMonitor
import Netlib.Check.CampusTCPTraceSlices
import Netlib.Theory.BoundedServiceRestriction

/-!
# Forward service on the same exchange prefix

While the current selector stays forward, its local fold is exact.
The one exchange service condition restricts to that stored prefix.
-/

namespace Netlib.Check.CampusTCPTwoExchangeProjection

open CampusTCPModel

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

theorem local_monitorAt_take (cfg : L.Config) (initial : L.Monitor) (steps : List (Step input)) (inside : slot ≤ count) :
    L.monitorAt cfg initial (steps.take count) slot = L.monitorAt cfg initial steps slot := by
  induction steps generalizing initial slot count with
  | nil => simp only [List.take_nil, L.monitorAt]
  | cons head rest ih =>
    cases count with
    | zero =>
      have zero : slot = 0 := by omega
      subst slot
      rfl
    | succ count =>
      cases slot with
      | zero => rfl
      | succ slot => exact ih (L.observe cfg initial head) (by omega)

theorem exchange_monitorAt_take (cfg : X.Config) (initial : X.Monitor) (steps : List (Step input)) (inside : slot ≤ count) :
    X.monitorAt cfg initial (steps.take count) slot = X.monitorAt cfg initial steps slot := by
  induction steps generalizing initial slot count with
  | nil => simp only [List.take_nil, X.monitorAt]
  | cons head rest ih =>
    cases count with
    | zero =>
      have zero : slot = 0 := by omega
      subst slot
      rfl
    | succ count =>
      cases slot with
      | zero => rfl
      | succ slot => exact ih (X.observe cfg initial head) (by omega)

theorem eventAt_take (steps : List (Step input)) (inside : slot < count) :
    S.eventAt (steps.take count) slot = S.eventAt steps slot := by
  unfold S.eventAt
  rw [List.getElem?_take_of_lt inside]

private theorem local_mode_beq (left right : CampusTCPTwoProgressMonitor.Mode) :
    (left == right) = decide (left = right) := by cases left <;> cases right <;> rfl

theorem observe_forward (mode : monitor.mode = .forward) (actual : Step input)
    (stays : (X.observe cfg monitor actual).mode = .forward) :
    (X.observe cfg monitor actual).forward = L.observe cfg.forward monitor.forward actual := by
  by_cases accepted : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoExchangeMonitor.allowed cfg actual.before monitor actual.event) = true
  · cases next : (L.observe cfg.forward monitor.forward actual).mode <;>
      simp only [X.observe, accepted, mode, next, local_mode_beq, reduceCtorEq, decide_false,
        decide_true, Bool.false_eq_true, ite_true, ite_false, CampusTCPTwoExchangeMonitor.Monitor.invalid] at stays ⊢
  · simp only [X.observe, accepted, ite_false, CampusTCPTwoExchangeMonitor.Monitor.invalid, reduceCtorEq] at stays

theorem forward_at (within : count ≤ steps.length)
    (stays : ∀ index, index ≤ count → (X.monitorAt cfg monitor steps index).mode = .forward)
    (inside : slot ≤ count) :
    (X.monitorAt cfg monitor steps slot).forward = L.monitorAt cfg.forward monitor.forward steps slot := by
  induction slot with
  | zero => simp only [CampusTCPTwoExchangeMonitor.monitorAt_zero, CampusTCPTwoProgressMonitor.monitorAt_zero]
  | succ slot ih =>
    have earlier : slot ≤ count := by omega
    have available : slot < steps.length := by omega
    have found : steps[slot]? = some steps[slot] := List.getElem?_eq_some_iff.mpr ⟨available, rfl⟩
    rw [CampusTCPTwoExchangeMonitor.monitorAt_next _ _ _ found,
      observe_forward (stays slot earlier) _ (by
        rw [← CampusTCPTwoExchangeMonitor.monitorAt_next _ _ _ found]
        exact stays (slot + 1) inside), ih earlier,
      CampusTCPTwoProgressMonitor.monitorAt_next _ _ _ found]

theorem forward_fold (within : count ≤ steps.length)
    (stays : ∀ index, index ≤ count → (X.monitorAt cfg monitor steps index).mode = .forward) :
    (X.monitorAt cfg monitor steps count).forward = (steps.take count).foldl (L.observe cfg.forward) monitor.forward := by
  have length : (steps.take count).length = count := by rw [List.length_take, Nat.min_eq_left within]
  rw [← CampusTCPTwoProgressMonitor.monitorAt_length, length, local_monitorAt_take _ _ _ (Nat.le_refl _)]
  exact forward_at within stays (Nat.le_refl _)

theorem forward_actions (within : count ≤ steps.length)
    (stays : ∀ index, index ≤ count → (X.monitorAt cfg monitor steps index).mode = .forward)
    (actions : ∀ index, index < steps.length → X.Allowed cfg (S.stateAt initial steps index)
      (X.monitorAt cfg monitor steps index) (S.eventAt steps index)) :
    ∀ index, index < (steps.take count).length → L.Allowed cfg.forward (S.stateAt initial (steps.take count) index)
      (L.monitorAt cfg.forward monitor.forward (steps.take count) index) (S.eventAt (steps.take count) index) := by
  intro index inside
  have length : (steps.take count).length = count := by rw [List.length_take, Nat.min_eq_left within]
  rw [length] at inside
  have selected := actions index (by omega)
  change CampusTCPTwoExchangeMonitor.allowed _ _ _ _ = true at selected
  simp only [CampusTCPTwoExchangeMonitor.allowed, stays index (by omega)] at selected
  rw [forward_at within stays (by omega)] at selected
  rw [CampusTCPTraceSlices.stateAt_take _ _ (by omega : index ≤ count),
    local_monitorAt_take _ _ _ (by omega : index ≤ count), eventAt_take _ inside]
  exact selected

theorem forward_service (within : count ≤ steps.length)
    (stays : ∀ index, index ≤ count → (X.monitorAt cfg monitor steps index).mode = .forward)
    (service : X.Serviced cfg initial monitor steps bound) :
    L.Serviced cfg.forward initial monitor.forward (steps.take count) bound := by
  have length : (steps.take count).length = count := by rw [List.length_take, Nat.min_eq_left within]
  change Theory.BoundedServiceCheck.Serviced (steps.take count).length _ _ _ bound
  rw [length]
  apply Theory.BoundedServiceRestriction.restrict service (offset := 0) (by omega)
    CampusTCPTwoExchangeMonitor.Demand.forward (fun _ _ same => CampusTCPTwoExchangeMonitor.Demand.forward.inj same) id
  · intro index inside
    simp only [Nat.zero_add, X.pendingAt, L.pendingAt, X.nextDemand, stays index inside]
    rw [forward_at within stays inside, CampusTCPTraceSlices.stateAt_take _ _ inside,
      local_monitorAt_take _ _ _ inside]
  · intro index inside
    change S.eventAt steps (0 + index) = id (S.eventAt (steps.take count) index)
    simpa only [Nat.zero_add, id_eq] using (eventAt_take steps inside).symm
  · intro demand event
    rfl

theorem forward_actions_checked (within : count ≤ steps.length)
    (stays : ∀ index, index ≤ count → (X.monitorAt cfg monitor steps index).mode = .forward)
    (actions : X.actions cfg initial monitor steps = true) :
    L.actions cfg.forward initial monitor.forward (steps.take count) = true :=
  (CampusTCPTwoProgressMonitor.actions_correct _ _ _ _).mpr
    (forward_actions within stays ((CampusTCPTwoExchangeMonitor.actions_correct _ _ _ _).mp actions))

theorem forward_service_checked (within : count ≤ steps.length)
    (stays : ∀ index, index ≤ count → (X.monitorAt cfg monitor steps index).mode = .forward)
    (service : X.check cfg initial monitor steps bound = true) :
    L.check cfg.forward initial monitor.forward (steps.take count) bound = true :=
  (CampusTCPTwoProgressMonitor.check_correct _ _ _ _ _).mpr
    (forward_service within stays ((CampusTCPTwoExchangeMonitor.check_correct _ _ _ _ _).mp service))

end Netlib.Check.CampusTCPTwoExchangeProjection
