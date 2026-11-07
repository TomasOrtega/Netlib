import Netlib.Check.CampusTCPTwoTransferMonitor
import Netlib.Check.CampusTCPTraceSlices
import Netlib.Check.CampusTCPTwoExchangeProjection
import Netlib.Theory.BoundedServiceRestriction

/-!
# Whole transfer service on actual slices

Suffixes start at their stored state and raw monitor.
Their actions and service come from the same whole certificate.
-/

namespace Netlib.Check.CampusTCPTwoTransferSlices

open CampusTCPModel

namespace M
export CampusTCPTwoTransferMonitor (Config Monitor observe monitorAt pendingAt Allowed Serviced actions check)
end M
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

export CampusTCPTraceSlices (stateAt_drop stateAt_take eventAt_drop)

variable {input : Input} {cfg : M.Config} {initial : State input} {monitor : M.Monitor}
variable {steps : List (Step input)} {offset count slot bound : Nat}

theorem monitorAt_drop (cfg : M.Config) (monitor : M.Monitor) (steps : List (Step input)) (offset slot : Nat) :
    M.monitorAt cfg (M.monitorAt cfg monitor steps offset) (steps.drop offset) slot =
      M.monitorAt cfg monitor steps (offset + slot) := by
  induction steps generalizing monitor offset with
  | nil => simp only [List.drop_nil, M.monitorAt]
  | cons head rest ih =>
    cases offset with
    | zero => simp only [List.drop_zero, CampusTCPTwoTransferMonitor.monitorAt_zero, Nat.zero_add]
    | succ offset =>
      simpa only [List.drop_succ_cons, M.monitorAt, Nat.succ_add] using ih (M.observe cfg monitor head) offset

theorem pendingAt_drop (cfg : M.Config) (initial : State input) (monitor : M.Monitor)
    (steps : List (Step input)) (offset slot : Nat) :
    M.pendingAt cfg (S.stateAt initial steps offset) (M.monitorAt cfg monitor steps offset) (steps.drop offset) slot =
      M.pendingAt cfg initial monitor steps (offset + slot) := by
  unfold M.pendingAt
  rw [CampusTCPTraceSlices.stateAt_drop, monitorAt_drop]

theorem actions_drop (within : offset ≤ steps.length)
    (actions : ∀ index, index < steps.length → M.Allowed cfg (S.stateAt initial steps index)
      (M.monitorAt cfg monitor steps index) (S.eventAt steps index)) :
    ∀ index, index < (steps.drop offset).length →
      M.Allowed cfg (S.stateAt (S.stateAt initial steps offset) (steps.drop offset) index)
        (M.monitorAt cfg (M.monitorAt cfg monitor steps offset) (steps.drop offset) index)
        (S.eventAt (steps.drop offset) index) := by
  intro index inside
  rw [CampusTCPTraceSlices.stateAt_drop, monitorAt_drop, CampusTCPTraceSlices.eventAt_drop]
  apply actions
  rw [List.length_drop] at inside
  omega

theorem service_drop (within : offset ≤ steps.length)
    (service : M.Serviced cfg initial monitor steps bound) :
    M.Serviced cfg (S.stateAt initial steps offset) (M.monitorAt cfg monitor steps offset) (steps.drop offset) bound := by
  change Theory.BoundedServiceCheck.Serviced (steps.drop offset).length _ _ _ bound
  apply Theory.BoundedServiceRestriction.restrict service (offset := offset) (by rw [List.length_drop]; omega)
    id (fun _ _ same => same) id
  · intro index _
    rw [Option.map_id, pendingAt_drop]
    rfl
  · intro index _
    exact (CampusTCPTraceSlices.eventAt_drop steps offset index).symm
  · intro demand event
    rfl

theorem monitorAt_take (cfg : M.Config) (monitor : M.Monitor) (steps : List (Step input)) (inside : slot ≤ count) :
    M.monitorAt cfg monitor (steps.take count) slot = M.monitorAt cfg monitor steps slot :=
  by
  induction steps generalizing monitor slot count with
  | nil => simp only [List.take_nil, M.monitorAt]
  | cons head rest ih =>
    cases count with
    | zero =>
      have zero : slot = 0 := by omega
      subst slot
      rfl
    | succ count =>
      cases slot with
      | zero => rfl
      | succ slot => exact ih (M.observe cfg monitor head) (by omega)

theorem monitorAt_fold (cfg : M.Config) (monitor : M.Monitor) (steps : List (Step input)) (within : slot ≤ steps.length) :
    M.monitorAt cfg monitor steps slot = (steps.take slot).foldl (M.observe cfg) monitor := by
  have length : (steps.take slot).length = slot := by rw [List.length_take, Nat.min_eq_left within]
  rw [← CampusTCPTwoTransferMonitor.monitorAt_length, length, monitorAt_take _ _ _ (Nat.le_refl _)]

theorem pendingAt_take (cfg : M.Config) (initial : State input) (monitor : M.Monitor)
    (steps : List (Step input)) (inside : slot ≤ count) :
    M.pendingAt cfg initial monitor (steps.take count) slot = M.pendingAt cfg initial monitor steps slot := by
  unfold M.pendingAt
  rw [CampusTCPTraceSlices.stateAt_take _ _ inside, monitorAt_take _ _ _ inside]

theorem actions_take (within : count ≤ steps.length)
    (actions : ∀ index, index < steps.length → M.Allowed cfg (S.stateAt initial steps index)
      (M.monitorAt cfg monitor steps index) (S.eventAt steps index)) :
    ∀ index, index < (steps.take count).length → M.Allowed cfg (S.stateAt initial (steps.take count) index)
      (M.monitorAt cfg monitor (steps.take count) index) (S.eventAt (steps.take count) index) := by
  intro index inside
  have length : (steps.take count).length = count := by rw [List.length_take, Nat.min_eq_left within]
  rw [length] at inside
  rw [CampusTCPTraceSlices.stateAt_take _ _ (by omega : index ≤ count),
    monitorAt_take _ _ _ (by omega : index ≤ count), CampusTCPTwoExchangeProjection.eventAt_take _ inside]
  exact actions index (by omega)

theorem service_take (within : count ≤ steps.length)
    (service : M.Serviced cfg initial monitor steps bound) : M.Serviced cfg initial monitor (steps.take count) bound := by
  have length : (steps.take count).length = count := by rw [List.length_take, Nat.min_eq_left within]
  change Theory.BoundedServiceCheck.Serviced (steps.take count).length _ _ _ bound
  rw [length]
  apply Theory.BoundedServiceRestriction.restrict service (offset := 0) (by omega)
    id (fun _ _ same => same) id
  · intro index inside
    rw [Nat.zero_add, Option.map_id, pendingAt_take _ _ _ _ inside]
    rfl
  · intro index inside
    simpa only [Nat.zero_add, id_eq] using (CampusTCPTwoExchangeProjection.eventAt_take steps inside).symm
  · intro demand event
    rfl

theorem actions_drop_checked (within : offset ≤ steps.length)
    (actions : M.actions cfg initial monitor steps = true) :
    M.actions cfg (S.stateAt initial steps offset) (M.monitorAt cfg monitor steps offset) (steps.drop offset) = true :=
  (CampusTCPTwoTransferMonitor.actions_correct _ _ _ _).mpr
    (actions_drop within ((CampusTCPTwoTransferMonitor.actions_correct _ _ _ _).mp actions))

theorem service_drop_checked (within : offset ≤ steps.length)
    (service : M.check cfg initial monitor steps bound = true) :
    M.check cfg (S.stateAt initial steps offset) (M.monitorAt cfg monitor steps offset) (steps.drop offset) bound = true :=
  (CampusTCPTwoTransferMonitor.check_correct _ _ _ _ _).mpr
    (service_drop within ((CampusTCPTwoTransferMonitor.check_correct _ _ _ _ _).mp service))

theorem actions_take_checked (within : count ≤ steps.length)
    (actions : M.actions cfg initial monitor steps = true) : M.actions cfg initial monitor (steps.take count) = true :=
  (CampusTCPTwoTransferMonitor.actions_correct _ _ _ _).mpr
    (actions_take within ((CampusTCPTwoTransferMonitor.actions_correct _ _ _ _).mp actions))

theorem service_take_checked (within : count ≤ steps.length)
    (service : M.check cfg initial monitor steps bound = true) : M.check cfg initial monitor (steps.take count) bound = true :=
  (CampusTCPTwoTransferMonitor.check_correct _ _ _ _ _).mpr
    (service_take within ((CampusTCPTwoTransferMonitor.check_correct _ _ _ _ _).mp service))

end Netlib.Check.CampusTCPTwoTransferSlices
