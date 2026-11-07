import Netlib.Check.CampusTCPRevocationControl

/-!
# Computed current operations for TCP shutdown demands

The inclusive state check retains each demand and evaluates its actual step.
False policy verdicts remain recorded; support and current action checks decide enabledness.
-/

namespace Netlib.Check.CampusTCPRevocationEnabled

open CampusTCPModel
open CampusTCPRevocationMonitor (Installation)
open CampusTCPRevocationControl (Demand)

variable {input : Input}

def proposed (names : Installation → String) (allowance : Nat) (state : State input) : Demand → Event
  | .install (.forward gateway) => .installAt gateway (names (.forward gateway))
  | .install (.ingress gateway) => .installGuardAt gateway (names (.ingress gateway))
  | .resolveLink id service bytes =>
    if state.custody.dropped < allowance then .dropPacket id else .deliver service bytes true

def enabled (names : Installation → String) (allowance : Nat) (state : State input) (demand : Demand) : Bool :=
  match CampusTCPModel.step input state (proposed names allowance state demand) with
  | .error _ => false
  | .ok effect => effect.supported &&
      CampusTCPRevocationControl.allowed names allowance state (proposed names allowance state demand) &&
      CampusTCPRevocationControl.serves names demand (proposed names allowance state demand)

def check (names : Installation → String) (allowance : Nat) (initial : State input)
    (steps : List (Step input)) : Bool :=
  (List.range (steps.length + 1)).all fun slot =>
    match CampusTCPRevocationControl.pendingAt names initial CampusTCPRevocationMonitor.initial steps slot with
    | none => true
    | some demand => enabled names allowance (CampusTCPSchedule.stateAt initial steps slot) demand

structure Witness (names : Installation → String) (allowance : Nat) (state : State input) (demand : Demand) where
  actual : Step input
  before : actual.before = state
  event : actual.event = proposed names allowance state demand
  supported : actual.result.supported = true
  allowed : CampusTCPRevocationControl.allowed names allowance actual.before actual.event = true
  serves : CampusTCPRevocationControl.serves names demand actual.event = true

theorem enabled_witness (names : Installation → String) (allowance : Nat) (state : State input) (demand : Demand)
    (checked : enabled names allowance state demand = true) : Nonempty (Witness names allowance state demand) := by
  cases computed : CampusTCPModel.step input state (proposed names allowance state demand) with
  | error reason => simp only [enabled, computed, Bool.false_eq_true] at checked
  | ok effect =>
    have flags : (effect.supported = true ∧
        CampusTCPRevocationControl.allowed names allowance state (proposed names allowance state demand) = true) ∧
        CampusTCPRevocationControl.serves names demand (proposed names allowance state demand) = true := by
      simpa only [enabled, computed, Bool.and_eq_true] using checked
    exact ⟨⟨⟨state, proposed names allowance state demand, effect, computed⟩,
      rfl, rfl, flags.1.1, flags.1.2, flags.2⟩⟩

theorem check_selected (names : Installation → String) (allowance : Nat) (initial : State input)
    (steps : List (Step input)) (checked : check names allowance initial steps = true)
    (slot : Nat) (within : slot ≤ steps.length) (demand : Demand)
    (selected : CampusTCPRevocationControl.pendingAt names initial CampusTCPRevocationMonitor.initial steps slot = some demand) :
    enabled names allowance (CampusTCPSchedule.stateAt initial steps slot) demand = true := by
  have member : slot ∈ List.range (steps.length + 1) := List.mem_range.mpr (by omega)
  have actual := List.all_eq_true.mp checked slot member
  simpa only [selected] using actual

theorem check_witness (names : Installation → String) (allowance : Nat) (initial : State input)
    (steps : List (Step input)) (checked : check names allowance initial steps = true)
    (slot : Nat) (within : slot ≤ steps.length) (demand : Demand)
    (selected : CampusTCPRevocationControl.pendingAt names initial CampusTCPRevocationMonitor.initial steps slot = some demand) :
    Nonempty (Witness names allowance (CampusTCPSchedule.stateAt initial steps slot) demand) :=
  enabled_witness names allowance _ demand (check_selected names allowance initial steps checked slot within demand selected)

end Netlib.Check.CampusTCPRevocationEnabled
