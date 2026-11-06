import Netlib.Check.CampusTCPGapProgressMonitor
import Netlib.Theory.BoundedServiceCheck

/-!
# Service bounds on the actual held-gap suffix

The finite check reads preceding-state demands and stored events.
Only evaluated operations supply service slots.
-/

namespace Netlib.Check.CampusTCPGapProgressServiceBound

open CampusTCPModel
namespace R
export CampusTCPGapProgressMonitor (Config Monitor Demand nextDemand monitorAt serves allowed Allowed)
end R
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

variable {input : Input}

def pendingAt (config : R.Config) (initial : State input) (monitor : R.Monitor)
    (steps : List (Step input)) (slot : Nat) : Option R.Demand :=
  R.nextDemand config (S.stateAt initial steps slot) (R.monitorAt config monitor steps slot)

def Serviced (config : R.Config) (initial : State input) (monitor : R.Monitor)
    (steps : List (Step input)) (bound : Nat) : Prop :=
  Theory.BoundedServiceCheck.Serviced steps.length (pendingAt config initial monitor steps)
    (S.eventAt steps) R.serves bound

def check (config : R.Config) (initial : State input) (monitor : R.Monitor)
    (steps : List (Step input)) (bound : Nat) : Bool :=
  Theory.BoundedServiceCheck.check steps.length (pendingAt config initial monitor steps)
    (S.eventAt steps) R.serves bound

theorem check_correct (config : R.Config) (initial : State input) (monitor : R.Monitor)
    (steps : List (Step input)) (bound : Nat) :
    check config initial monitor steps bound = true ↔ Serviced config initial monitor steps bound :=
  Theory.BoundedServiceCheck.check_correct _ _ _ _ _

def actions (config : R.Config) (initial : State input) (monitor : R.Monitor) (steps : List (Step input)) : Bool :=
  (List.range steps.length).all fun slot => R.allowed config (S.stateAt initial steps slot)
    (R.monitorAt config monitor steps slot) (S.eventAt steps slot)

theorem actions_correct (config : R.Config) (initial : State input) (monitor : R.Monitor) (steps : List (Step input)) :
    actions config initial monitor steps = true ↔
      ∀ slot, slot < steps.length → R.Allowed config (S.stateAt initial steps slot)
        (R.monitorAt config monitor steps slot) (S.eventAt steps slot) := by
  simp only [actions, List.all_eq_true, List.mem_range, R.Allowed]

end Netlib.Check.CampusTCPGapProgressServiceBound
