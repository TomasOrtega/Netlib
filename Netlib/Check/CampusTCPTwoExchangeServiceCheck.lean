import Netlib.Check.CampusTCPTwoExchangeMonitor
import Netlib.Theory.BoundedServiceTable

/-!
# Cached service checks for the stored exchange suffix

The tables use only stored results and monitor observations.
-/

namespace Netlib.Check.CampusTCPTwoExchangeServiceCheck

open CampusTCPModel

namespace M
export CampusTCPTwoExchangeMonitor (Config Monitor Demand nextDemand observe pendingAt Serviced)
end M

variable {input : Input}

def pendingList (config : M.Config) (initial : State input) (monitor : M.Monitor) :
    List (Step input) → List (Option M.Demand)
  | [] => [M.nextDemand config initial monitor]
  | head :: rest => M.nextDemand config initial monitor ::
      pendingList config head.result.state (M.observe config monitor head) rest

theorem pendingList_length (config : M.Config) (initial : State input) (monitor : M.Monitor)
    (steps : List (Step input)) : (pendingList config initial monitor steps).length = steps.length + 1 := by
  induction steps generalizing initial monitor with
  | nil => rfl
  | cons head rest ih => simp only [pendingList, List.length_cons, ih]

theorem pendingList_get (config : M.Config) (initial : State input) (monitor : M.Monitor)
    (steps : List (Step input)) (slot : Nat) (within : slot ≤ steps.length) :
    (pendingList config initial monitor steps)[slot]? = some (M.pendingAt config initial monitor steps slot) := by
  induction steps generalizing initial monitor slot with
  | nil =>
    have zero : slot = 0 := by simpa only [List.length_nil, Nat.le_zero] using within
    subst slot
    rfl
  | cons head rest ih =>
    cases slot with
    | zero => rfl
    | succ slot =>
      exact ih head.result.state (M.observe config monitor head) slot (by simpa only [List.length_cons, Nat.succ_le_succ_iff] using within)

def pendingArray (config : M.Config) (initial : State input) (monitor : M.Monitor) (steps : List (Step input)) :
    Array (Option M.Demand) := (pendingList config initial monitor steps).toArray

theorem pendingArray_get (config : M.Config) (initial : State input) (monitor : M.Monitor)
    (steps : List (Step input)) (slot : Nat) (within : slot ≤ steps.length) :
    (pendingArray config initial monitor steps)[slot]? = some (M.pendingAt config initial monitor steps slot) := by
  rw [pendingArray, List.getElem?_toArray]
  exact pendingList_get config initial monitor steps slot within

theorem pendingArray_value (config : M.Config) (initial : State input) (monitor : M.Monitor)
    (steps : List (Step input)) (slot : Nat) (within : slot ≤ steps.length) :
    ((pendingArray config initial monitor steps)[slot]?).getD none = M.pendingAt config initial monitor steps slot := by
  rw [pendingArray_get config initial monitor steps slot within]
  rfl

def eventsArray (steps : List (Step input)) : Array Event := (steps.map (·.event)).toArray

theorem eventsArray_get (steps : List (Step input)) (slot : Nat) :
    (eventsArray steps)[slot]? = (steps[slot]?).map (·.event) := by
  simp only [eventsArray, List.getElem?_toArray, List.getElem?_map]

theorem eventsArray_value (steps : List (Step input)) (slot : Nat) :
    ((eventsArray steps)[slot]?).getD (.authentication 0) = CampusTCPSchedule.eventAt steps slot := by
  rw [eventsArray_get]
  unfold CampusTCPSchedule.eventAt
  cases steps[slot]? <;> rfl

def check (config : M.Config) (initial : State input) (monitor : M.Monitor)
    (steps : List (Step input)) (bound : Nat) : Bool :=
  Theory.BoundedServiceTable.check steps.length (pendingArray config initial monitor steps) (eventsArray steps)
    (.authentication 0) CampusTCPTwoExchangeMonitor.serves bound

theorem check_correct (config : M.Config) (initial : State input) (monitor : M.Monitor)
    (steps : List (Step input)) (bound : Nat) :
    check config initial monitor steps bound = true ↔ M.Serviced config initial monitor steps bound :=
  Theory.BoundedServiceTable.check_correct (pendingArray_value config initial monitor steps)
    (fun slot _ => eventsArray_value steps slot)

theorem check_eq (config : M.Config) (initial : State input) (monitor : M.Monitor)
    (steps : List (Step input)) (bound : Nat) :
    check config initial monitor steps bound = CampusTCPTwoExchangeMonitor.check config initial monitor steps bound :=
  Theory.BoundedServiceTable.check_eq (pendingArray_value config initial monitor steps)
    (fun slot _ => eventsArray_value steps slot)

end Netlib.Check.CampusTCPTwoExchangeServiceCheck
