import Netlib.Check.CampusTCPSchedule
import Netlib.Theory.BoundedServiceRank

/-!
# Four native installations in a TCP revocation

The monitor removes a target only for its actual installation event.
Other operations retain all outstanding installation demands.
-/

namespace Netlib.Check.CampusTCPRevocationMonitor

open CampusTCPModel

inductive Installation where
  | forward (gateway : Gateway)
  | ingress (gateway : Gateway)
  deriving Repr, DecidableEq

abbrev Monitor := List Installation

def initial : Monitor :=
  [.forward .primary, .ingress .primary, .forward .standby, .ingress .standby]

def requested : Event → Option (Installation × String)
  | .install name => some (.forward .primary, name)
  | .installAt gateway name => some (.forward gateway, name)
  | .installGuard name => some (.ingress .primary, name)
  | .installGuardAt gateway name => some (.ingress gateway, name)
  | _ => none

def selected (names : Installation → String) (event : Event) : Option Installation :=
  match requested event with
  | none => none
  | some (target, name) => if name = names target then some target else none

def observe (names : Installation → String) (monitor : Monitor) (event : Event) : Monitor :=
  match selected names event with
  | none => monitor
  | some target => monitor.erase target

def nextDemand (monitor : Monitor) : Option Installation := monitor.head?

def serves (names : Installation → String) (target : Installation) (event : Event) : Bool :=
  decide (selected names event = some target)

def monitorAt (names : Installation → String) (monitor : Monitor) : List (Step input) → Nat → Monitor
  | [], _ => monitor
  | _ :: _, 0 => monitor
  | actual :: rest, slot + 1 => monitorAt names (observe names monitor actual.event) rest slot

def service (names : Installation → String) (monitor : Monitor) (steps : List (Step input)) (bound : Nat) : Bool :=
  Theory.BoundedServiceCheck.check steps.length
    (fun slot => nextDemand (monitorAt names monitor steps slot))
    (CampusTCPSchedule.eventAt steps) (serves names) bound

@[simp] theorem initial_length : initial.length = 4 := rfl

theorem observe_sublist (names : Installation → String) (monitor : Monitor) (event : Event) :
    List.Sublist (observe names monitor event) monitor := by
  unfold observe
  split
  · exact List.Sublist.refl _
  · exact List.erase_sublist

theorem observe_nonincrease (names : Installation → String) (monitor : Monitor) (event : Event) :
    (observe names monitor event).length ≤ monitor.length :=
  (observe_sublist names monitor event).length_le

theorem observe_equal (names : Installation → String) (monitor : Monitor) (event : Event)
    (same : (observe names monitor event).length = monitor.length) : observe names monitor event = monitor :=
  (observe_sublist names monitor event).eq_of_length same

theorem demand_exists (monitor : Monitor) (positive : 0 < monitor.length) :
    ∃ target, nextDemand monitor = some target := by
  cases monitor with
  | nil => simp at positive
  | cons head tail => exact ⟨head, rfl⟩

theorem observe_strict (names : Installation → String) (monitor : Monitor) (event : Event)
    (target : Installation) (pending : nextDemand monitor = some target)
    (served : serves names target event = true) :
    (observe names monitor event).length < monitor.length := by
  have selected : selected names event = some target := of_decide_eq_true served
  cases monitor with
  | nil => simp [nextDemand] at pending
  | cons head tail =>
    have same : head = target := Option.some.inj pending
    subst head
    simp only [observe, selected, List.erase_cons_head, List.length_cons]
    omega

theorem monitorAt_zero (names : Installation → String) (monitor : Monitor) (steps : List (Step input)) :
    monitorAt names monitor steps 0 = monitor := by cases steps <;> rfl

theorem monitorAt_succ (names : Installation → String) (monitor : Monitor) (steps : List (Step input))
    (slot : Nat) (within : slot < steps.length) :
    monitorAt names monitor steps (slot + 1) =
      observe names (monitorAt names monitor steps slot) (CampusTCPSchedule.eventAt steps slot) := by
  induction steps generalizing monitor slot with
  | nil => simp at within
  | cons actual rest ih =>
    cases slot with
    | zero => simp only [monitorAt, monitorAt_zero, CampusTCPSchedule.eventAt, List.getElem?_cons_zero]
    | succ slot => exact ih _ _ (Nat.lt_of_succ_lt_succ within)

theorem complete (names : Installation → String) (monitor : Monitor) (steps : List (Step input))
    (bound : Nat) (checked : service names monitor steps bound = true)
    (enough : monitor.length * bound ≤ steps.length) :
    monitorAt names monitor steps (monitor.length * bound) = [] := by
  have serviced := (Theory.BoundedServiceCheck.check_correct _ _ _ _ _).mp checked
  have nonincrease : ∀ slot, slot < steps.length →
      (monitorAt names monitor steps (slot + 1)).length ≤ (monitorAt names monitor steps slot).length := by
    intro slot inside
    rw [monitorAt_succ names monitor steps slot inside]
    exact observe_nonincrease _ _ _
  have demand : ∀ slot, slot ≤ steps.length → 0 < (monitorAt names monitor steps slot).length →
      ∃ target, nextDemand (monitorAt names monitor steps slot) = some target := by
    intro slot _ positive
    exact demand_exists _ positive
  have persistent : ∀ slot, slot < steps.length → 0 < (monitorAt names monitor steps slot).length →
      ∀ target, (monitorAt names monitor steps (slot + 1)).length = (monitorAt names monitor steps slot).length →
      nextDemand (monitorAt names monitor steps slot) = some target →
      nextDemand (monitorAt names monitor steps (slot + 1)) = some target := by
    intro slot inside _ target same selected
    rw [monitorAt_succ names monitor steps slot inside] at same ⊢
    rw [observe_equal names _ _ same]
    exact selected
  have strict : ∀ slot, slot < steps.length → 0 < (monitorAt names monitor steps slot).length →
      ∀ target, nextDemand (monitorAt names monitor steps slot) = some target →
      serves names target (CampusTCPSchedule.eventAt steps slot) = true →
      (monitorAt names monitor steps (slot + 1)).length < (monitorAt names monitor steps slot).length := by
    intro slot inside _ target selected served
    rw [monitorAt_succ names monitor steps slot inside]
    exact observe_strict names _ _ target selected served
  have zero := Theory.BoundedServiceRank.zero_by_at serviced nonincrease demand persistent strict
    0 (by simp only [monitorAt_zero, Nat.zero_add]; exact enough)
  simp only [monitorAt_zero, Nat.zero_add] at zero
  exact List.eq_nil_of_length_eq_zero zero

end Netlib.Check.CampusTCPRevocationMonitor
