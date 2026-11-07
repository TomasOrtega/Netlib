import Netlib.Check.CampusTCPRevocationControl
import Netlib.Check.CampusTCPRevocationFrames
import Netlib.Check.CampusTCPTraceSlices

/-!
# Bounded installation of the four stored TCP deny targets

The same action and service checks establish the actual native sources.
Later transport and target installs retain those sources and current lifetimes.
-/

namespace Netlib.Check.CampusTCPRevocationInstallation

open CampusTCPModel CampusTCPRevocationTargets

namespace C
export CampusTCPRevocationControl (allowed actions service)
end C
namespace M
export CampusTCPRevocationMonitor (Installation Monitor initial requested monitorAt)
end M
namespace F
export CampusTCPRevocationFrames (initial_established established_installed)
end F
namespace S
export CampusTCPSchedule (stateAt)
end S

variable {input : Input} {initial final : State input} {events remaining : List Event}
variable {steps : List (Step input)} {allowance bound slot : Nat}

theorem actions_member (names : M.Installation → String)
    (actions : C.actions names allowance steps = true) (actual : Step input) (member : actual ∈ steps) :
    C.allowed names allowance actual.before actual.event = true := by
  induction steps with
  | nil => cases member
  | cons head rest ih =>
    have checked : C.allowed names allowance head.before head.event = true ∧ C.actions names allowance rest = true := by
      simpa only [C.actions, Bool.and_eq_true] using actions
    rcases List.mem_cons.mp member with same | later
    · exact same ▸ checked.1
    · exact ih checked.2 later

theorem allowed_frame (targets : Targets input initial) (actual : Step input)
    (checked : C.allowed targets.names allowance actual.before actual.event = true) :
    CampusTCPRoundEnvironment.TransportOnly actual.event ∨
      ∃ changed, M.requested actual.event = some (changed, targets.names changed) := by
  cases request : M.requested actual.event with
  | none => exact .inl (CampusTCPRevocationControl.allowed_transport _ _ _ _ checked request)
  | some pair =>
    rcases pair with ⟨changed, name⟩
    have same := CampusTCPRevocationControl.allowed_request _ _ _ _ checked changed name request
    exact .inr ⟨changed, by simp only [same]⟩

private theorem monitorAt_take (names : M.Installation → String) (monitor : M.Monitor)
    (steps : List (Step input)) (count : Nat) :
    M.monitorAt names monitor (steps.take count) count = M.monitorAt names monitor steps count := by
  induction steps generalizing monitor count with
  | nil => simp only [List.take_nil, M.monitorAt]
  | cons actual rest ih =>
    cases count with
    | zero => simp only [List.take_zero, M.monitorAt]
    | succ count => exact ih _ count

theorem empty_after (names : M.Installation → String)
    (checked : C.service names initial M.initial steps bound = true)
    (enough : 4 * bound ≤ steps.length) (after : 4 * bound ≤ slot) (within : slot ≤ steps.length) :
    M.monitorAt names M.initial steps slot = [] := by
  have complete := CampusTCPRevocationControl.installations_complete names initial steps bound checked enough
  have nonincrease : ∀ index, index < steps.length →
      (M.monitorAt names M.initial steps (index + 1)).length ≤ (M.monitorAt names M.initial steps index).length := by
    intro index inside
    rw [CampusTCPRevocationMonitor.monitorAt_succ names M.initial steps index inside]
    exact CampusTCPRevocationMonitor.observe_nonincrease _ _ _
  have bounded := Theory.BoundedServiceRank.rank_mono
    (rank := fun index => (M.monitorAt names M.initial steps index).length) nonincrease after within
  rw [complete, List.length_nil] at bounded
  exact List.eq_nil_of_length_eq_zero (by omega)

theorem established_at (trace : Trace input initial events steps final remaining) (targets : Targets input initial)
    (actions : C.actions targets.names allowance steps = true) (within : slot ≤ steps.length) :
    targets.Established (M.monitorAt targets.names M.initial steps slot) (S.stateAt initial steps slot) := by
  have earlierTrace := CampusTCPSchedule.Trace.take trace slot within
  have established := CampusTCPRevocationFrames.Trace.established earlierTrace targets M.initial
    (fun actual member => allowed_frame targets actual
      (actions_member _ actions actual (List.mem_of_mem_take member))) (F.initial_established targets initial)
  rw [List.length_take, Nat.min_eq_left within, monitorAt_take] at established
  exact established

theorem current_at (trace : Trace input initial events steps final remaining) (targets : Targets input initial)
    (actions : C.actions targets.names allowance steps = true) (within : slot ≤ steps.length) :
    targets.CurrentAt (S.stateAt initial steps slot) := by
  apply CampusTCPRevocationFrames.Trace.current (CampusTCPSchedule.Trace.take trace slot within) targets
    (fun actual member => allowed_frame targets actual (actions_member _ actions actual (List.mem_of_mem_take member)))
  intro gateway
  exact ⟨rfl, rfl, rfl⟩

theorem installed_at (trace : Trace input initial events steps final remaining) (targets : Targets input initial)
    (actions : C.actions targets.names allowance steps = true)
    (checked : C.service targets.names initial M.initial steps bound = true)
    (enough : 4 * bound ≤ steps.length) (after : 4 * bound ≤ slot) (within : slot ≤ steps.length) :
    targets.Installed (S.stateAt initial steps slot) ∧ targets.CurrentAt (S.stateAt initial steps slot) := by
  have established := established_at trace targets actions within
  rw [empty_after _ checked enough after within] at established
  exact ⟨F.established_installed targets _ established, current_at trace targets actions within⟩

theorem installed_by (trace : Trace input initial events steps final remaining) (targets : Targets input initial)
    (actions : C.actions targets.names allowance steps = true)
    (checked : C.service targets.names initial M.initial steps bound = true)
    (enough : 4 * bound ≤ steps.length) :
    targets.Installed (S.stateAt initial steps (4 * bound)) ∧ targets.CurrentAt (S.stateAt initial steps (4 * bound)) :=
  installed_at trace targets actions checked enough (Nat.le_refl _) enough

end Netlib.Check.CampusTCPRevocationInstallation
