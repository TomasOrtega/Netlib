import Netlib.Check.CampusTCPRevocationBound
import Netlib.Check.CampusTCPRevocationClosure
import Netlib.Check.CampusTCPRevocationFrames
import Netlib.Check.CampusTCPRevocationInstallation

/-!
# Actual early TCP revocation completion

The finite search reads stored installation and custody states.
Its selected cut retains the real trace and the original loss counter.
-/

namespace Netlib.Check.CampusTCPRevocationCompletion

open CampusTCPModel CampusTCPRevocationTargets

namespace C
export CampusTCPRevocationCustody (frontier)
end C
namespace M
export CampusTCPRevocationMonitor (initial monitorAt)
end M
namespace D
export CampusTCPRevocationControl (actions service)
end D
namespace B
export CampusTCPRevocationBound (slots)
end B
namespace S
export CampusTCPSchedule (stateAt)
end S

variable {input : Input} {initial final : State input} {events remaining : List Event}
variable {steps : List (Step input)} {allowance bound slot : Nat}

def ready (targets : Targets input initial) (steps : List (Step input)) (slot : Nat) : Bool :=
  (M.monitorAt targets.names M.initial steps slot).isEmpty &&
    (C.frontier (S.stateAt initial steps slot)).isEmpty

def findCompletion (targets : Targets input initial) (steps : List (Step input)) (bound : Nat) : Option Nat :=
  (List.range (min (B.slots initial bound) steps.length + 1)).find? (ready targets steps)

theorem ready_correct (targets : Targets input initial) (steps : List (Step input)) (slot : Nat) :
    ready targets steps slot = true ↔
      M.monitorAt targets.names M.initial steps slot = [] ∧
      C.frontier (S.stateAt initial steps slot) = [] := by
  simp only [ready, Bool.and_eq_true, List.isEmpty_iff]

theorem found_bounds (targets : Targets input initial)
    (found : findCompletion targets steps bound = some slot) :
    slot ≤ B.slots initial bound ∧ slot ≤ steps.length := by
  have member := List.mem_of_find?_eq_some found
  have inside := List.mem_range.mp member
  omega

theorem found_ready (targets : Targets input initial)
    (found : findCompletion targets steps bound = some slot) :
    M.monitorAt targets.names M.initial steps slot = [] ∧ C.frontier (S.stateAt initial steps slot) = [] := by
  exact (ready_correct targets steps slot).mp (List.find?_some found)

theorem found_first (targets : Targets input initial)
    (found : findCompletion targets steps bound = some slot) (earlier : Nat) (before : earlier < slot) :
    ready targets steps earlier = false := by
  have minimal := (List.find?_range_eq_some.mp found).2.2 earlier before
  cases observed : ready targets steps earlier <;> simp_all

theorem found_trace (trace : Trace input initial events steps final remaining) (targets : Targets input initial)
    (found : findCompletion targets steps bound = some slot) :
    Trace input initial ((steps.take slot).map (·.event)) (steps.take slot)
      (S.stateAt initial steps slot) [] :=
  CampusTCPSchedule.Trace.take trace slot (found_bounds targets found).2

theorem closed_at (trace : Trace input initial events steps final remaining) (targets : Targets input initial)
    (actions : D.actions targets.names allowance steps = true)
    (found : findCompletion targets steps bound = some slot) :
    CampusTCPRevocationClosure.Closed targets (S.stateAt initial steps slot) := by
  have within := (found_bounds targets found).2
  have selected := found_ready targets found
  have established := CampusTCPRevocationInstallation.established_at trace targets actions within
  rw [selected.1] at established
  exact ⟨CampusTCPRevocationFrames.established_installed targets _ established,
    CampusTCPRevocationInstallation.current_at trace targets actions within, selected.2⟩

theorem actions_drop (names : CampusTCPRevocationMonitor.Installation → String)
    (actions : D.actions names allowance steps = true) (slot : Nat) :
    D.actions names allowance (steps.drop slot) = true := by
  induction steps generalizing slot with
  | nil => simp only [List.drop_nil, D.actions]
  | cons actual rest ih =>
    cases slot with
    | zero => exact actions
    | succ slot =>
      have checked : CampusTCPRevocationControl.allowed names allowance actual.before actual.event = true ∧
          D.actions names allowance rest = true := by
        simpa only [D.actions, Bool.and_eq_true] using actions
      have later := checked.2
      exact ih later slot

theorem suffix_closed (trace : Trace input initial events steps final remaining) (targets : Targets input initial)
    (actions : D.actions targets.names allowance steps = true)
    (revoked : CampusTCPRevocationTargets.revoked input initial.authentication = true)
    (history : Theory.PacketCustody.History initial.custody)
    (found : findCompletion targets steps bound = some slot) :
    CampusTCPRevocationClosure.Closed targets final ∧
      ∀ actual ∈ steps.drop slot, CampusTCPRevocationClosure.Quiet actual := by
  have within := (found_bounds targets found).2
  have preceding := CampusTCPSchedule.Trace.take trace slot within
  have suffix := CampusTCPTraceSlices.Trace.drop trace within
  exact CampusTCPRevocationClosure.Trace.closed suffix targets revoked
    (actions_drop targets.names actions slot) (CampusTCPCustodyFacts.Trace.history preceding history)
    (closed_at trace targets actions found)

theorem services_none_after (trace : Trace input initial events steps final remaining) (targets : Targets input initial)
    (actions : D.actions targets.names allowance steps = true)
    (revoked : CampusTCPRevocationTargets.revoked input initial.authentication = true)
    (history : Theory.PacketCustody.History initial.custody)
    (found : findCompletion targets steps bound = some slot) :
    ∀ actual ∈ steps.drop slot, ∀ served,
      actual.result.service = some served → served.evidence.output = none := by
  intro actual member
  exact ((suffix_closed trace targets actions revoked history found).2 actual member).service

theorem receipts_none_after (trace : Trace input initial events steps final remaining) (targets : Targets input initial)
    (actions : D.actions targets.names allowance steps = true)
    (revoked : CampusTCPRevocationTargets.revoked input initial.authentication = true)
    (history : Theory.PacketCustody.History initial.custody)
    (found : findCompletion targets steps bound = some slot) :
    ∀ actual ∈ steps.drop slot, actual.result.receipt = none := by
  intro actual member
  exact ((suffix_closed trace targets actions revoked history found).2 actual member).receipt

theorem exists_completion (trace : Trace input initial events steps final remaining) (targets : Targets input initial)
    (actions : D.actions targets.names allowance steps = true)
    (checked : D.service targets.names initial M.initial steps bound = true)
    (revoked : CampusTCPRevocationTargets.revoked input initial.authentication = true)
    (history : Theory.PacketCustody.History initial.custody)
    (enough : B.slots initial bound ≤ steps.length) :
    ∃ slot, findCompletion targets steps bound = some slot := by
  obtain ⟨complete⟩ := CampusTCPRevocationBound.complete trace targets actions checked revoked history enough
  have selected : ready targets steps complete.slot = true := by
    apply (ready_correct targets steps complete.slot).mpr
    exact ⟨CampusTCPRevocationInstallation.empty_after targets.names checked
      (Nat.le_trans complete.afterInstall complete.within) complete.afterInstall complete.within, complete.empty⟩
  have member : complete.slot ∈ List.range (min (B.slots initial bound) steps.length + 1) := by
    apply List.mem_range.mpr
    have deadline := complete.deadline
    have within := complete.within
    omega
  cases found : findCompletion targets steps bound with
  | none =>
    have absent := List.find?_eq_none.mp found complete.slot member
    exact False.elim (absent selected)
  | some slot => exact ⟨slot, rfl⟩

end Netlib.Check.CampusTCPRevocationCompletion
