import Netlib.Check.CampusRevocationControlFrames

namespace Netlib.Check.CampusRevocationControl

open Packet Protocol
open CampusRevocationModel
open CampusRevocationTargets

theorem trace_authentication (trace : Trace input budget initial steps final) (targets : Targets input after)
    (permitted : ∀ actual ∈ steps, allowed targets actual = true) :
    final.campus.authentication = initial.campus.authentication := by
  induction trace with
  | nil => rfl
  | cons head rest ih =>
    have next := allowed_authentication targets head (permitted head (by simp))
    exact (ih (fun actual member => permitted actual (List.mem_cons_of_mem _ member))).trans next

theorem trace_binding (trace : Trace input budget initial steps final) (entry : NetfilterNAT.Entry)
    (binding : initial.campus.deployment.handoff.binding = some entry) :
    final.campus.deployment.handoff.binding = some entry := by
  induction trace with
  | nil => exact binding
  | cons head rest ih => exact ih (step_binding head entry binding)

theorem authentication_at_after (report : Report input budget events) (cut : Nat) (targets : Targets input after)
    (checked : actions report cut targets = true) (slot : Nat) (afterCut : cut ≤ slot)
    (within : slot ≤ report.steps.length) :
    (stateAt input.initial report.steps slot).campus.authentication =
      (stateAt input.initial report.steps cut).campus.authentication := by
  have range : slot - cut ≤ (report.steps.drop cut).length := by simp only [List.length_drop]; omega
  have interval := (report.trace.drop cut).take (slot - cut) range
  have same := trace_authentication interval targets (fun actual member =>
    actions_allowed report cut targets checked actual (List.mem_of_mem_take member))
  have index : cut + (slot - cut) = slot := by omega
  simpa only [stateAt_offset, index] using same

theorem binding_at_after (report : Report input budget events) (cut : Nat) (slot : Nat)
    (afterCut : cut ≤ slot) (within : slot ≤ report.steps.length) (entry : NetfilterNAT.Entry)
    (binding : (stateAt input.initial report.steps cut).campus.deployment.handoff.binding = some entry) :
    (stateAt input.initial report.steps slot).campus.deployment.handoff.binding = some entry := by
  have range : slot - cut ≤ (report.steps.drop cut).length := by simp only [List.length_drop]; omega
  have interval := (report.trace.drop cut).take (slot - cut) range
  have same := trace_binding interval entry binding
  have index : cut + (slot - cut) = slot := by omega
  simpa only [stateAt_offset, index] using same

end Netlib.Check.CampusRevocationControl
