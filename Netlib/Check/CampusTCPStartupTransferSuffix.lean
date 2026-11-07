import Netlib.Check.CampusTCPStartupTransferExecution
import Netlib.Check.CampusTCPStartupTransferRestriction

/-!
# The literal data suffix of the whole observed execution

A data cut keeps one actual startup snapshot throughout the suffix.
Its Actions and service check follow from the same whole certificate.
-/

namespace Netlib.Check.CampusTCPStartupTransferSuffix

open CampusTCPModel

namespace E
export CampusTCPStartupTransferExecution
  (Monitor initial observe allowed nextDemand monitorAt pendingAt actions Serviced check actions_correct check_correct)
end E
namespace M
export CampusTCPStartupTransferMonitor (Config Demand)
end M
namespace P
export CampusTCPStartupMonitor (Monitor observe)
end P
namespace T
export CampusTCPStartupTransferConfig (Handoff snapshot snapshot_fields)
end T
namespace W
export CampusTCPTwoTransferMonitor (Monitor observe monitorAt pendingAt allowed actions Serviced check)
end W
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

variable {input : Input} {config : M.Config} {initial : State input}
variable {monitor : E.Monitor input} {dataMonitor : W.Monitor}
variable {handoff : T.Handoff input.active input.passive}
variable {steps : List (Step input)} {offset slot bound : Nat}

@[simp] theorem monitorAt_zero (config : M.Config) (monitor : E.Monitor input) (steps : List (Step input)) :
    E.monitorAt config monitor steps 0 = monitor := by cases steps <;> rfl

theorem monitorAt_data (config : M.Config) (handoff : T.Handoff input.active input.passive)
    (monitor : W.Monitor) (steps : List (Step input)) (slot : Nat) :
    E.monitorAt config (.data handoff monitor) steps slot =
      .data handoff (W.monitorAt (config.transfer.data handoff) monitor steps slot) := by
  induction steps generalizing monitor slot with
  | nil => rfl
  | cons actual rest ih =>
    cases slot with
    | zero => rfl
    | succ slot => exact ih (W.observe (config.transfer.data handoff) monitor actual) slot

theorem monitorAt_drop (config : M.Config) (monitor : E.Monitor input) (steps : List (Step input)) (offset slot : Nat) :
    E.monitorAt config (E.monitorAt config monitor steps offset) (steps.drop offset) slot =
      E.monitorAt config monitor steps (offset + slot) := by
  induction steps generalizing monitor offset with
  | nil => simp only [List.drop_nil, E.monitorAt]
  | cons actual rest ih =>
    cases offset with
    | zero => simp only [List.drop_zero, monitorAt_zero, Nat.zero_add]
    | succ offset =>
      simpa only [List.drop_succ_cons, E.monitorAt, Nat.succ_add] using ih (E.observe config monitor actual) offset

theorem data_monitor_suffix (cut : E.monitorAt config monitor steps offset = .data handoff dataMonitor) :
    E.monitorAt config monitor steps (offset + slot) =
      .data handoff (W.monitorAt (config.transfer.data handoff) dataMonitor (steps.drop offset) slot) := by
  rw [← monitorAt_drop, cut, monitorAt_data]

theorem data_pending_suffix (cut : E.monitorAt config monitor steps offset = .data handoff dataMonitor) :
    E.pendingAt config initial monitor steps (offset + slot) =
      (W.pendingAt (config.transfer.data handoff) (S.stateAt initial steps offset) dataMonitor (steps.drop offset) slot).map
        CampusTCPStartupTransferMonitor.Demand.data := by
  unfold E.pendingAt W.pendingAt
  rw [data_monitor_suffix cut, CampusTCPTraceSlices.stateAt_drop]
  rfl

theorem data_allowed_suffix (cut : E.monitorAt config monitor steps offset = .data handoff dataMonitor) :
    E.allowed config (S.stateAt initial steps (offset + slot)) (E.monitorAt config monitor steps (offset + slot)) =
      W.allowed (config.transfer.data handoff)
        (S.stateAt (S.stateAt initial steps offset) (steps.drop offset) slot)
        (W.monitorAt (config.transfer.data handoff) dataMonitor (steps.drop offset) slot) := by
  rw [data_monitor_suffix cut, CampusTCPTraceSlices.stateAt_drop]
  rfl

theorem data_actions_suffix (within : offset ≤ steps.length)
    (cut : E.monitorAt config monitor steps offset = .data handoff dataMonitor)
    (actions : E.actions config initial monitor steps = true) :
    W.actions (config.transfer.data handoff) (S.stateAt initial steps offset) dataMonitor (steps.drop offset) = true :=
  CampusTCPStartupTransferRestriction.data_actions_suffix within ((E.actions_correct _ _ _ _).mp actions)
    (fun _ _ => data_allowed_suffix cut)

theorem data_service_suffix (within : offset ≤ steps.length)
    (cut : E.monitorAt config monitor steps offset = .data handoff dataMonitor)
    (service : E.Serviced config initial monitor steps bound) :
    W.Serviced (config.transfer.data handoff) (S.stateAt initial steps offset) dataMonitor (steps.drop offset) bound :=
  CampusTCPStartupTransferRestriction.data_service_suffix within service (fun _ _ => data_pending_suffix cut)

theorem data_check_suffix (within : offset ≤ steps.length)
    (cut : E.monitorAt config monitor steps offset = .data handoff dataMonitor)
    (checked : E.check config initial monitor steps bound = true) :
    W.check (config.transfer.data handoff) (S.stateAt initial steps offset) dataMonitor (steps.drop offset) bound = true :=
  CampusTCPStartupTransferRestriction.data_check_suffix within ((E.check_correct _ _ _ _ _).mp checked)
    (fun _ _ => data_pending_suffix cut)

theorem observe_startup_data (actual : Step input) (startup : P.Monitor)
    (observed : E.observe config (.startup startup) actual = .data handoff dataMonitor) :
    (P.observe config startup actual).mode = .data ∧ T.snapshot actual.result.state = some handoff ∧ dataMonitor = .initial := by
  simp only [E.observe] at observed
  split at observed
  · rename_i ready
    cases selected : T.snapshot actual.result.state with
    | none => rw [selected] at observed; cases observed
    | some retained =>
      rw [selected] at observed
      cases observed
      exact ⟨ready, rfl, rfl⟩
  · cases observed

theorem observe_startup_snapshot (actual : Step input) (startup : P.Monitor)
    (observed : E.observe config (.startup startup) actual = .data handoff dataMonitor) :
    actual.result.state.recoveryArchive = some handoff.archive ∧ handoff.startupDrops = actual.result.state.custody.dropped :=
  T.snapshot_fields (observe_startup_data actual startup observed).2.1

end Netlib.Check.CampusTCPStartupTransferSuffix
