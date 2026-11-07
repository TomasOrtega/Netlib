import Netlib.Check.CampusTCPStartupMonitor
import Netlib.Check.CampusTCPStartupJobDrainComplete

/-!
# Protected demands after startup completes

A live recovery job supplies the demand. An empty inventory demands closure.
Actual queue frames preserve the same selected work.
-/

namespace Netlib.Check.CampusTCPStartupDrainSelection

open CampusTCPModel CampusTCPStartupJobs

namespace P
export CampusTCPStartupSelection (Protection phaseRank path criticalPath criticalTimer choose retain demand useful)
end P
namespace M
export CampusTCPStartupMonitor (Monitor advanceProtection)
end M

variable {input : Input} {config : CampusTCPStartupTransferMonitor.Config}
variable {state after : State input} {held : Option P.Protection}

private theorem choose_complete (complete : P.phaseRank state = 4) :
    (∃ index job, P.choose state = some (.path index) ∧ P.path state index = some job) ∨
      (P.choose state = none ∧ inventory state = []) := by
  cases jobs : inventory state with
  | nil =>
    right
    exact ⟨by simp only [P.choose, P.criticalPath, P.criticalTimer, complete, Nat.reduceEqDiff,
      ↓reduceIte, jobs, List.find?_nil, Option.map_none], rfl⟩
  | cons job jobs =>
    left
    refine ⟨job.outputIndex, job, ?_, ?_⟩
    · simp only [P.choose, P.criticalPath, complete, Nat.reduceEqDiff, ↓reduceIte,
        jobs, P.useful, List.find?_cons, ↓reduceIte]
    · simp only [P.path, jobs, List.find?_cons, decide_true]

theorem retain_complete (complete : P.phaseRank state = 4) :
    (∃ index job, P.retain state held = some (.path index) ∧ P.path state index = some job) ∨
      (P.retain state held = none ∧ inventory state = []) := by
  cases held with
  | none => exact choose_complete complete
  | some protection =>
    cases protection with
    | timer actor =>
      simpa only [P.retain, P.criticalTimer, complete, Nat.reduceEqDiff, reduceCtorEq, ↓reduceIte] using
        choose_complete (state := state) complete
    | path index =>
      cases selected : P.path state index with
      | none => simpa only [P.retain, selected] using choose_complete (state := state) complete
      | some job =>
        exact Or.inl ⟨index, job, by simp only [P.retain, selected, P.useful, complete, ↓reduceIte], selected⟩

theorem positive_demand (complete : P.phaseRank state = 4) (positive : 0 < potential state) :
    ∃ job ∈ inventory state, P.demand config state held = some (CampusTCPStartupSelection.Job.event config job) := by
  rcases retain_complete (held := held) complete with ⟨index, job, retained, selected⟩ | ⟨retained, empty⟩
  · exact ⟨job, CampusTCPStartupSelection.selected_member selected,
      by simp only [P.demand, retained, selected, Option.map_some]⟩
  · simp only [potential, empty, List.map_nil, List.sum_nil, Nat.lt_irrefl] at positive

theorem zero_demand (complete : P.phaseRank state = 4) (zero : potential state = 0) :
    P.demand config state held = some .finishStartup := by
  have empty := potential_zero_iff.mp zero
  rcases retain_complete (held := held) complete with ⟨index, job, retained, selected⟩ | ⟨retained, empty⟩
  · have member := CampusTCPStartupSelection.selected_member selected
    rw [empty] at member
    cases member
  · simp only [P.demand, retained, complete, ↓reduceIte]

theorem retain_idempotent (complete : P.phaseRank state = 4) :
    P.retain state (P.retain state held) = P.retain state held := by
  rcases retain_complete (held := held) complete with ⟨index, job, retained, selected⟩ | ⟨retained, empty⟩
  · rw [retained]
    exact CampusTCPStartupSelection.retain_live_path selected (by simp only [P.useful, complete])
  · rw [retained]
    simp only [P.retain, P.choose, P.criticalPath, P.criticalTimer, complete, Nat.reduceEqDiff,
      ↓reduceIte, empty, List.find?_nil, Option.map_none]

theorem retain_frame (before : P.phaseRank state = 4) (later : P.phaseRank after = 4)
    (frame : CampusTCPStartupJobDrainComplete.QueueFrame state after) :
    P.retain after held = P.retain state held := by
  have paths (index : Nat) : P.path after index = P.path state index :=
    CampusTCPStartupSelection.path_same (congrArg Theory.PacketCustody.State.pending frame.custody)
      (congrArg (fun work => work.pending) frame.work)
  have chosen : P.choose after = P.choose state := by
    simp only [P.choose, P.criticalPath, P.criticalTimer, before, later, Nat.reduceEqDiff,
      ↓reduceIte, frame.inventory]
  cases held with
  | none => exact chosen
  | some protection =>
    cases protection with
    | timer actor =>
      simp only [P.retain, P.criticalTimer, before, later, reduceCtorEq, ↓reduceIte, chosen]
    | path index =>
      simp only [P.retain, paths, P.useful, before, later, chosen]

theorem demand_frame (before : P.phaseRank state = 4) (later : P.phaseRank after = 4)
    (frame : CampusTCPStartupJobDrainComplete.QueueFrame state after) :
    P.demand config after held = P.demand config state held := by
  have paths (index : Nat) : P.path after index = P.path state index :=
    CampusTCPStartupSelection.path_same (congrArg Theory.PacketCustody.State.pending frame.custody)
      (congrArg (fun work => work.pending) frame.work)
  rcases retain_complete (held := held) before with ⟨index, job, retained, selected⟩ | ⟨retained, empty⟩
  all_goals simp only [P.demand, retain_frame before later frame, retained, paths, before, later, ↓reduceIte]

theorem demand_idempotent (complete : P.phaseRank state = 4) :
    P.demand config state (P.retain state held) = P.demand config state held := by
  simp only [P.demand, retain_idempotent complete]

theorem advanceProtection_frame (actual : Step input) (monitor : M.Monitor)
    (before : P.phaseRank actual.before = 4) (later : P.phaseRank actual.result.state = 4)
    (frame : CampusTCPStartupJobDrainComplete.QueueFrame actual.before actual.result.state) :
    M.advanceProtection config monitor actual = P.retain actual.before monitor.protection := by
  have retained := retain_frame (held := P.retain actual.before monitor.protection) before later frame
  rcases retain_complete (held := monitor.protection) before with ⟨index, job, selected, present⟩ | ⟨selected, empty⟩
  all_goals
    simp only [M.advanceProtection, before, later, Nat.lt_irrefl, ↓reduceIte, selected,
      CampusTCPStartupMonitor.expired, Bool.false_eq_true]
    first
      | simpa only [selected] using retained.trans (retain_idempotent before)
      | (cases actual.event <;> simpa only [selected] using retained.trans (retain_idempotent before))

theorem pending_frame (actual : Step input) (monitor : M.Monitor)
    (before : P.phaseRank actual.before = 4) (later : P.phaseRank actual.result.state = 4)
    (frame : CampusTCPStartupJobDrainComplete.QueueFrame actual.before actual.result.state) :
    P.demand config actual.result.state (M.advanceProtection config monitor actual) =
      P.demand config actual.before monitor.protection := by
  rw [advanceProtection_frame actual monitor before later frame, demand_frame before later frame]
  exact demand_idempotent before

end Netlib.Check.CampusTCPStartupDrainSelection
