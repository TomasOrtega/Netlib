import Netlib.Check.CampusTCPStartupCriticalRank
import Netlib.Check.CampusTCPStartupJobUnique

/-!
# Rank bounds for the next actual startup path

The current inventory supplies the path. A pending final ACK has priority.
-/

namespace Netlib.Check.CampusTCPStartupCriticalChoice

open CampusTCPModel CampusTCPStartupJobs

namespace P
export CampusTCPStartupSelection (phaseRank useful path criticalPath choose retain)
end P
namespace R
export CampusTCPStartupCriticalRank (rank pathCost stageCost futureCost)
end R
namespace U
export CampusTCPStartupJobUnique (Linear)
end U

variable {input : Input} {state : State input} {job : Job input}

private theorem find_exists {rows : List α} {predicate : α → Bool} (member : value ∈ rows)
    (accepted : predicate value = true) : ∃ selected, rows.find? predicate = some selected := by
  cases found : rows.find? predicate with
  | none => exact False.elim (List.find?_eq_none.mp found value member accepted)
  | some selected => exact ⟨selected, rfl⟩

theorem criticalPath_useful (selected : P.criticalPath state = some job) :
    job ∈ inventory state ∧ P.useful (P.phaseRank state) job = true := by
  by_cases phase : P.phaseRank state = 3
  · simp only [P.criticalPath, phase, ite_true] at selected
    cases first : (inventory state).find? (fun current => decide (current.actor = .client ∧ current.kind = .finalAck)) with
    | none =>
      rw [first] at selected
      change (inventory state).find? (P.useful 3) = some job at selected
      refine ⟨List.mem_of_find?_eq_some selected, ?_⟩
      rw [phase]
      exact List.find?_some selected
    | some candidate =>
      rw [first] at selected
      change some candidate = some job at selected
      cases selected
      have accepted := List.find?_some
        (p := fun current : Job input => decide (current.actor = .client ∧ current.kind = .finalAck)) first
      have fields := of_decide_eq_true accepted
      refine ⟨List.mem_of_find?_eq_some first, ?_⟩
      simp only [P.useful, phase, fields.1, fields.2, true_and, true_or, decide_true]
  · simp only [P.criticalPath, phase, ite_false] at selected
    exact ⟨List.mem_of_find?_eq_some selected, List.find?_some selected⟩

theorem rank_choose_path (linear : U.Linear state) (incomplete : P.phaseRank state ≠ 4)
    (selected : P.criticalPath state = some job) :
    R.rank quantum state (P.choose state) = R.pathCost (P.phaseRank state) job := by
  obtain ⟨member, useful⟩ := criticalPath_useful selected
  have path := linear.path_eq job member
  have choice : P.choose state = some (.path job.outputIndex) := by simp only [P.choose, selected]
  simp only [R.rank, incomplete, ite_false, choice, P.retain, path, useful, ite_true,
    Option.map_some, Option.getD_some]

theorem answered_cost (phase : P.phaseRank state = 2) (job : Job input) :
    R.pathCost (P.phaseRank state) job ≤ 6 := by
  have stage : R.stageCost job.stage ≤ 3 := by cases job.stage <;> decide
  simp only [R.pathCost, phase, R.futureCost]
  change R.stageCost job.stage + 3 ≤ 6
  omega

theorem finalAck_cost (phase : P.phaseRank state = 3) (kind : job.kind = .finalAck) :
    R.pathCost (P.phaseRank state) job ≤ 3 := by
  have stage : R.stageCost job.stage ≤ 3 := by cases job.stage <;> decide
  simpa [R.pathCost, phase, R.futureCost, kind] using stage

theorem rank_choose_answered (linear : U.Linear state) (phase : P.phaseRank state = 2)
    (member : job ∈ inventory state) (actor : job.actor = .server) (kind : job.kind = .synAck) :
    R.rank quantum state (P.choose state) ≤ 6 := by
  have useful : P.useful (P.phaseRank state) job = true := by
    simp only [P.useful, phase, actor, kind, true_and, decide_true]
  obtain ⟨candidate, selected⟩ := find_exists member useful
  have critical : P.criticalPath state = some candidate := by
    simpa [P.criticalPath, phase] using selected
  rw [rank_choose_path linear (by omega) critical]
  exact answered_cost phase candidate

theorem rank_choose_finalAck (linear : U.Linear state) (phase : P.phaseRank state = 3)
    (member : job ∈ inventory state) (actor : job.actor = .client) (kind : job.kind = .finalAck) :
    R.rank quantum state (P.choose state) ≤ 3 := by
  have accepted : decide (job.actor = .client ∧ job.kind = .finalAck) = true := by
    simp only [actor, kind, true_and, decide_true]
  obtain ⟨candidate, selected⟩ := find_exists
    (predicate := fun current : Job input => decide (current.actor = .client ∧ current.kind = .finalAck)) member accepted
  have critical : P.criticalPath state = some candidate := by
    simp only [P.criticalPath, phase, ite_true, selected, Option.or]
  have acceptedCandidate := List.find?_some
    (p := fun current : Job input => decide (current.actor = .client ∧ current.kind = .finalAck)) selected
  have fields := of_decide_eq_true acceptedCandidate
  rw [rank_choose_path linear (by omega) critical]
  exact finalAck_cost phase fields.2

end Netlib.Check.CampusTCPStartupCriticalChoice
