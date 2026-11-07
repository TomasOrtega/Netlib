import Netlib.Check.CampusTCPStartupCriticalChoice

/-!
# The next path after a real startup retry

An emitted SYN or SYNACK supplies current useful work after timer expiry.
-/

namespace Netlib.Check.CampusTCPStartupCriticalRetryChoice

open CampusTCPModel CampusTCPStartupJobs

namespace P
export CampusTCPStartupSelection (phaseRank useful criticalPath choose)
end P
namespace R
export CampusTCPStartupCriticalRank (rank pathCost stageCost futureCost pathCost_le)
end R
namespace U
export CampusTCPStartupJobUnique (Linear)
end U

variable {input : Input} {state : State input} {job : Job input}

private theorem useful_find (member : job ∈ inventory state) (useful : P.useful (P.phaseRank state) job = true) :
    ∃ candidate, (inventory state).find? (P.useful (P.phaseRank state)) = some candidate := by
  cases found : (inventory state).find? (P.useful (P.phaseRank state)) with
  | none => exact False.elim (List.find?_eq_none.mp found job member useful)
  | some candidate => exact ⟨candidate, rfl⟩

theorem criticalPath_exists (member : job ∈ inventory state) (useful : P.useful (P.phaseRank state) job = true) :
    ∃ candidate, P.criticalPath state = some candidate := by
  obtain ⟨candidate, found⟩ := useful_find member useful
  by_cases phase : P.phaseRank state = 3
  · cases first : (inventory state).find? (fun current => decide (current.actor = .client ∧ current.kind = .finalAck)) with
    | none =>
      refine ⟨candidate, ?_⟩
      simp only [P.criticalPath, phase, ite_true, first, Option.or]
      simpa only [phase] using found
    | some preferred =>
      exact ⟨preferred, by simp only [P.criticalPath, phase, ite_true, first, Option.or]⟩
  · exact ⟨candidate, by simpa only [P.criticalPath, phase, ite_false] using found⟩

theorem rank_choose_opened (linear : U.Linear state) (phase : P.phaseRank state = 1)
    (member : job ∈ inventory state) (actor : job.actor = .client) (kind : job.kind = .syn) :
    R.rank quantum state (P.choose state) ≤ 9 := by
  have useful : P.useful (P.phaseRank state) job = true := by
    simp only [P.useful, phase, actor, kind, true_and, decide_true]
  obtain ⟨candidate, selected⟩ := criticalPath_exists member useful
  rw [CampusTCPStartupCriticalChoice.rank_choose_path linear (by omega) selected]
  exact R.pathCost_le _ candidate

theorem acknowledged_cost (phase : P.phaseRank state = 3) (job : Job input) :
    R.pathCost (P.phaseRank state) job ≤ 6 := by
  have stage : R.stageCost job.stage ≤ 3 := by cases job.stage <;> decide
  unfold R.pathCost R.futureCost
  rw [phase]
  change R.stageCost job.stage + (if 3 = 3 ∧ job.kind = .synAck then 3 else 0) ≤ 6
  split <;> omega

theorem rank_choose_acknowledged (linear : U.Linear state) (phase : P.phaseRank state = 3)
    (member : job ∈ inventory state) (actor : job.actor = .server) (kind : job.kind = .synAck) :
    R.rank quantum state (P.choose state) ≤ 6 := by
  have useful : P.useful (P.phaseRank state) job = true := by
    simp only [P.useful, phase, actor, kind, true_and, or_true, decide_true]
  obtain ⟨candidate, selected⟩ := criticalPath_exists member useful
  rw [CampusTCPStartupCriticalChoice.rank_choose_path linear (by omega) selected]
  exact acknowledged_cost phase candidate

end Netlib.Check.CampusTCPStartupCriticalRetryChoice
