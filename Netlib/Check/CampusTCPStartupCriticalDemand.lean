import Netlib.Check.CampusTCPStartupCriticalQueueRank
import Netlib.Check.CampusTCPStartupCurrentAt
import Netlib.Check.TCPHandshakeRecoveryAvailabilityFacts

/-!
# A current critical startup rank and demand

The actual OPEN rules out an idle drive cut. Reachable timers supply expiry work.
-/

namespace Netlib.Check.CampusTCPStartupCriticalDemand

open Protocol.TCP CampusTCPModel CampusTCPStartupJobs

namespace P
export CampusTCPStartupSelection (phaseRank path useful criticalPath criticalTimer choose retain demand timerDemand)
end P
namespace R
export CampusTCPStartupCriticalRank (rank stageCost futureCost pathCost critical_pending retain_timer)
end R
namespace U
export CampusTCPStartupJobUnique (Linear)
end U
namespace M
export CampusTCPStartupMonitor (Monitor Mode observe)
end M
namespace E
export CampusTCPStartupTransferExecution (initial monitorAt actions)
end E

variable {input : Input} {state : State input} {job : Job input}
variable {current : TCPHandshakeRecovery.State input.active input.passive}
variable {config : CampusTCPStartupTransferMonitor.Config}

theorem stageCost_positive (stage : Stage) : 0 < R.stageCost stage := by cases stage <;> decide

theorem pathCost_positive (phase : Nat) (job : Job input) : 0 < R.pathCost phase job := by
  have positive := stageCost_positive job.stage
  unfold R.pathCost
  omega

private theorem choose_cases (linear : U.Linear state) (critical : ∃ actor, P.criticalTimer state = some actor) :
    (∃ index job, P.choose state = some (.path index) ∧ P.path state index = some job) ∨
      (∃ actor, P.choose state = some (.timer actor) ∧ P.criticalTimer state = some actor) := by
  cases chosen : P.criticalPath state with
  | none =>
    obtain ⟨actor, timer⟩ := critical
    exact Or.inr ⟨actor, by simp only [P.choose, chosen, timer, Option.map_some], timer⟩
  | some job =>
    have member := (CampusTCPStartupCriticalChoice.criticalPath_useful chosen).1
    exact Or.inl ⟨job.outputIndex, job, by simp only [P.choose, chosen], linear.path_eq job member⟩

theorem effective_cases (linear : U.Linear state) (critical : ∃ actor, P.criticalTimer state = some actor) :
    (∃ index job, P.retain state held = some (.path index) ∧ P.path state index = some job) ∨
      (∃ actor, P.retain state held = some (.timer actor) ∧ P.criticalTimer state = some actor) := by
  have fallback := choose_cases linear critical
  cases held with
  | none => exact fallback
  | some protection =>
    cases protection with
    | path index =>
      cases found : P.path state index with
      | none => simpa only [P.retain, found] using fallback
      | some job =>
        by_cases useful : P.useful (P.phaseRank state) job = true
        · exact Or.inl ⟨index, job, by simp only [P.retain, found, useful, ↓reduceIte], found⟩
        · simpa only [P.retain, found, useful, Bool.false_eq_true, ↓reduceIte] using fallback
    | timer actor =>
      by_cases selected : P.criticalTimer state = some actor
      · exact Or.inr ⟨actor, by simp only [P.retain, selected, ↓reduceIte], selected⟩
      · simpa only [P.retain, selected, ↓reduceIte] using fallback

private theorem critical_exists (phase : P.phaseRank state = 1 ∨ P.phaseRank state = 2 ∨ P.phaseRank state = 3) :
    ∃ actor, P.criticalTimer state = some actor := by
  rcases phase with first | second | third
  · exact ⟨.client, by simp only [P.criticalTimer, first]⟩
  · exact ⟨.server, by simp only [P.criticalTimer, second]⟩
  · exact ⟨.server, by simp only [P.criticalTimer, third]⟩

theorem timer_lower (connected : state.connection = .recovering current)
    (retained : P.retain state held = some (.timer actor))
    (incomplete : P.phaseRank state ≠ 4) :
    (if P.phaseRank state = 1 then 10 else 7) ≤ R.rank quantum state held := by
  simp only [R.rank, incomplete, ite_false, retained, CampusTCPStartupSelection.timer, connected]
  unfold CampusTCPStartupTimerWait.distance
  split <;> omega

theorem rank_phase_one (connected : state.connection = .recovering current) (linear : U.Linear state)
    (phase : P.phaseRank state = 1) : 7 ≤ R.rank quantum state held := by
  rcases effective_cases linear (critical_exists (Or.inl phase)) (held := held) with
    ⟨index, job, retained, selected⟩ | ⟨actor, retained, timer⟩
  · have exactRank := CampusTCPStartupCriticalQueueRank.rank_retained retained selected (by omega : P.phaseRank state ≠ 4) (quantum := quantum)
    have positive := stageCost_positive job.stage
    rw [exactRank]
    simp only [R.pathCost, R.futureCost, phase, ite_true]
    omega
  · have lower := timer_lower connected retained (by omega : P.phaseRank state ≠ 4) (quantum := quantum)
    simp only [phase, ite_true] at lower
    omega

theorem rank_phase_two (connected : state.connection = .recovering current) (linear : U.Linear state)
    (phase : P.phaseRank state = 2) : 4 ≤ R.rank quantum state held := by
  rcases effective_cases linear (critical_exists (Or.inr (Or.inl phase))) (held := held) with
    ⟨index, job, retained, selected⟩ | ⟨actor, retained, timer⟩
  · have exactRank := CampusTCPStartupCriticalQueueRank.rank_retained retained selected (by omega : P.phaseRank state ≠ 4) (quantum := quantum)
    have positive := stageCost_positive job.stage
    rw [exactRank]
    simp only [R.pathCost, R.futureCost, phase, show (2 : Nat) ≠ 1 from by decide, ite_false, ite_true]
    omega
  · have lower := timer_lower connected retained (by omega : P.phaseRank state ≠ 4) (quantum := quantum)
    simp only [phase, show (2 : Nat) ≠ 1 from by decide, ite_false] at lower
    omega

theorem rank_phase_three (connected : state.connection = .recovering current) (linear : U.Linear state)
    (phase : P.phaseRank state = 3) : 1 ≤ R.rank quantum state held := by
  rcases effective_cases linear (critical_exists (Or.inr (Or.inr phase))) (held := held) with
    ⟨index, job, retained, selected⟩ | ⟨actor, retained, timer⟩
  · have exactRank := CampusTCPStartupCriticalQueueRank.rank_retained retained selected (by omega : P.phaseRank state ≠ 4) (quantum := quantum)
    rw [exactRank]
    exact pathCost_positive _ _
  · have lower := timer_lower connected retained (by omega : P.phaseRank state ≠ 4) (quantum := quantum)
    split at lower <;> omega

theorem rank_positive (connected : state.connection = .recovering current) (linear : U.Linear state)
    (phase : P.phaseRank state = 1 ∨ P.phaseRank state = 2 ∨ P.phaseRank state = 3) :
    0 < R.rank quantum state held := by
  rcases phase with first | second | third
  · have lower := rank_phase_one connected linear first (held := held) (quantum := quantum); omega
  · have lower := rank_phase_two connected linear second (held := held) (quantum := quantum); omega
  · exact rank_phase_three connected linear third

theorem demand_exists (connected : state.connection = .recovering current)
    (reachable : TCPHandshakeRecovery.Reachable current) (linear : U.Linear state)
    (phase : P.phaseRank state = 1 ∨ P.phaseRank state = 2 ∨ P.phaseRank state = 3) :
    ∃ event, P.demand config state held = some event := by
  rcases effective_cases linear (critical_exists phase) (held := held) with
    ⟨index, job, retained, selected⟩ | ⟨actor, retained, timer⟩
  · exact ⟨CampusTCPStartupSelection.Job.event config job, by simp only [P.demand, retained, selected, Option.map_some]⟩
  · obtain ⟨flight, pending⟩ := R.critical_pending connected reachable timer
    simp only [P.demand, retained, P.timerDemand, CampusTCPStartupSelection.timer, connected, pending]
    split <;> exact ⟨_, rfl⟩

theorem finish_complete (demand : P.demand config state held = some .finishStartup) : P.phaseRank state = 4 := by
  cases retained : P.retain state held with
  | none =>
    simp only [P.demand, retained] at demand
    split at demand
    · assumption
    · cases demand
  | some protection =>
    cases protection with
    | path index =>
      cases found : P.path state index with
      | none => simp only [P.demand, retained, found, Option.map_none, reduceCtorEq] at demand
      | some job =>
        simp only [P.demand, retained, found, Option.map_some, Option.some.injEq] at demand
        cases job <;> cases demand
    | timer actor =>
      simp only [P.demand, retained, P.timerDemand] at demand
      split at demand
      · cases demand
      · split at demand
        · split at demand <;> cases demand
        · cases demand

end Netlib.Check.CampusTCPStartupCriticalDemand
