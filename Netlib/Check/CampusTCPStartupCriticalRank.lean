import Netlib.Check.CampusTCPStartupTimerWait

/-!
# Remaining critical service before startup completes

A protected path keeps its queue stage. A timer adds its actual wait distance.
The current elapsed-time bound supplies the finite rank bound.
-/

namespace Netlib.Check.CampusTCPStartupCriticalRank

open CampusTCPModel

namespace P
export CampusTCPStartupSelection (Protection phaseRank choose retain path criticalPath criticalTimer timer)
end P
namespace J
export CampusTCPStartupJobs (Job Stage)
end J
namespace T
export CampusTCPStartupTimerWait (distance elapsed_distance_le)
end T
namespace W
export CampusTCPRecoveryRoundMonitor (waitSlots)
end W

def stageCost : J.Stage → Nat
  | .ingress => 3
  | .ticket => 2
  | .link => 1

def futureCost (phase : Nat) (kind : TCPHandshakeRecovery.Kind) : Nat :=
  if phase = 1 then 6 else if phase = 2 then 3 else if phase = 3 ∧ kind = .synAck then 3 else 0

def pathCost (phase : Nat) (job : J.Job input) : Nat := stageCost job.stage + futureCost phase job.kind

def rank (quantum : Nat) (state : State input) (held : Option P.Protection) : Nat :=
  if P.phaseRank state = 4 then 0
  else match P.retain state held with
    | some (.path index) => ((P.path state index).map (pathCost (P.phaseRank state))).getD 0
    | some (.timer actor) =>
      match P.timer state actor with
      | some current => T.distance quantum current + if P.phaseRank state = 1 then 9 else 6
      | none => 0
    | none => 0

theorem pathCost_le (phase : Nat) (job : J.Job input) : pathCost phase job ≤ 9 := by
  have stage : stageCost job.stage ≤ 3 := by cases job.stage <;> decide
  have future : futureCost phase job.kind ≤ 6 := by
    unfold futureCost
    split
    · omega
    · split
      · omega
      · split <;> omega
  unfold pathCost
  omega

private theorem choose_timer (selected : P.choose state = some (.timer actor)) :
    P.criticalTimer state = some actor := by
  cases current : P.criticalPath state with
  | some job => simp only [P.choose, current, reduceCtorEq, Option.some.injEq] at selected
  | none =>
    cases pending : P.criticalTimer state with
    | none => simp only [P.choose, current, pending, Option.map_none, reduceCtorEq] at selected
    | some target =>
      simp only [P.choose, current, pending, Option.map_some, Option.some.injEq] at selected
      cases selected
      rfl

theorem retain_timer (selected : P.retain state held = some (.timer actor)) :
    P.criticalTimer state = some actor := by
  cases held with
  | none => exact choose_timer selected
  | some held =>
    cases held with
    | path index =>
      cases found : P.path state index with
      | none => exact choose_timer (by simpa only [P.retain, found] using selected)
      | some job =>
        by_cases useful : CampusTCPStartupSelection.useful (P.phaseRank state) job = true
        · simp only [P.retain, found, useful, ↓reduceIte] at selected
          cases selected
        · exact choose_timer (by simpa only [P.retain, found, useful, Bool.false_eq_true, ↓reduceIte] using selected)
    | timer target =>
      by_cases same : P.criticalTimer state = some target
      · simp only [P.retain, same, ↓reduceIte, Option.some.injEq] at selected
        cases selected
        exact same
      · exact choose_timer (by simpa only [P.retain, same, ↓reduceIte] using selected)

theorem critical_pending (connected : state.connection = .recovering current)
    (reachable : TCPHandshakeRecovery.Reachable current) (selected : P.criticalTimer state = some actor) :
    ∃ flight, (current.timer actor.recoverySide).status = .pending flight := by
  have timers := reachable.phase_timers
  cases phase : current.phase with
  | idle | complete complete client server => simp only [P.criticalTimer, P.phaseRank, connected, phase, reduceCtorEq] at selected
  | opened value =>
    simp only [P.criticalTimer, P.phaseRank, connected, phase, Option.some.injEq] at selected
    subst actor
    rw [TCPHandshakeRecovery.PhaseTimers, phase] at timers
    exact ⟨timers.1.choose, timers.1.choose_spec.1⟩
  | answered value =>
    simp only [P.criticalTimer, P.phaseRank, connected, phase, Option.some.injEq] at selected
    subst actor
    rw [TCPHandshakeRecovery.PhaseTimers, phase] at timers
    exact ⟨timers.2.choose, timers.2.choose_spec.1⟩
  | acknowledged value client =>
    simp only [P.criticalTimer, P.phaseRank, connected, phase, Option.some.injEq] at selected
    subst actor
    rw [TCPHandshakeRecovery.PhaseTimers, phase] at timers
    exact ⟨timers.2.choose, timers.2.choose_spec.1⟩

theorem rank_le (connected : state.connection = .recovering current)
    (reachable : TCPHandshakeRecovery.Reachable current)
    (clocks : ∀ actor : Actor, (current.timer actor.recoverySide).now ≤ horizon) :
    rank quantum state held ≤ W.waitSlots quantum (1000 + horizon) + 10 := by
  unfold rank
  split
  · omega
  · cases selected : P.retain state held with
    | none => change 0 ≤ W.waitSlots quantum (1000 + horizon) + 10; omega
    | some protection =>
      cases protection with
      | path index =>
        cases found : P.path state index with
        | none => simp only [found, Option.map_none, Option.getD_none]; omega
        | some job =>
          have cost := pathCost_le (P.phaseRank state) job
          simpa only [found, Option.map_some, Option.getD_some] using
            (show pathCost (P.phaseRank state) job ≤ W.waitSlots quantum (1000 + horizon) + 10 by omega)
      | timer actor =>
        obtain ⟨flight, pending⟩ := critical_pending connected reachable (retain_timer selected)
        have bound := T.elapsed_distance_le (current.timer_valid actor.recoverySide) pending
          (reachable.timers_bounded actor.recoverySide) (clocks actor) (quantum := quantum)
        simp only [P.timer, connected]
        split <;> omega

end Netlib.Check.CampusTCPStartupCriticalRank
