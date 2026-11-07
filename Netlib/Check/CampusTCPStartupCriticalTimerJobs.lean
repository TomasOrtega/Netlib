import Netlib.Check.CampusTCPStartupDriveJobsEnabled
import Netlib.Check.CampusTCPStartupCriticalRank

/-!
# Actual queue work during a protected startup timer

Assignment and service keep the connection and selected timer. Queue progress
therefore preserves the protected timer's rank and exact demand.
-/

namespace Netlib.Check.CampusTCPStartupCriticalTimerJobs

open CampusTCPModel

namespace P
export CampusTCPStartupSelection (retain criticalTimer timer timerDemand demand phaseRank)
end P
namespace M
export CampusTCPStartupMonitor (Monitor advanceProtection expired)
end M
namespace R
export CampusTCPStartupCriticalRank (rank retain_timer)
end R
namespace A
export CampusTCPRoundAssignment (AssignmentFacts)
end A
namespace S
export CampusTCPRecoveryStartupServiceEnabled (Service)
end S
namespace J
export CampusTCPStartupDriveJobsEnabled (Run)
end J

variable {input : Input} {events : List Event} {report : Report input events}
variable {config : CampusTCPStartupTransferMonitor.Config} {monitor : M.Monitor}
variable {actual : Step input} {actor : Actor}

private theorem timer_frame (connection : actual.result.state.connection = actual.before.connection)
    (held : P.retain actual.before monitor.protection = some (.timer actor))
    (quiet : M.expired config.transfer.quantum actual.before (some (.timer actor)) actual.event = false) :
    M.advanceProtection config monitor actual = some (.timer actor) ∧
      R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) =
        R.rank config.transfer.quantum actual.before monitor.protection ∧
      P.demand config actual.result.state (M.advanceProtection config monitor actual) =
        P.demand config actual.before monitor.protection := by
  have phase : P.phaseRank actual.result.state = P.phaseRank actual.before := by
    simp only [P.phaseRank, connection]
  have role := R.retain_timer held
  have afterRole : P.criticalTimer actual.result.state = some actor := by
    simpa only [P.criticalTimer, phase] using role
  have retained : P.retain actual.result.state (some (.timer actor)) = some (.timer actor) :=
    CampusTCPStartupSelection.retain_timer afterRole
  have protection : M.advanceProtection config monitor actual = some (.timer actor) := by
    simp only [M.advanceProtection, held, phase, Nat.lt_irrefl, ↓reduceIte, quiet]
    exact retained
  refine ⟨protection, ?_, ?_⟩
  · simp only [R.rank, phase, protection, retained, held, P.timer, connection]
  · simp only [P.demand, protection, retained, held, P.timerDemand, P.timer, connection]

theorem assignment (facts : A.AssignmentFacts report.final index ingress produced actual)
    (held : P.retain actual.before monitor.protection = some (.timer actor)) :
    M.advanceProtection config monitor actual = some (.timer actor) ∧
      R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) =
        R.rank config.transfer.quantum actual.before monitor.protection ∧
      P.demand config actual.result.state (M.advanceProtection config monitor actual) =
        P.demand config actual.before monitor.protection := by
  have connection : actual.result.state.connection = actual.before.connection := by
    rw [facts.frame, facts.beforeEq]
  apply timer_frame connection held
  simp only [M.expired, facts.event]

theorem service (facts : S.Service report item actual)
    (held : P.retain actual.before monitor.protection = some (.timer actor)) :
    M.advanceProtection config monitor actual = some (.timer actor) ∧
      R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) =
        R.rank config.transfer.quantum actual.before monitor.protection ∧
      P.demand config actual.result.state (M.advanceProtection config monitor actual) =
        P.demand config actual.before monitor.protection := by
  have connection : actual.result.state.connection = actual.before.connection := facts.connection.trans (congrArg State.connection facts.before).symm
  apply timer_frame connection held
  simp only [M.expired, facts.event]

theorem run (value : J.Run config report current job actual)
    (ordinary : (∃ index ingress, actual.event = .assign index ingress) ∨
      ∃ ticket, actual.event = .serve ticket none)
    (held : P.retain actual.before monitor.protection = some (.timer actor)) :
    M.advanceProtection config monitor actual = some (.timer actor) ∧
      R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) =
        R.rank config.transfer.quantum actual.before monitor.protection ∧
      P.demand config actual.result.state (M.advanceProtection config monitor actual) =
        P.demand config actual.before monitor.protection := by
  cases value with
  | assignment facts => exact assignment facts held
  | service facts => exact service facts held
  | delivery facts =>
    rcases ordinary with ⟨index, ingress, event⟩ | ⟨ticket, event⟩
    · have impossible := facts.delivery.event.symm.trans event
      cases impossible
    · have impossible := facts.delivery.event.symm.trans event
      cases impossible

end Netlib.Check.CampusTCPStartupCriticalTimerJobs
