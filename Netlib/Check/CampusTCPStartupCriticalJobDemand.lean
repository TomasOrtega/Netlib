import Netlib.Check.CampusTCPStartupJobEvent
import Netlib.Check.CampusTCPStartupCriticalJobStep

/-!
# Serving the current startup job strictly decreases its critical rank

Actual queue references identify the demanded output before no-copy uniqueness applies.
-/

namespace Netlib.Check.CampusTCPStartupCriticalJobDemand

open Protocol.TCP CampusTCPModel CampusTCPStartupJobs

namespace P
export CampusTCPStartupSelection (phaseRank path retain demand timerDemand criticalTimer)
end P
namespace R
export CampusTCPStartupCriticalRank (rank)
end R
namespace M
export CampusTCPStartupMonitor (Monitor advanceProtection)
end M
namespace J
export CampusTCPStartupDriveJobsEnabled (Run)
end J

variable {input : Input} {events : List Event} {report : Report input events}
variable {current : TCPHandshakeRecovery.State input.active input.passive} {actual : Step input}
variable {config : CampusTCPStartupTransferMonitor.Config} {monitor : M.Monitor}

private theorem critical_exists (phase : P.phaseRank state = 1 ∨ P.phaseRank state = 2 ∨ P.phaseRank state = 3) :
    ∃ actor, P.criticalTimer state = some actor := by
  rcases phase with first | second | third
  · exact ⟨.client, by simp only [P.criticalTimer, first]⟩
  · exact ⟨.server, by simp only [P.criticalTimer, second]⟩
  · exact ⟨.server, by simp only [P.criticalTimer, third]⟩

private theorem timer_not_job (job : Job input)
    (selected : P.timerDemand quantum state actor = some (CampusTCPStartupSelection.Job.event config job)) : False := by
  cases job <;> simp only [CampusTCPStartupSelection.Job.event, P.timerDemand] at selected
  all_goals
    split at selected
    · cases selected
    · split at selected
      · split at selected <;> cases selected
      · cases selected

theorem strict (run : J.Run config report current job actual)
    (connected : report.final.connection = .recovering current)
    (nocopy : ∀ actual ∈ report.steps, ∀ id, actual.event ≠ .copyPacket id)
    (member : job ∈ inventory report.final)
    (phase : P.phaseRank actual.before = 1 ∨ P.phaseRank actual.before = 2 ∨ P.phaseRank actual.before = 3)
    (monitor : M.Monitor)
    (demanded : P.demand config actual.before monitor.protection = some actual.event) :
    R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) <
      R.rank config.transfer.quantum actual.before monitor.protection := by
  have linear : CampusTCPStartupJobUnique.Linear actual.before := by
    rw [run.before]
    exact CampusTCPStartupJobUnique.Report.linear report nocopy
  have actualMember : job ∈ inventory actual.before := by rw [run.before]; exact member
  have pending := inventory_pending member
  have incomplete : P.phaseRank actual.before ≠ 4 := by rcases phase with first | second | third <;> omega
  rcases CampusTCPStartupCriticalDemand.effective_cases linear (critical_exists phase) (held := monitor.protection) with
    ⟨index, heldJob, retained, selected⟩ | ⟨actor, retained, timer⟩
  · have oldEvent : CampusTCPStartupSelection.Job.event config heldJob = actual.event := by
      simpa only [P.demand, retained, selected, Option.map_some, Option.some.injEq] using demanded
    have heldMember : heldJob ∈ inventory report.final := by
      rw [← run.before]
      exact CampusTCPStartupSelection.selected_member selected
    have sameOutput := CampusTCPStartupJobEvent.Report.same_event_output report heldJob job heldMember member
      (oldEvent.trans run.event)
    have same : heldJob = job := linear.job_eq (CampusTCPStartupSelection.selected_member selected) actualMember sameOutput
    subst heldJob
    have held : P.retain actual.before monitor.protection = some (.path job.outputIndex) := by
      rw [CampusTCPStartupSelection.selected_index selected]
      exact retained
    have present : P.path actual.before job.outputIndex = some job := by
      rw [CampusTCPStartupSelection.selected_index selected]
      exact selected
    cases run with
    | @assignment item index source payload actual facts =>
      exact CampusTCPStartupCriticalQueueRank.assignment_strict actual report facts.beforeEq nocopy item index source payload pending
        facts.event monitor held incomplete
    | @service item source production actual facts =>
      exact CampusTCPStartupCriticalQueueRank.service_strict actual report facts.before nocopy item source production pending facts.event
        facts.served facts.recorded facts.emission facts.emitted monitor held incomplete
    | delivery facts =>
      exact CampusTCPStartupCriticalLinkStep.strict facts connected nocopy pending incomplete held present
  · have selected : P.timerDemand config.transfer.quantum actual.before actor = some actual.event := by
      simpa only [P.demand, retained] using demanded
    rw [run.event] at selected
    exact False.elim (timer_not_job job selected)

end Netlib.Check.CampusTCPStartupCriticalJobDemand
