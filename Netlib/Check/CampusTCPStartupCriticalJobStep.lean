import Netlib.Check.CampusTCPStartupCriticalQueueOther
import Netlib.Check.CampusTCPStartupCriticalDeliveryOther
import Netlib.Check.CampusTCPStartupCriticalTimerJobs
import Netlib.Check.CampusTCPStartupCriticalTimerReceive
import Netlib.Check.CampusTCPStartupCriticalReceiveAdvance
import Netlib.Check.CampusTCPStartupCriticalLinkStep

/-!
# Critical rank laws for the same actual startup job

A phase advance or selected path step lowers the rank. Equal rank keeps the demand.
-/

namespace Netlib.Check.CampusTCPStartupCriticalJobStep

open Protocol.TCP CampusTCPModel CampusTCPStartupJobs

namespace P
export CampusTCPStartupSelection (phaseRank path retain demand criticalTimer)
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
namespace U
export CampusTCPStartupJobUnique (Linear)
end U
namespace Q
export CampusTCPStartupCriticalQueueOther (PathFrame)
end Q

variable {input : Input} {events : List Event} {report : Report input events}
variable {current : TCPHandshakeRecovery.State input.active input.passive} {actual : Step input}
variable {config : CampusTCPStartupTransferMonitor.Config} {monitor : M.Monitor}

def Law (config : CampusTCPStartupTransferMonitor.Config) (monitor : M.Monitor) (actual : Step input) : Prop :=
  R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) ≤
      R.rank config.transfer.quantum actual.before monitor.protection ∧
    (R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) =
      R.rank config.transfer.quantum actual.before monitor.protection →
      P.demand config actual.result.state (M.advanceProtection config monitor actual) =
        P.demand config actual.before monitor.protection)

private theorem strict_law
    (strict : R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) <
      R.rank config.transfer.quantum actual.before monitor.protection) : Law config monitor actual := by
  constructor
  · omega
  · intro equal
    omega

private theorem equal_law
    (equal : R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) =
      R.rank config.transfer.quantum actual.before monitor.protection)
    (pending : P.demand config actual.result.state (M.advanceProtection config monitor actual) =
      P.demand config actual.before monitor.protection) : Law config monitor actual :=
  ⟨Nat.le_of_eq equal, fun _ => pending⟩

private theorem frame_law (frame : Q.PathFrame job actual) (linear : U.Linear actual.before)
    (retained : P.retain actual.before monitor.protection = some (.path job.outputIndex)) : Law config monitor actual :=
  equal_law (frame.rank linear monitor retained) (frame.pending linear monitor retained)

private theorem same_job (linear : U.Linear state) (member : job ∈ inventory state)
    (selected : P.path state index = some heldJob) (same : job.outputIndex = index) : heldJob = job :=
  linear.job_eq (CampusTCPStartupSelection.selected_member selected) member
    ((CampusTCPStartupSelection.selected_index selected).trans same.symm)

private theorem path_at_index (selected : P.path state index = some job) : P.path state job.outputIndex = some job := by
  rw [CampusTCPStartupSelection.selected_index selected]
  exact selected

private theorem held_at_index (selected : P.path state index = some job)
    (retained : P.retain state held = some (.path index)) : P.retain state held = some (.path job.outputIndex) := by
  rw [CampusTCPStartupSelection.selected_index selected]
  exact retained

private theorem critical_exists (phase : P.phaseRank state = 1 ∨ P.phaseRank state = 2 ∨ P.phaseRank state = 3) :
    ∃ actor, P.criticalTimer state = some actor := by
  rcases phase with first | second | third
  · exact ⟨.client, by simp only [P.criticalTimer, first]⟩
  · exact ⟨.server, by simp only [P.criticalTimer, second]⟩
  · exact ⟨.server, by simp only [P.criticalTimer, third]⟩

theorem step (run : J.Run config report current job actual)
    (connected : report.final.connection = .recovering current)
    (nocopy : ∀ actual ∈ report.steps, ∀ id, actual.event ≠ .copyPacket id)
    (member : job ∈ inventory report.final)
    (phase : P.phaseRank actual.before = 1 ∨ P.phaseRank actual.before = 2 ∨ P.phaseRank actual.before = 3)
    (monitor : M.Monitor) : Law config monitor actual := by
  have before := run.before
  have linear : U.Linear actual.before := by rw [before]; exact CampusTCPStartupJobUnique.Report.linear report nocopy
  have beforeMember : job ∈ inventory actual.before := by rw [before]; exact member
  have pending := inventory_pending member
  have incomplete : P.phaseRank actual.before ≠ 4 := by rcases phase with first | second | third <;> omega
  have effective := CampusTCPStartupCriticalDemand.effective_cases linear (critical_exists phase) (held := monitor.protection)
  cases run with
  | @assignment item index source payload actual facts =>
    rcases effective with ⟨heldIndex, heldJob, retained, selected⟩ | ⟨actor, retained, timer⟩
    · by_cases same : index = heldIndex
      · have sameJob := same_job linear beforeMember selected same
        subst heldJob
        apply strict_law
        exact CampusTCPStartupCriticalQueueRank.assignment_strict actual report facts.beforeEq nocopy item index source
          payload pending facts.event monitor (held_at_index selected retained) incomplete
      · have different : index ≠ heldJob.outputIndex := by
          simpa only [CampusTCPStartupSelection.selected_index selected] using same
        have frame := CampusTCPStartupCriticalQueueOther.assignment_frame actual report facts.beforeEq nocopy
          (path_at_index selected) different facts.event
        exact frame_law frame linear (held_at_index selected retained)
    · have frame := CampusTCPStartupCriticalTimerJobs.assignment (config := config) (monitor := monitor) facts retained
      exact equal_law frame.2.1 frame.2.2
  | @service item source production actual facts =>
    rcases effective with ⟨heldIndex, heldJob, retained, selected⟩ | ⟨actor, retained, timer⟩
    · by_cases same : item.value.outputIndex = heldIndex
      · have sameJob := same_job linear beforeMember selected same
        subst heldJob
        apply strict_law
        exact CampusTCPStartupCriticalQueueRank.service_strict actual report facts.before nocopy item source production
          pending facts.event facts.served facts.recorded facts.emission facts.emitted monitor
          (held_at_index selected retained) incomplete
      · have different : facts.served.ticket.value.outputIndex ≠ heldJob.outputIndex := by
          rw [facts.ticket]
          simpa only [CampusTCPStartupSelection.selected_index selected] using same
        have frame := CampusTCPStartupCriticalQueueOther.service_frame actual report facts.before nocopy
          (path_at_index selected) facts.event facts.served facts.recorded different
        exact frame_law frame linear (held_at_index selected retained)
    · have frame := CampusTCPStartupCriticalTimerJobs.service (config := config) (monitor := monitor) facts retained
      exact equal_law frame.2.1 frame.2.2
  | @delivery item index served emission emitted source production payload actual facts =>
    by_cases advance : P.phaseRank actual.before < P.phaseRank actual.result.state
    · exact strict_law (CampusTCPStartupCriticalReceiveAdvance.strict facts connected nocopy phase advance)
    · have monotone := CampusTCPStartupCriticalReceiveAdvance.nondecrease facts connected
      have sameLevel : P.phaseRank actual.result.state = P.phaseRank actual.before := by omega
      rcases effective with ⟨heldIndex, heldJob, retained, selected⟩ | ⟨actor, retained, timer⟩
      · by_cases same : served.ticket.value.outputIndex = heldIndex
        · have sameJob := same_job linear beforeMember selected same
          subst heldJob
          apply strict_law
          exact CampusTCPStartupCriticalLinkStep.strict facts connected nocopy pending incomplete
            (held_at_index selected retained) (path_at_index selected)
        · have different : served.ticket.value.outputIndex ≠ heldJob.outputIndex := by
            simpa only [CampusTCPStartupSelection.selected_index selected] using same
          have frame := CampusTCPStartupCriticalDeliveryOther.delivery_frame actual report facts.delivery.before nocopy
            (path_at_index selected) item index served emission emitted payload pending different facts.delivery.event sameLevel
          exact frame_law frame linear (held_at_index selected retained)
      · exact equal_law
          (CampusTCPStartupCriticalTimerReceive.rank_eq facts connected sameLevel retained)
          (CampusTCPStartupCriticalTimerReceive.persistent facts connected sameLevel retained)

theorem nonincrease (run : J.Run config report current job actual)
    (connected : report.final.connection = .recovering current)
    (nocopy : ∀ actual ∈ report.steps, ∀ id, actual.event ≠ .copyPacket id)
    (member : job ∈ inventory report.final)
    (phase : P.phaseRank actual.before = 1 ∨ P.phaseRank actual.before = 2 ∨ P.phaseRank actual.before = 3)
    (monitor : M.Monitor) :
    R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) ≤
      R.rank config.transfer.quantum actual.before monitor.protection :=
  (step run connected nocopy member phase monitor).1

theorem persistent (run : J.Run config report current job actual)
    (connected : report.final.connection = .recovering current)
    (nocopy : ∀ actual ∈ report.steps, ∀ id, actual.event ≠ .copyPacket id)
    (member : job ∈ inventory report.final)
    (phase : P.phaseRank actual.before = 1 ∨ P.phaseRank actual.before = 2 ∨ P.phaseRank actual.before = 3)
    (monitor : M.Monitor)
    (equal : R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) =
      R.rank config.transfer.quantum actual.before monitor.protection) :
    P.demand config actual.result.state (M.advanceProtection config monitor actual) =
      P.demand config actual.before monitor.protection :=
  (step run connected nocopy member phase monitor).2 equal

end Netlib.Check.CampusTCPStartupCriticalJobStep
