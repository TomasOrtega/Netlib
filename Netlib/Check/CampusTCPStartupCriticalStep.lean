import Netlib.Check.CampusTCPStartupCriticalClockStep
import Netlib.Check.CampusTCPStartupCriticalTimeoutStep
import Netlib.Check.CampusTCPStartupCriticalJobDemand

/-!
# Critical rank laws at an actual whole-report drive slot

One Actions check supplies the current allowed event.
The fixed native profile derives each actual job or due timeout.
-/

namespace Netlib.Check.CampusTCPStartupCriticalStep

open Packet Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupServiceEnabled (PathsAligned)
open CampusTCPRecoveryStartupReceiveFields (PassiveTarget)

namespace E
export CampusTCPStartupTransferExecution (initial monitorAt actions actions_correct allowed)
end E
namespace M
export CampusTCPStartupMonitor (Monitor allowed advanceProtection)
end M
namespace P
export CampusTCPStartupSelection (phaseRank demand allowed jobAllowed timeoutAllowed timer clockAllowed)
end P
namespace R
export CampusTCPStartupCriticalRank (rank)
end R
namespace J
export CampusTCPStartupDriveJobsEnabled (Run job_on_step_at)
end J
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

structure Law (config : CampusTCPStartupTransferMonitor.Config) (monitor : M.Monitor) (actual : Step input) : Prop where
  nonincrease : R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) ≤
    R.rank config.transfer.quantum actual.before monitor.protection
  persistent : R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) =
      R.rank config.transfer.quantum actual.before monitor.protection →
    P.demand config actual.result.state (M.advanceProtection config monitor actual) =
      P.demand config actual.before monitor.protection
  served : P.demand config actual.before monitor.protection = some actual.event →
    R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) <
      R.rank config.transfer.quantum actual.before monitor.protection

variable {input : Input} {events : List CampusTCPModel.Event} {whole : Report input events}
variable {config : CampusTCPStartupTransferMonitor.Config} {monitor : M.Monitor} {count : Nat}
variable {report : Report input events} {current : C.State input.active input.passive} {actual : Step input}

private theorem timeout_value (report : Report input events)
    (connected : report.final.connection = .recovering current)
    (before : actual.before = report.final) (event : actual.event = .startupTimeout actor generation true)
    (permitted : P.timeoutAllowed actual.before actor generation = true) :
    ∃ flight, Nonempty (CampusTCPRecoveryStartupTimeoutEnabled.Timeout report current actor generation flight actual) := by
  have allowed := permitted
  simp only [P.timeoutAllowed, P.timer, before, connected] at allowed
  cases status : (current.timer actor.recoverySide).status with
  | idle | acknowledged flight atTime => simp only [status] at allowed; cases allowed
  | pending flight =>
    have fields : generation = flight.retries ∧ flight.deadline ≤ (current.timer actor.recoverySide).now :=
      of_decide_eq_true (by simpa only [status] using allowed)
    obtain ⟨enabled, ⟨value⟩⟩ := CampusTCPRecoveryStartupTimeoutEnabled.timeout_current report connected status fields.1 fields.2
    exact ⟨flight, ⟨value.on_step actual before event⟩⟩

private theorem other_job (permitted : P.allowed config state held event = true)
    (notClock : ¬∃ actor millis, event = .startupClock actor millis)
    (notTimeout : ¬∃ actor generation, event = .startupTimeout actor generation true)
    (notFinish : event ≠ .finishStartup) (notDrop : ∀ id, event ≠ .dropPacket id) :
    P.jobAllowed config state event = true := by
  cases event with
  | startupClock actor millis => exact False.elim (notClock ⟨actor, millis, rfl⟩)
  | startupTimeout actor generation policy =>
    cases policy
    · exact permitted
    · exact False.elim (notTimeout ⟨actor, generation, rfl⟩)
  | finishStartup => exact False.elim (notFinish rfl)
  | dropPacket id => exact False.elim (notDrop id rfl)
  | _ => exact permitted

variable (profile : CampusTCPStartupNative.Profile (input.contextFor .primary)
  (beforeService input (S.stateAt input.initial whole.steps config.startup.preparation.length) .primary)
  input.zone (Handshake.outbound input.active config.startup.remote))

theorem at_slot (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (inside : count < whole.steps.length)
    (ending : E.monitorAt config (E.initial config) whole.steps count = .startup monitor)
    (drive : monitor.mode = .drive) (paths : PathsAligned config profile) (valid : input.passive.Valid)
    (target : PassiveTarget profile.entry input.passive)
    (actual : Step input) (found : whole.steps[count]? = some actual)
    (phases : P.phaseRank actual.before = 1 ∨ P.phaseRank actual.before = 2 ∨ P.phaseRank actual.before = 3)
    (positive : 0 < config.transfer.quantum) (nodrop : ∀ id, actual.event ≠ .dropPacket id) :
    Law config monitor actual := by
  obtain ⟨head, selected, before, eventAt, _⟩ := CampusTCPSchedule.Trace.at whole.trace count inside
  have same : head = actual := Option.some.inj (selected.symm.trans found)
  subst head
  let within : count ≤ whole.steps.length := Nat.le_of_lt inside
  let currentReport := CampusTCPSchedule.Report.cut whole count within
  have cutBefore : actual.before = currentReport.final := before
  have permitted := (E.actions_correct _ _ _ _).mp actions count inside
  rw [ending] at permitted
  have allowed : P.allowed config actual.before monitor.protection actual.event = true := by
    simpa only [E.allowed, M.allowed, drive, ← before, ← eventAt] using permitted
  have nocopy := CampusTCPStartupProfileFacts.Report.cut_no_copy whole prep actions within ending
  obtain ⟨located⟩ := CampusTCPStartupCurrentAt.at_drive profile prep actions within ending drive
  have connected : currentReport.final.connection = .recovering located.current := located.value.connected
  have connectedBefore : actual.before.connection = .recovering located.current := by rw [cutBefore]; exact connected
  by_cases clock : ∃ actor millis, actual.event = .startupClock actor millis
  · obtain ⟨actor, millis, event⟩ := clock
    have checked : P.clockAllowed config actual.before monitor.protection actor millis = true := by
      simpa only [P.allowed, event] using allowed
    exact ⟨CampusTCPStartupCriticalClockFrame.nonincrease currentReport cutBefore connectedBefore event checked,
      CampusTCPStartupCriticalClockFrame.persistent currentReport cutBefore connectedBefore event checked,
      CampusTCPStartupCriticalClockStep.served_strict connectedBefore positive event⟩
  by_cases timeout : ∃ actor generation, actual.event = .startupTimeout actor generation true
  · obtain ⟨actor, generation, event⟩ := timeout
    have checked : P.timeoutAllowed actual.before actor generation = true := by
      simpa only [P.allowed, event] using allowed
    obtain ⟨flight, ⟨value⟩⟩ := timeout_value currentReport connected cutBefore event checked
    have laws := CampusTCPStartupCriticalTimeoutStep.step_laws (monitor := monitor) currentReport connected nocopy value phases positive
    exact ⟨laws.1, laws.2,
      CampusTCPStartupCriticalTimeoutStep.served_strict currentReport connected nocopy value positive⟩
  have notFinish : actual.event ≠ .finishStartup := by
    intro event
    have demanded : P.demand config actual.before monitor.protection = some .finishStartup := by
      simpa only [P.allowed, event, decide_eq_true_eq] using allowed
    have complete := CampusTCPStartupCriticalDemand.finish_complete demanded
    rcases phases with first | second | third <;> omega
  have jobs := other_job allowed clock timeout notFinish nodrop
  obtain ⟨job, member, event⟩ := List.any_eq_true.mp jobs
  have actualEvent : actual.event = CampusTCPStartupSelection.Job.event config job := (of_decide_eq_true event).symm
  have currentMember : job ∈ CampusTCPStartupJobs.inventory currentReport.final := by
    simpa only [cutBefore] using member
  obtain ⟨current, ⟨run⟩⟩ := J.job_on_step_at profile prep actions within ending drive paths valid target
    job currentMember actual before actualEvent
  have laws := CampusTCPStartupCriticalJobStep.step run current.value.connected nocopy currentMember phases monitor
  exact ⟨laws.1, laws.2, CampusTCPStartupCriticalJobDemand.strict run current.value.connected nocopy currentMember phases monitor⟩

end Netlib.Check.CampusTCPStartupCriticalStep
