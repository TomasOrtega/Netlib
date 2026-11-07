import Netlib.Check.CampusTCPStartupCurrentAt
import Netlib.Check.CampusTCPStartupJobSource
import Netlib.Check.CampusTCPRoundAssignment
import Netlib.Check.CampusTCPRecoveryStartupServiceEnabled
import Netlib.Check.CampusTCPRecoveryStartupLinkDelivery

/-!
# Enabled jobs at an actual whole-report drive cut

The same Actions check derives current native readiness. Each result retains
its actual assignment, gateway emission, or endpoint receipt.
-/

namespace Netlib.Check.CampusTCPStartupDriveJobsEnabled

open Packet Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupServiceEnabled (PathsAligned Service)
open CampusTCPRecoveryStartupLinkDelivery (Delivered)
open CampusTCPRecoveryStartupReceiveFields (PassiveTarget)

namespace J
export CampusTCPStartupJobs (Job Source PacketItem inventory)
end J
namespace E
export CampusTCPStartupTransferExecution (initial monitorAt actions)
end E
namespace P
export CampusTCPStartupMonitor (Monitor)
end P
namespace A
export CampusTCPRoundAssignment (AssignmentFacts)
end A

variable {input : Input} {events : List CampusTCPModel.Event} {whole : Report input events}
variable {config : CampusTCPStartupTransferMonitor.Config} {monitor : P.Monitor} {count : Nat}
variable {current : C.State input.active input.passive} {report : Report input events}

inductive Run (config : CampusTCPStartupTransferMonitor.Config) (report : Report input events)
    (current : C.State input.active input.passive) : J.Job input → Step input → Type where
  | assignment {item index source payload actual}
      (facts : A.AssignmentFacts report.final index (config.transfer.ingress .primary (Actor.ofRecovery source.occurrence.actor)) source.produced actual) :
      Run config report current (.ingress item index source payload) actual
  | service {item source production actual} (facts : Service report item actual) :
      Run config report current (.ticket item source production) actual
  | delivery {item index served emission emitted source production payload actual}
      (facts : Delivered report current source index served emission actual) :
      Run config report current (.link item index served emission emitted source production payload) actual

theorem Run.before (value : Run config report current job actual) : actual.before = report.final := by
  cases value with
  | assignment facts => exact facts.beforeEq
  | service facts => exact facts.before
  | delivery facts => exact facts.delivery.before

theorem Run.event (value : Run config report current job actual) : actual.event = CampusTCPStartupSelection.Job.event config job := by
  cases value with
  | assignment facts => exact facts.event
  | service facts => exact facts.event
  | delivery facts => exact facts.delivery.event

theorem Run.supported (value : Run config report current job actual) : actual.result.supported = true := by
  cases value with
  | assignment facts => exact facts.supported
  | service facts => exact facts.supported
  | delivery facts => exact facts.delivery.supported

theorem Run.passed (value : Run config report current job actual) : actual.result.passed = true := by
  cases value with
  | assignment facts => exact facts.passed
  | service facts => exact facts.passed
  | delivery facts => exact facts.delivery.passed

def Run.on_step (value : Run config report current job actual) (supplied : Step input)
    (before : supplied.before = report.final) (event : supplied.event = CampusTCPStartupSelection.Job.event config job) :
    Run config report current job supplied := by
  have firstBefore := value.before.trans before.symm
  have firstEvent := value.event.trans event.symm
  have computed := actual.computed
  rw [firstBefore, firstEvent, supplied.computed] at computed
  have result : actual.result = supplied.result := (Except.ok.inj computed).symm
  have same : actual = supplied := by
    cases actual
    cases supplied
    simp_all only
  exact same ▸ value

private theorem route_ready (report : Report input events) (cold : CampusTCPRecoveryStartupCold.ColdProfile report)
    (actor : Actor) : CampusTCPEnabled.RouteReady report.final actor := by
  have owners := CampusTCPStartupPrimaryServices.Trace.cold_owners report.trace cold
  have owner : report.final.owner actor = .primary := by
    change report.final.owners.get actor.leg = .primary
    rw [owners]
    cases actor <;> rfl
  have fields := CampusTCPStartupControlFrames.Report.control_fields report cold
  refine ⟨fields.1, ?_, ?_, ?_⟩
  · rw [owner]
    rfl
  · exact fun _ => ⟨fields.2.1, fields.2.2.1⟩
  · rw [owner]
    intro impossible
    cases impossible

variable (profile : CampusTCPStartupNative.Profile (input.contextFor .primary)
  (beforeService input (CampusTCPSchedule.stateAt input.initial whole.steps config.startup.preparation.length) .primary)
  input.zone (Handshake.outbound input.active config.startup.remote))

private theorem enabled (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (within : count ≤ whole.steps.length)
    (ending : E.monitorAt config (E.initial config) whole.steps count = .startup monitor)
    (located : CampusTCPStartupCurrentAt.At whole config count within profile)
    (paths : PathsAligned config profile) (valid : input.passive.Valid)
    (target : PassiveTarget profile.entry input.passive)
    (job : J.Job input) (member : job ∈ J.inventory (CampusTCPSchedule.Report.cut whole count within).final) :
    ∃ actual, Nonempty (Run config (CampusTCPSchedule.Report.cut whole count within) located.current job actual) := by
  let currentReport := CampusTCPSchedule.Report.cut whole count within
  have pending := CampusTCPStartupJobs.inventory_pending member
  cases job with
  | ingress item index source payload =>
    have found := CampusTCPStartupJobSource.Report.job_lookup currentReport (.ingress item index source payload) member
    have ingress : CampusTCPEnabled.IngressPending currentReport.final index :=
      ⟨item, pending, by simp only [payload, Transit.ingressAt, beq_self_eq_true]⟩
    obtain ⟨actual, facts⟩ := CampusTCPRoundAssignment.Report.assign_enabled currentReport index
      (config.transfer.ingress .primary (Actor.ofRecovery source.occurrence.actor)) source.produced found
      (route_ready currentReport located.value.cold source.produced.actor) ingress
    exact ⟨actual, ⟨.assignment facts⟩⟩
  | ticket item source production =>
    obtain ⟨actual, ⟨facts⟩⟩ := CampusTCPRecoveryStartupServiceEnabled.serve_at whole prep actions within ending
      located.value paths item source production pending
    exact ⟨actual, ⟨.service facts⟩⟩
  | link item index served emission emitted source production payload =>
    obtain ⟨actual, ⟨facts⟩⟩ := CampusTCPRecoveryStartupLinkDelivery.deliver located.value valid target
      item index served emission emitted source production payload pending
    exact ⟨actual, ⟨.delivery facts⟩⟩

theorem job_at (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (within : count ≤ whole.steps.length)
    (ending : E.monitorAt config (E.initial config) whole.steps count = .startup monitor) (drive : monitor.mode = .drive)
    (paths : PathsAligned config profile) (valid : input.passive.Valid)
    (target : PassiveTarget profile.entry input.passive)
    (job : J.Job input) (member : job ∈ J.inventory (CampusTCPSchedule.Report.cut whole count within).final) :
    ∃ current actual, Nonempty (Run config (CampusTCPSchedule.Report.cut whole count within) current job actual) := by
  obtain ⟨located⟩ := CampusTCPStartupCurrentAt.at_drive profile prep actions within ending drive
  obtain ⟨actual, result⟩ := enabled profile prep actions within ending located paths valid target job member
  exact ⟨located.current, actual, result⟩

theorem job_on_step (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (within : count ≤ whole.steps.length)
    (ending : E.monitorAt config (E.initial config) whole.steps count = .startup monitor) (drive : monitor.mode = .drive)
    (paths : PathsAligned config profile) (valid : input.passive.Valid)
    (target : PassiveTarget profile.entry input.passive)
    (job : J.Job input) (member : job ∈ J.inventory (CampusTCPSchedule.Report.cut whole count within).final)
    (actual : Step input) (before : actual.before = CampusTCPSchedule.stateAt input.initial whole.steps count)
    (event : actual.event = CampusTCPStartupSelection.Job.event config job) :
    ∃ current, Nonempty (Run config (CampusTCPSchedule.Report.cut whole count within) current job actual) := by
  obtain ⟨current, selected, ⟨result⟩⟩ := job_at profile prep actions within ending drive paths valid target job member
  exact ⟨current, ⟨result.on_step actual before event⟩⟩

theorem allowed_step (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (within : count ≤ whole.steps.length)
    (ending : E.monitorAt config (E.initial config) whole.steps count = .startup monitor) (drive : monitor.mode = .drive)
    (paths : PathsAligned config profile) (valid : input.passive.Valid)
    (target : PassiveTarget profile.entry input.passive)
    (actual : Step input) (before : actual.before = CampusTCPSchedule.stateAt input.initial whole.steps count)
    (allowed : CampusTCPStartupSelection.jobAllowed config actual.before actual.event = true) :
    ∃ current job, job ∈ J.inventory (CampusTCPSchedule.Report.cut whole count within).final ∧
      Nonempty (Run config (CampusTCPSchedule.Report.cut whole count within) current job actual) := by
  obtain ⟨job, member, event⟩ := List.any_eq_true.mp allowed
  have selected : actual.event = CampusTCPStartupSelection.Job.event config job := (of_decide_eq_true event).symm
  have present : job ∈ J.inventory (CampusTCPSchedule.Report.cut whole count within).final := by simpa only [before, CampusTCPSchedule.Report.cut] using member
  obtain ⟨current, result⟩ := job_on_step profile prep actions within ending drive paths valid target job present actual before selected
  exact ⟨current, job, present, result⟩


theorem job_on_step_at (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (within : count ≤ whole.steps.length)
    (ending : E.monitorAt config (E.initial config) whole.steps count = .startup monitor) (drive : monitor.mode = .drive)
    (paths : PathsAligned config profile) (valid : input.passive.Valid)
    (target : PassiveTarget profile.entry input.passive)
    (job : J.Job input) (member : job ∈ J.inventory (CampusTCPSchedule.Report.cut whole count within).final)
    (actual : Step input) (before : actual.before = CampusTCPSchedule.stateAt input.initial whole.steps count)
    (event : actual.event = CampusTCPStartupSelection.Job.event config job) :
    ∃ located : CampusTCPStartupCurrentAt.At whole config count within profile,
      Nonempty (Run config (CampusTCPSchedule.Report.cut whole count within) located.current job actual) := by
  obtain ⟨located⟩ := CampusTCPStartupCurrentAt.at_drive profile prep actions within ending drive
  obtain ⟨selected, ⟨result⟩⟩ := enabled profile prep actions within ending located paths valid target job member
  exact ⟨located, ⟨result.on_step actual before event⟩⟩

end Netlib.Check.CampusTCPStartupDriveJobsEnabled
