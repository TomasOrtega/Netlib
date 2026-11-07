import Netlib.Check.CampusTCPTransferEnabled
import Netlib.Check.CampusTCPTwoTransferMonitor
import Netlib.Check.CampusTCPRecoveryRoundPhaseBase

/-!
# Current control guards survive clock slots

The guards use current transport state and transfer metadata.
Clock slots preserve those fields and retain the actual endpoint cursors.
-/

namespace Netlib.Check.CampusTCPTwoTransferGuards

open CampusTCPModel
open CampusTCPRound (Cut)
open CampusTCPTwoTransferMonitor (Control)

namespace T
export CampusTCPTransferEnabled
  (PauseReady StageReady InstallReady RouteReady FenceReady ResumeReady)
end T

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {current next : Cut input complete}
variable {control : Control}

def Ready (state : State input) : Control → Prop
  | .pause => T.PauseReady state
  | .capture => T.StageReady state
  | .install => T.InstallReady state
  | .clientRoute | .serverRoute => T.RouteReady state
  | .fence => T.FenceReady state
  | .resume => T.ResumeReady state

theorem clock (placement : CampusTCPRecoveryRoundPhaseBase.At current next)
    (ready : Ready current.report.final control) : Ready next.report.final control := by
  have history := congrArg (fun resident : Local => resident.history.length) placement.frame.primary
  cases control <;> cases ready <;> constructor
  all_goals first
    | assumption
    | (simpa only [placement.frame.assignmentPaused, placement.frame.primarySealed,
        placement.frame.primaryFenced, placement.frame.primary, placement.frame.standby,
        placement.frame.owners, placement.frame.installation, placement.frame.cache,
        State.outstanding, placement.frame.work, history] using (by assumption))

def event (input : Input) : Control → Event
  | .pause => .pause
  | .capture => .stageCheckpoint
  | .install => .installCheckpoint (input.deployment .standby).executionNS
  | .clientRoute => .switchRoute .client .standby
  | .serverRoute => .switchRoute .server .standby
  | .fence => .fencePrimary
  | .resume => .resume

theorem enabled (control : Control) (ready : Ready current.report.final control) :
    ∃ actual, Nonempty (CampusTCPTransferEnabled.Control current (event input control) actual) := by
  cases control with
  | pause => exact CampusTCPTransferEnabled.pause_at ready
  | capture =>
    obtain ⟨actual, _, move, _⟩ := CampusTCPTransferEnabled.stage_at ready
    exact ⟨actual, move⟩
  | install =>
    obtain ⟨actual, _, move, _⟩ := CampusTCPTransferEnabled.install_at ready
    exact ⟨actual, move⟩
  | clientRoute => exact CampusTCPTransferEnabled.route_at ready .client
  | serverRoute => exact CampusTCPTransferEnabled.route_at ready .server
  | fence => exact CampusTCPTransferEnabled.fence_at ready
  | resume => exact CampusTCPTransferEnabled.resume_at ready

theorem event_config (config : CampusTCPTwoTransferMonitor.Config)
    (namespaceEq : config.executionNS = (input.deployment .standby).executionNS) (control : Control) :
    control.event config = event input control := by
  cases control <;> first | rfl | exact congrArg Event.installCheckpoint namespaceEq

end Netlib.Check.CampusTCPTwoTransferGuards
