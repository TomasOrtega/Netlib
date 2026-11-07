import Netlib.Check.CampusTCPRecoveryStartupServiceEnabled
import Netlib.Check.CampusTCPRecoveredTransferTask

/-!
# Native transfer paths after the actual startup setup

Both deployments use the same installed candidate. Actual startup and setup
frames retain their policy checks and primary routing.
-/

namespace Netlib.Check.CampusTCPRecoveredNative

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPRecoveredSetup CampusTCPRecoveredSetupAppend
open CampusTCPRecoveryStartupCurrentNative (Current)
open CampusTCPRecoveryStartupCurrentEntry (History)
open CampusTCPRecoveryStartupServiceEnabled (PathsAligned)
open CampusTCPRecoveredTwoWriteInitial (Built)

namespace R
export CampusTCPRoundEnvironment (Environment environment TransportOnly)
end R
namespace N
export CampusTCPTwoTransferNative (Checks Routing)
end N
namespace E
export CampusTCPRecoveredTwoWriteEndpoints (cut)
end E

variable {input : Input} {baseEvents events : List CampusTCPModel.Event}
variable {base : Report input baseEvents} {report : Report input events}
variable {header : Header} {config : CampusTCPStartupTransferMonitor.Config}
variable {profile : CampusTCPStartupNative.Profile (input.contextFor .primary)
  (beforeService input base.final .primary) input.zone header}
variable {ready : DrainReady report} {archive : RecoveryArchive input.active input.passive}
variable {lower upper : List UInt8}

structure DataPaths (config : CampusTCPStartupTransferMonitor.Config)
    (profile : CampusTCPStartupNative.Profile (input.contextFor .primary)
      (beforeService input base.final .primary) input.zone header) where
  primary : PathsAligned config profile
  standby : ∀ actor : Actor, CampusTCPStartupNative.Path (input.contextFor .standby)
    (beforeService input base.final .standby) profile.entry actor.direction
  ingress : ∀ actor, (standby actor).ingress = config.transfer.ingress .standby actor
  hop : ∀ actor, (standby actor).hop = actor.nextHop
  configured : ∀ gateway, input.configured gateway = true

private def path_native (path : CampusTCPStartupNative.Path context before entry direction) :
    CampusTCPRoundGateway.Native context before path.ingress entry direction path.hop where
  checks := path.checks
  budget := path.budget
  forwardComparison := path.forwardComparison
  guardComparison := path.guardComparison
  ingressPermit := path.ingressPermit
  forwarding := by
    cases direction <;> exact ⟨rfl, path.route, path.forward, path.late⟩
  covered := path.covered

private theorem QuietAppend.environment {prior : Prefix input events archive}
    (value : QuietAppend prior actor event joint result) (transport : R.TransportOnly joint) :
    R.environment prior.report.final = R.environment value.next.report.final := by
  rw [value.final, ← value.before]
  exact CampusTCPRoundEnvironment.Step.environment value.actual (by rw [value.eventEq]; exact transport)

private theorem Drained.environment (drained : Drained ready archive) :
    R.environment report.final = R.environment drained.next.report.final := by
  rw [drained.final, ← drained.before]
  exact CampusTCPRoundEnvironment.Step.environment drained.actual (by rw [drained.event]; trivial)

private theorem Prepared.environment {start : Prefix input events archive} (value : Prepared start bytes) :
    R.environment start.report.final = R.environment value.next.report.final :=
  (QuietAppend.environment value.clientRecovery trivial).trans ((QuietAppend.environment value.serverRecovery trivial).trans
    ((QuietAppend.environment value.clientAck trivial).trans ((QuietAppend.environment value.serverAck trivial).trans
      (QuietAppend.environment value.written trivial))))

private theorem Built.entry (value : Current base profile report current)
    (drained : Drained ready archive) (prepared : Prepared drained.next (lower ++ upper))
    (built : Built drained prepared) : built.initial.gatewayState.session.entry = profile.entry := by
  have phase := built.initial.gatewayState.phase
  change (beforeService input prepared.next.report.final .primary).admission.phase =
    .data built.initial.gatewayState.session at phase
  rw [prepared.gateway_frame .primary, CampusTCPRecoveredSetupAppend.Drained.gateway_frame drained .primary] at phase
  exact value.entry _ (by rw [phase]; rfl)

def Built.checks (history : History base report) (value : Current base profile report current)
    (paths : DataPaths config profile) (drained : Drained ready archive)
    (prepared : Prepared drained.next (lower ++ upper)) (built : Built drained prepared) :
    N.Checks (E.cut prepared) built.initial.gatewayState.session.entry := by
  refine ⟨config.transfer.ingress, ?_, paths.configured⟩
  intro gateway actor
  rw [Built.entry value drained prepared built]
  have beforeFrame : (beforeService input base.final gateway).environment =
      (beforeService input prepared.next.report.final gateway).environment :=
    (CampusTCPRoundEnvironment.Trace.service_environment history.trace history.transport gateway).trans
      (congrArg CampusTCPService.Before.environment
        ((prepared.gateway_frame gateway).trans (CampusTCPRecoveredSetupAppend.Drained.gateway_frame drained gateway))).symm
  cases gateway with
  | primary =>
    have ingress : (profile.paths actor.direction).ingress = config.transfer.ingress .primary actor := by
      cases actor
      · exact paths.primary.ingress .active
      · exact paths.primary.ingress .passive
    have hop : (profile.paths actor.direction).hop = actor.nextHop := by
      cases actor
      · exact paths.primary.hop .active
      · exact paths.primary.hop .passive
    rw [← ingress, ← hop]
    exact CampusTCPTwoProgressReframe.native_path (path_native (profile.paths actor.direction)) _ beforeFrame
  | standby =>
    rw [← paths.ingress actor, ← paths.hop actor]
    exact CampusTCPTwoProgressReframe.native_path (path_native (paths.standby actor)) _ beforeFrame

@[simp] theorem Built.checks_ingress (history : History base report)
    (value : Current base profile report current) (paths : DataPaths config profile)
    (drained : Drained ready archive) (prepared : Prepared drained.next (lower ++ upper))
    (built : Built drained prepared) : (Built.checks history value paths drained prepared built).ingress = config.transfer.ingress := rfl

theorem Built.routing (value : Current base profile report current)
    (drained : Drained ready archive) (prepared : Prepared drained.next (lower ++ upper))
    (_built : Built drained prepared) : N.Routing (E.cut prepared) .primary := by
  have frame := (Drained.environment drained).trans (Prepared.environment prepared)
  have owners := congrArg CampusTCPRoundEnvironment.Environment.owners frame
  have paused := congrArg CampusTCPRoundEnvironment.Environment.assignmentPaused frame
  have sealed := congrArg CampusTCPRoundEnvironment.Environment.primarySealed frame
  have fenced := congrArg CampusTCPRoundEnvironment.Environment.primaryFenced frame
  have coldOwners := CampusTCPStartupPrimaryServices.Trace.cold_owners report.trace value.cold
  have fields := CampusTCPStartupControlFrames.Report.control_fields report value.cold
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro actor
    change prepared.next.report.final.owners.get actor.leg = .primary
    change report.final.owners = prepared.next.report.final.owners at owners
    rw [← owners, coldOwners]
    cases actor <;> rfl
  · exact paused.symm.trans fields.1
  · intro _
    exact ⟨sealed.symm.trans fields.2.1, fenced.symm.trans fields.2.2.1⟩
  · intro impossible
    cases impossible

end Netlib.Check.CampusTCPRecoveredNative
