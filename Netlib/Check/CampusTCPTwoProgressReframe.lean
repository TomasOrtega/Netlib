import Netlib.Check.CampusTCPTwoProgressGatewayState
import Netlib.Check.CampusTCPWriteEnabled

/-!
# Retained startup and native checks at a later cut

Only transport state can change under these frames.
The startup source and native comparisons remain the actual earlier records.
-/

namespace Netlib.Check.CampusTCPTwoProgressReframe

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {gateway : Gateway}

def retain_basis (basis : StartupBasis cut) (retained : cut.report.steps <+: current.report.steps) : StartupBasis current :=
  { basis with
    retained := by
      obtain ⟨earlier, before⟩ := basis.retained
      have old : basis.report.steps <+: cut.report.steps := ⟨earlier, before.symm⟩
      obtain ⟨later, after⟩ := old.trans retained
      exact ⟨later, after.symm⟩ }

def gateway_start {basis : StartupBasis cut} {start : GatewayStart cut basis gateway}
    (value : CampusTCPTwoProgressGateway.Current start current)
    (retained : cut.report.steps <+: current.report.steps) : GatewayStart current (retain_basis basis retained) gateway := {
  session := value.session
  identity := start.identity.trans value.identity
  phase := value.phase
  trackerValid := value.trackerValid
  record := value.record
  member := value.member
  entry := value.entry
  confirmed := value.confirmed }

def native_path (native : CampusTCPRoundGateway.Native context before ingress entry direction hop)
    (after : CampusTCPService.Before) (same : before.environment = after.environment) :
    CampusTCPRoundGateway.Native context after ingress entry direction hop := by
  have configuration := congrArg CampusTCPService.Before.Environment.configuration same
  have guard := congrArg CampusTCPService.Before.Environment.guard same
  change before.configuration = after.configuration at configuration
  change before.guard = after.guard at guard
  refine {
    checks := native.checks.reframe after same
    budget := by rw [CampusTCPService.Checks.reframe_budget]; exact native.budget
    forwardComparison := by rw [CampusTCPService.Checks.reframe_forward_passed]; exact native.forwardComparison
    guardComparison := by rw [CampusTCPService.Checks.reframe_guard_passed]; exact native.guardComparison
    ingressPermit := ?_
    forwarding := ?_
    covered := native.covered }
  · rw [← guard]
    exact native.ingressPermit
  · rw [← configuration]
    exact native.forwarding

def native_env (native : NativeEnv cut gateway entry)
    (same : CampusTCPRoundEnvironment.environment cut.report.final = CampusTCPRoundEnvironment.environment current.report.final) :
    NativeEnv current gateway entry := by
  have owners := congrArg CampusTCPRoundEnvironment.Environment.owners same
  have paused := congrArg CampusTCPRoundEnvironment.Environment.assignmentPaused same
  have sealed := congrArg CampusTCPRoundEnvironment.Environment.primarySealed same
  have fenced := congrArg CampusTCPRoundEnvironment.Environment.primaryFenced same
  have installed := congrArg CampusTCPRoundEnvironment.Environment.installed same
  change cut.report.final.owners = current.report.final.owners at owners
  change cut.report.final.assignmentPaused = current.report.final.assignmentPaused at paused
  change cut.report.final.primarySealed = current.report.final.primarySealed at sealed
  change cut.report.final.primaryFenced = current.report.final.primaryFenced at fenced
  change cut.report.final.installation.isSome = current.report.final.installation.isSome at installed
  refine {
    ingress := native.ingress
    paths := fun actor => native_path (native.paths actor) _ (CampusTCPRoundEnvironment.service_environment _ _ same gateway)
    owners := ?_
    configured := native.configured
    unpaused := paused.symm.trans native.unpaused
    primary := ?_
    standby := ?_ }
  · intro actor
    change current.report.final.owners.get actor.leg = gateway
    rw [← owners]
    exact native.owners actor
  · intro primary
    obtain ⟨oldSealed, oldFenced⟩ := native.primary primary
    exact ⟨sealed.symm.trans oldSealed, fenced.symm.trans oldFenced⟩
  · intro standby
    obtain ⟨old, previous, oldSealed, oldFenced⟩ := native.standby standby
    have present : current.report.final.installation.isSome = true := by
      rw [← installed, previous]
      rfl
    obtain ⟨next, selected⟩ := Option.isSome_iff_exists.mp present
    exact ⟨next, selected, sealed.symm.trans oldSealed, fenced.symm.trans oldFenced⟩

def native_entry (native : NativeEnv cut gateway before) (same : after = before) : NativeEnv cut gateway after :=
  same.symm ▸ native

def write_native {actor : Actor} {bytes : List UInt8} {actual : Step input}
    (value : CampusTCPWriteEnabled.WriteMove cut actor bytes actual) (native : NativeEnv cut gateway entry) :
    NativeEnv value.move.after gateway entry := native_env native value.environment

end Netlib.Check.CampusTCPTwoProgressReframe
