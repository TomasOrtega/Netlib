import Netlib.Check.CampusTCPRevocation
import Netlib.Check.CampusTCPStartupTransferCheck

/-!
# The earlier cold-start transfer in the same revocation report

Native path checks concern the actual preparation cut.
The resulting transfer is a literal prefix of the unchanged whole report.
-/

namespace Netlib.Check.CampusTCPRevocation

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPRevocationTargets

variable {input : Input} {events : List CampusTCPModel.Event} {report : Report input events}
variable {config : CampusTCPStartupTransferMonitor.Config} {transferEnd triggerCut bound : Nat}
variable {targets : Targets input (cutState report triggerCut)}

def Result.transferReport (value : Result report config transferEnd triggerCut bound targets) :
    Report input ((report.steps.take transferEnd).map (·.event)) :=
  CampusTCPSchedule.Report.cut report transferEnd (Nat.le_trans (Nat.le_of_lt value.checked.order) value.checked.within)

theorem Result.transfer_length (value : Result report config transferEnd triggerCut bound targets) :
    value.transferReport.steps.length = transferEnd := by
  change (report.steps.take transferEnd).length = transferEnd
  rw [List.length_take, Nat.min_eq_left (Nat.le_trans (Nat.le_of_lt value.checked.order) value.checked.within)]

theorem Result.transfer_done (value : Result report config transferEnd triggerCut bound targets) :
    CampusTCPStartupTransferObserved.doneAt config value.transferReport.steps transferEnd = true := by
  change CampusTCPStartupTransferObserved.doneAt config (report.steps.take transferEnd) transferEnd = true
  unfold CampusTCPStartupTransferObserved.doneAt
  rw [CampusTCPRevocationPhased.monitorAt_take config _ report.steps transferEnd transferEnd (Nat.le_refl _)]
  exact value.checked.done

variable (value : Result report config transferEnd triggerCut bound targets)
variable (profile : CampusTCPStartupNative.Profile (input.contextFor .primary)
  (beforeService input (CampusTCPSchedule.stateAt input.initial value.transferReport.steps
    config.startup.preparation.length) .primary)
  input.zone (Handshake.outbound input.active config.startup.remote))

theorem Result.prior (prep : CampusTCPStartupProfile.Prep config.startup)
    (budget : config.transfer.lossAllowance ≤ 2)
    (prepared : config.startup.preparation.length ≤ value.transferReport.steps.length)
    (paths : CampusTCPRecoveredNative.DataPaths
      (base := CampusTCPStartupTransferObserved.preparation value.transferReport config prepared) config profile)
    (raw : CampusTCPRecoveredTransferTask.RawReserves input config.transfer.lower config.transfer.upper
      config.transfer.reverseLower config.transfer.reverseUpper)
    (namespaceEq : config.transfer.executionNS = (input.deployment .standby).executionNS) :
    Nonempty (CampusTCPStartupTransferObserved.Result config value.transferReport transferEnd) := by
  apply CampusTCPStartupTransferObserved.complete_at profile prep value.checked.transfer budget prepared paths raw namespaceEq
    transferEnd
  · rw [value.transfer_length]
    exact Nat.le_refl _
  · exact value.transfer_done

structure WithTransfer (value : Result report config transferEnd triggerCut bound targets) where
  prior : CampusTCPStartupTransferObserved.Result config value.transferReport transferEnd

variable {value}

theorem WithTransfer.history (joint : WithTransfer value) :
    joint.prior.transfer.current.report.steps = report.steps.take transferEnd := by
  have history := joint.prior.history
  change joint.prior.transfer.current.report.steps = (report.steps.take transferEnd).take transferEnd at history
  simpa only [List.take_take, Nat.min_self] using history

theorem WithTransfer.streams (joint : WithTransfer value) :
    joint.prior.transfer.readWrite.read.actual.result.read = config.transfer.lower ++ config.transfer.upper ∧
      joint.prior.transfer.value.completed.reader.result.read = config.transfer.reverseLower ++ config.transfer.reverseUpper :=
  joint.prior.streams

theorem WithTransfer.controls (joint : WithTransfer value) : joint.prior.transfer.monitor.controls.map (·.1) =
    [.pause, .capture, .install, .clientRoute, .serverRoute, .fence, .resume] := joint.prior.controls

structure CertifiedTransfer (report : Report input events) (config : CampusTCPStartupTransferMonitor.Config)
    (transferEnd triggerCut bound : Nat) where
  core : Certified report config transferEnd triggerCut bound
  transfer : Nonempty (WithTransfer core.result)

def certifyTransfer (report : Report input events) (config : CampusTCPStartupTransferMonitor.Config)
    (transferEnd triggerCut bound : Nat) (raw : Raw) :
    Except String (CertifiedTransfer report config transferEnd triggerCut bound) := do
  let core ← certify report config transferEnd triggerCut bound raw
  let checked ← CampusTCPStartupTransferCheck.checkReport core.result.transferReport config transferEnd
  have transfer : Nonempty (WithTransfer core.result) := by
    obtain ⟨prior⟩ := checked.result
    exact ⟨⟨prior⟩⟩
  return ⟨core, transfer⟩

end Netlib.Check.CampusTCPRevocation
