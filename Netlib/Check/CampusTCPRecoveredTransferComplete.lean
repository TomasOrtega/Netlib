import Netlib.Check.CampusTCPRecoveredTransferTask
import Netlib.Check.CampusTCPStartupTransferConfigBuilt
import Netlib.Check.CampusTCPStartupTransferSuffix
import Netlib.Check.CampusTCPTwoTransferReportLoss

/-!
# The actual transfer suffix after recovered setup

One whole Actions check and service check supply the literal data suffix.
The data allowance retains all losses in the startup report.
-/

namespace Netlib.Check.CampusTCPRecoveredTransferComplete

open Protocol.TCP CampusTCPModel CampusTCPRecoveredSetup

namespace P
export CampusTCPRecoveredTransferTask (Task)
end P
namespace E
export CampusTCPRecoveredTwoWriteEndpoints (cut)
end E
namespace M
export CampusTCPStartupTransferMonitor (Config)
end M
namespace W
export CampusTCPStartupTransferExecution (initial monitorAt actions check)
end W
namespace N
export CampusTCPTwoTransferNative (Checks Routing)
end N
namespace R
export CampusTCPTwoTransferExchangeResult (Result complete_by)
end R
namespace B
export CampusTCPTwoTransferExchangeBound (wholeSlots)
end B

variable {input : Input} {events wholeEvents : List Event} {report : Report input events}
variable {ready : DrainReady report} {config : M.Config}
variable (task : P.Task ready config.transfer.lower config.transfer.upper config.transfer.reverseLower config.transfer.reverseUpper)

structure At (whole : Report input wholeEvents) : Prop where
  retained : (E.cut task.prepared).report.steps <+: whole.steps
  monitor : W.monitorAt config (W.initial config) whole.steps (E.cut task.prepared).report.steps.length =
    .data ⟨task.archive, (E.cut task.prepared).report.final.custody.dropped⟩ .initial

variable {whole : Report input wholeEvents} (placed : At task whole)

include placed

theorem At.state :
    CampusTCPSchedule.stateAt input.initial whole.steps (E.cut task.prepared).report.steps.length =
      (E.cut task.prepared).report.final := by
  obtain ⟨later, history⟩ := placed.retained
  have selected : whole.steps.take (E.cut task.prepared).report.steps.length = (E.cut task.prepared).report.steps := by
    rw [← history, List.take_left]
  rw [← CampusTCPTraceSlices.stateAt_take _ _ (Nat.le_refl (E.cut task.prepared).report.steps.length), selected]
  exact CampusTCPSchedule.Trace.last_state (E.cut task.prepared).report.trace

theorem complete_by
    (checks : N.Checks (E.cut task.prepared) task.built.initial.gatewayState.session.entry)
    (routing : N.Routing (E.cut task.prepared) .primary)
    (ingress : checks.ingress = config.transfer.ingress)
    (namespaceEq : config.transfer.executionNS = (input.deployment .standby).executionNS)
    (budget : config.transfer.lossAllowance ≤ 2) (positive : 0 < config.transfer.quantum)
    (actions : W.actions config input.initial (W.initial config) whole.steps = true)
    (service : W.check config input.initial (W.initial config) whole.steps bound = true)
    (enough : (E.cut task.prepared).report.steps.length + B.wholeSlots task.built.initial config.transfer.quantum
      (config.transfer.lossAllowance - report.final.custody.dropped) bound ≤ whole.steps.length) :
    Nonempty (R.Result task.built.initial checks routing config.transfer.quantum
      (config.transfer.lossAllowance - report.final.custody.dropped)
      config.transfer.reverseLower config.transfer.reverseUpper bound
      (whole.steps.drop (E.cut task.prepared).report.steps.length)) := by
  have within := placed.retained.length_le
  have sameConfig := CampusTCPStartupTransferConfigBuilt.Built.data_config task.drained config.transfer
    task.prepared task.built checks routing ingress namespaceEq
  have remaining : config.transfer.lossAllowance - task.prepared.next.report.final.custody.dropped =
      config.transfer.lossAllowance - report.final.custody.dropped :=
    congrArg (fun count => config.transfer.lossAllowance - count) (CampusTCPRecoveredTransferTask.Task.drop_count task)
  rw [remaining] at sameConfig
  change config.transfer.data ⟨task.archive, (E.cut task.prepared).report.final.custody.dropped⟩ =
    CampusTCPTwoTransferLocatedCore.config task.built.initial checks routing config.transfer.quantum
      (config.transfer.lossAllowance - report.final.custody.dropped)
      config.transfer.reverseLower config.transfer.reverseUpper at sameConfig
  have dataActions := CampusTCPStartupTransferSuffix.data_actions_suffix within placed.monitor actions
  have dataService := CampusTCPStartupTransferSuffix.data_check_suffix within placed.monitor service
  rw [sameConfig, At.state task placed] at dataActions dataService
  have trace := CampusTCPTraceSlices.Trace.drop whole.trace within
  rw [At.state task placed] at trace
  apply R.complete_by task.built.initial checks routing config.transfer.quantum
    (config.transfer.lossAllowance - report.final.custody.dropped)
    config.transfer.reverseLower config.transfer.reverseUpper task.primaryEmpty task.standbyEmpty
    (CampusTCPRecoveredTransferTask.Task.target_namespace task checks)
    task.reverseEndpoints task.reverseGateway task.reverseLowerNonempty task.reverseUpperNonempty
    (Nat.le_trans (Nat.sub_le _ _) budget) positive trace dataActions dataService
  rw [List.length_drop]
  omega

end Netlib.Check.CampusTCPRecoveredTransferComplete
