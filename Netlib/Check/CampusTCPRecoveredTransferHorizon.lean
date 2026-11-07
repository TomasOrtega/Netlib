import Netlib.Check.CampusTCPRecoveredTransferComplete
import Netlib.Check.CampusTCPRecoveredTransferBound
import Netlib.Check.CampusTCPStartupActionsProfile

/-!
# The transfer horizon after an actual startup boundary

The raw setup horizon bounds both inherited data timers.
One whole Actions check and service check supply the transfer result.
-/

namespace Netlib.Check.CampusTCPRecoveredTransferHorizon

open CampusTCPModel CampusTCPRecoveredSetup

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
export CampusTCPStartupTransferExecution (initial actions check)
end W
namespace N
export CampusTCPTwoTransferNative (Checks Routing)
end N
namespace R
export CampusTCPTwoTransferExchangeResult (Result)
end R

variable {input : Input} {events wholeEvents : List Event} {report : Report input events}
variable {ready : DrainReady report} {config : M.Config} {whole : Report input wholeEvents}
variable (task : P.Task ready config.transfer.lower config.transfer.upper config.transfer.reverseLower config.transfer.reverseUpper)

theorem complete_by (placed : CampusTCPRecoveredTransferComplete.At task whole)
    (checks : N.Checks (E.cut task.prepared) task.built.initial.gatewayState.session.entry)
    (routing : N.Routing (E.cut task.prepared) .primary)
    (ingress : checks.ingress = config.transfer.ingress)
    (namespaceEq : config.transfer.executionNS = (input.deployment .standby).executionNS)
    (budget : config.transfer.lossAllowance ≤ 2) (positive : 0 < config.transfer.quantum)
    (actions : W.actions config input.initial (W.initial config) whole.steps = true)
    (service : W.check config input.initial (W.initial config) whole.steps bound = true)
    (clocks : CampusTCPStartupClockBounds.Actions config.transfer.quantum (E.cut task.prepared).report.steps)
    (within : (E.cut task.prepared).report.steps.length ≤ setupSlots)
    (enough : setupSlots + CampusTCPRecoveredTransferBound.slots config.transfer.quantum
      config.transfer.lossAllowance setupSlots bound ≤ whole.steps.length) :
    Nonempty (R.Result task.built.initial checks routing config.transfer.quantum
      (config.transfer.lossAllowance - report.final.custody.dropped)
      config.transfer.reverseLower config.transfer.reverseUpper bound
      (whole.steps.drop (E.cut task.prepared).report.steps.length)) := by
  apply CampusTCPRecoveredTransferComplete.complete_by task placed checks routing ingress namespaceEq
    budget positive actions service
  have bounded := CampusTCPRecoveredTransferBound.Task.whole_slots_le task clocks within
    (allowance := config.transfer.lossAllowance) (bound := bound)
  omega

theorem complete_from_whole (placed : CampusTCPRecoveredTransferComplete.At task whole)
    (checks : N.Checks (E.cut task.prepared) task.built.initial.gatewayState.session.entry)
    (routing : N.Routing (E.cut task.prepared) .primary)
    (ingress : checks.ingress = config.transfer.ingress)
    (namespaceEq : config.transfer.executionNS = (input.deployment .standby).executionNS)
    (prep : CampusTCPStartupProfile.Prep config.startup)
    (budget : config.transfer.lossAllowance ≤ 2) (positive : 0 < config.transfer.quantum)
    (actions : W.actions config input.initial (W.initial config) whole.steps = true)
    (service : W.check config input.initial (W.initial config) whole.steps bound = true)
    (within : (E.cut task.prepared).report.steps.length ≤ setupSlots)
    (enough : setupSlots + CampusTCPRecoveredTransferBound.slots config.transfer.quantum
      config.transfer.lossAllowance setupSlots bound ≤ whole.steps.length) :
    Nonempty (R.Result task.built.initial checks routing config.transfer.quantum
      (config.transfer.lossAllowance - report.final.custody.dropped)
      config.transfer.reverseLower config.transfer.reverseUpper bound
      (whole.steps.drop (E.cut task.prepared).report.steps.length)) := by
  have clocks := CampusTCPStartupActionsProfile.Report.clock_actions whole prep actions
  exact complete_by task placed checks routing ingress namespaceEq budget positive actions service
    (fun actual member => clocks actual (placed.retained.subset member)) within enough

end Netlib.Check.CampusTCPRecoveredTransferHorizon
