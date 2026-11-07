import Netlib.Check.CampusTCPRecoveredTransferComplete

/-!
# One custody ledger through recovered setup and transfer

The startup packet IDs remain in the resulting report.
Drain and endpoint setup add no losses or replacement packet identities.
-/

namespace Netlib.Check.CampusTCPRecoveredTransferLedger

open Protocol.TCP CampusTCPModel CampusTCPRecoveredSetup CampusTCPReportLoss

namespace P
export CampusTCPRecoveredTransferTask (Task)
end P
namespace E
export CampusTCPRecoveredTwoWriteEndpoints (cut cut_history)
end E
namespace N
export CampusTCPTwoTransferNative (Checks Routing)
end N
namespace R
export CampusTCPTwoTransferExchangeResult (Result)
end R

variable {input : Input} {events : List Event} {report : Report input events}
variable {ready : DrainReady report} {lower upper reverseLower reverseUpper : List UInt8}
variable (task : P.Task ready lower upper reverseLower reverseUpper)

theorem Task.drop_ids : (E.cut task.prepared).report.final.custody.droppedIDs = report.final.custody.droppedIDs := by
  have quiet : dropID task.drained.actual = none := by
    simp only [dropID, CampusTCPDropIDs.dropID, CampusTCPDropIDs.eventDropID, task.drained.event]
  have suffix : dropIDs (task.drained.actual :: task.prepared.joints) = [] := by
    simpa only [dropIDs, List.filterMap_cons, quiet] using
      CampusTCPRecoveredSetupLoss.Prepared.joint_drop_ids task.prepared
  rw [CampusTCPReportLoss.Report.drop_ids, E.cut_history task.drained task.prepared,
    dropIDs_append, suffix, List.append_nil, ← CampusTCPReportLoss.Report.drop_ids report]

variable {checks : N.Checks (E.cut task.prepared) task.built.initial.gatewayState.session.entry}
variable {routing : N.Routing (E.cut task.prepared) .primary} {quantum allowance bound : Nat} {steps : List (Step input)}
variable (result : R.Result task.built.initial checks routing quantum allowance reverseLower reverseUpper bound steps)

theorem Result.drop_ids :
    result.current.report.final.custody.droppedIDs = report.final.custody.droppedIDs ++ result.monitor.exchange.drops := by
  rw [CampusTCPTwoTransferReportLoss.Result.report_drop_ids result, Task.drop_ids task]

theorem Result.drop_count :
    result.current.report.final.custody.dropped = report.final.custody.dropped + result.monitor.exchange.drops.length := by
  rw [CampusTCPTwoTransferReportLoss.Result.report_drop_count result, CampusTCPRecoveredTransferTask.Task.drop_count task]

theorem Result.ids_disjoint :
    ∀ old ∈ report.final.custody.droppedIDs, ∀ later ∈ result.monitor.exchange.drops, old ≠ later := by
  rw [← Task.drop_ids task]
  exact CampusTCPTwoTransferReportLoss.Result.prefix_drop_ids_disjoint result

theorem Result.whole_budget (whole : Nat) (prior : report.final.custody.dropped ≤ whole)
    (remaining : allowance = whole - report.final.custody.dropped) :
    result.current.report.final.custody.dropped ≤ whole := by
  have actual := Result.drop_count task result
  have bounded := result.shared_budget.2
  omega

end Netlib.Check.CampusTCPRecoveredTransferLedger
