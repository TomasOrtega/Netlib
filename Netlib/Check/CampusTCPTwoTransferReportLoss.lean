import Netlib.Check.CampusTCPTwoTransferExchangeResult
import Netlib.Check.CampusTCPReportLoss

/-!
# Transfer loss in the whole report

The two reads retain startup losses and actual packet identities.
The data task uses only the allowance left at its initial cut.
-/

namespace Netlib.Check.CampusTCPTwoTransferReportLoss

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferExchangeResult (Result)
open CampusTCPReportLoss

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance bound : Nat} {reverseLower reverseUpper : List UInt8} {steps : List (Step input)}

variable (result : Result initial checks routing quantum allowance reverseLower reverseUpper bound steps)

theorem Result.suffix_drop_ids :
    result.monitor.exchange.drops = dropIDs (steps.take result.slot) := by
  have suffix : result.reverse.point.value.recorded.suffix = steps.take result.slot :=
    List.append_cancel_left (result.reverse.point.value.recorded.history.symm.trans result.history)
  have actual := result.recorded_eq.symm.trans suffix
  rw [result.accounting.1, actual]
  rfl

theorem Result.report_drop_ids :
    result.current.report.final.custody.droppedIDs =
      cut.report.final.custody.droppedIDs ++ result.monitor.exchange.drops := by
  rw [CampusTCPReportLoss.Report.drop_ids, result.history, dropIDs_append,
    ← CampusTCPReportLoss.Report.drop_ids cut.report, ← Result.suffix_drop_ids result]

theorem Result.report_drop_count :
    result.current.report.final.custody.dropped =
      cut.report.final.custody.dropped + result.monitor.exchange.drops.length := by
  have count : drops (steps.take result.slot) = result.monitor.exchange.drops.length := by
    rw [← dropIDs_length, ← Result.suffix_drop_ids result]
  rw [CampusTCPReportLoss.Report.drop_count, result.history, drops_append,
    ← CampusTCPReportLoss.Report.drop_count cut.report, count]

theorem Result.prefix_drop_ids_disjoint :
    ∀ old ∈ cut.report.final.custody.droppedIDs, ∀ later ∈ result.monitor.exchange.drops, old ≠ later := by
  have distinct := CampusTCPReportLoss.Report.drop_ids_distinct result.current.report
  rw [result.history, dropIDs_append, ← CampusTCPReportLoss.Report.drop_ids cut.report,
    ← Result.suffix_drop_ids result] at distinct
  exact (List.nodup_append.mp distinct).2.2

theorem Result.remaining_allowance (whole : Nat)
    (bounded : result.current.report.final.custody.dropped ≤ whole) :
    result.monitor.exchange.drops.length ≤ whole - cut.report.final.custody.dropped := by
  have count := Result.report_drop_count result
  omega

theorem Result.whole_budget (whole : Nat) (prior : cut.report.final.custody.dropped ≤ whole)
    (remaining : allowance = whole - cut.report.final.custody.dropped) :
    result.current.report.final.custody.dropped ≤ whole := by
  have count := Result.report_drop_count result
  have bounded := result.shared_budget.2
  omega

theorem Result.data_timeouts_remaining (whole : Nat)
    (bounded : result.current.report.final.custody.dropped ≤ whole) :
    result.monitor.exchange.timeouts ≤ whole - cut.report.final.custody.dropped :=
  Nat.le_trans result.shared_budget.1 (Result.remaining_allowance result whole bounded)

end Netlib.Check.CampusTCPTwoTransferReportLoss
