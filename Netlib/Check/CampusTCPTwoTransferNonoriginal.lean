import Netlib.Check.CampusTCPTwoTransferOriginalRankStep
import Netlib.Check.CampusTCPTwoTransferEvidenceStep

/-!
# Retained forward work after the original phase

An actual continued step cannot return to the original phase.
Transfer control and primary drain are complete in this region.
-/

namespace Netlib.Check.CampusTCPTwoTransferNonoriginal

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)
open CampusTCPTwoTransferEvidence (Evidence Advanced)

namespace W
export CampusTCPTwoTransferMonitor (Monitor Allowed observe controlDemand drainTicket)
end W
namespace R
export CampusTCPTwoTransferOriginalRank (rank zero_iff)
end R

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {actual : Step input}
variable {evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

theorem advanced_nonoriginal (advance : Advanced evidence actual)
    (nonoriginal : monitor.exchange.forward.mode ≠ .originals)
    (allowed : W.Allowed cfg current.report.final monitor actual.event) :
    (W.observe cfg monitor actual).exchange.forward.mode ≠ .originals := by
  have zero := (R.zero_iff evidence).mpr nonoriginal
  have nonincrease := CampusTCPTwoTransferOriginalRankStep.nonincrease evidence advance.move allowed
  have nextZero : R.rank advance.move.after.report.final (W.observe cfg monitor actual) = 0 := by omega
  exact (R.zero_iff advance.next).mp nextZero

theorem ordinary (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (nonoriginal : monitor.exchange.forward.mode ≠ .originals) :
    W.controlDemand monitor = none ∧ W.drainTicket current.report.final monitor = none := by
  have finished := evidence.nonoriginal_finished nonoriginal
  simp only [W.controlDemand, W.drainTicket, finished]
  exact ⟨trivial, rfl⟩

theorem local_allowed (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (nonoriginal : monitor.exchange.forward.mode ≠ .originals)
    (allowed : W.Allowed cfg current.report.final monitor actual.event) :
    CampusTCPTwoProgressMonitor.Allowed ((cfg).at current.report.final).forward
      current.report.final monitor.exchange.forward actual.event := by
  have demands := ordinary evidence nonoriginal
  have exchangeAllowed := CampusTCPTwoTransferOriginalRank.ordinary_allowed evidence.healthy demands.2 demands.1 allowed
  simpa only [CampusTCPTwoExchangeMonitor.Allowed, CampusTCPTwoExchangeMonitor.allowed,
    evidence.forward.exchange, CampusTCPTwoProgressMonitor.Allowed] using exchangeAllowed

end Netlib.Check.CampusTCPTwoTransferNonoriginal
