import Netlib.Check.CampusTCPTwoTransferCurrentReverseAt
import Netlib.Check.CampusTCPTwoTransferCurrentReverseProjectionHistory

/-!
# The same whole service selects the actual reverse task

Current reverse evidence derives routing and the fixed local configuration.
The projection includes actual clocks after the reverse read.
-/

namespace Netlib.Check.CampusTCPTwoTransferCurrentReverseProjection

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferEvidence (Evidence ReadAdvanced)
open CampusTCPTwoTransferPostRead (After)
open CampusTCPTwoTransferCurrentReverseGeometry (Started)
open CampusTCPTwoTransferCurrentReverseAt (Current reverseConfig)
open CampusTCPTwoTransferLocatedCore (config)

namespace W
export CampusTCPTwoTransferMonitor (Monitor Demand nextDemand pendingAt serves Allowed Serviced actions check monitorAt)
end W
namespace X
export CampusTCPTwoExchangeMonitor (Demand nextDemand)
end X
namespace L
export CampusTCPTwoProgressMonitor (Demand nextDemand monitorAt pendingAt Allowed Serviced actions check)
end L
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

def tag (demand : L.Demand) : W.Demand := .exchange (.reverse demand)

theorem tag_injective (first second : L.Demand) (same : tag first = tag second) : first = second := by
  cases same
  rfl

theorem serves_tag (cfg : CampusTCPTwoTransferMonitor.Config) (demand : L.Demand) (event : Event) :
    W.serves cfg (tag demand) event = CampusTCPTwoProgressMonitor.serves demand event := rfl

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut readBefore writeBefore current : Cut input complete} {sender : Actor} {gateway location : Gateway}
variable {lower upper : List UInt8} {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {readMonitor writeMonitor monitor : W.Monitor} {readActual written : Step input}
variable {evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper readBefore readMonitor location}
variable {forward : ReadAdvanced evidence readActual} {post : After forward writeBefore writeMonitor}
variable {start : Started post written}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

theorem pending_current (value : Current start current monitor) :
    W.nextDemand cfg current.report.final monitor =
      (L.nextDemand (reverseConfig start) current.report.final monitor.exchange.reverse).map tag := by
  have noDrain := CampusTCPTwoTransferControlObserve.noDrain_of_non_capture current.report.final monitor
    (by rw [value.finished]; decide)
  have noControl : CampusTCPTwoTransferMonitor.controlDemand monitor = none := by
    rw [CampusTCPTwoTransferMonitor.controlDemand, value.finished]
  simp only [W.nextDemand, value.finished, reduceCtorEq, decide_false, Bool.false_eq_true, ite_false, noDrain, noControl]
  rcases value.phase with ⟨mode, _⟩ | ⟨mode, done⟩
  · rw [X.nextDemand, mode, ← value.config]
    cases L.nextDemand (reverseConfig start) current.report.final monitor.exchange.reverse <;> rfl
  · simp only [X.nextDemand, mode, L.nextDemand, done, Option.map_none]

end Netlib.Check.CampusTCPTwoTransferCurrentReverseProjection
