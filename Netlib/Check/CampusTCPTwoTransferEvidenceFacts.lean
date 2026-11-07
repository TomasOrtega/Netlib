import Netlib.Check.CampusTCPTwoTransferEvidence

/-!
# Accounting and permissions from current transfer evidence

The actual stored prefix supplies health, compliance, and all counters.
Its clock bound uses the same global slot count as the transfer monitor.
-/

namespace Netlib.Check.CampusTCPTwoTransferEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

private theorem passed_of_fold (config : CampusTCPTwoTransferMonitor.Config) (monitor : W.Monitor)
    (steps : List (Step input)) (healthy : (steps.foldl (W.observe config) monitor).mode ≠ .invalid) :
    ∀ actual ∈ steps, actual.result.passed = true := by
  induction steps generalizing monitor with
  | nil => intro _ member; cases member
  | cons actual rest ih =>
    have nextHealthy := CampusTCPTwoTransferAccounting.fold_healthy config (W.observe config monitor actual) rest healthy
    have passed := (CampusTCPTwoTransferAccounting.observe_checked config monitor actual nextHealthy).2.2.1
    intro chosen member
    rcases List.mem_cons.mp member with same | later
    · exact same ▸ passed
    · exact ih (W.observe config monitor actual) healthy chosen later

variable (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)

theorem Evidence.passed : ∀ actual ∈ evidence.recorded.suffix, actual.result.passed = true :=
  passed_of_fold cfg .initial evidence.recorded.suffix (by rw [evidence.recorded.observed]; exact evidence.healthy)

include evidence in
theorem Evidence.compliant (prior : cut.report.compliant = true) : current.report.compliant = true :=
  CampusTCPRecoveryRoundOrigins.compliant_of_suffix cut.report current.report current.supported prior
    evidence.recorded.suffix evidence.recorded.history evidence.passed

theorem Evidence.accounting :
    monitor.exchange.drops = evidence.recorded.suffix.filterMap CampusTCPTwoProgressLossHistory.dropID ∧
      monitor.exchange.timeouts = (evidence.recorded.suffix.filter CampusTCPTwoExchangeLoss.isTimeoutOutput).length ∧
      monitor.exchange.slots = evidence.recorded.suffix.length := by
  have counted := CampusTCPTwoTransferAccounting.initial_accounting cfg evidence.recorded.suffix
    (by rw [evidence.recorded.observed]; exact evidence.healthy)
  rwa [evidence.recorded.observed] at counted

theorem Evidence.actual_budget :
    (evidence.recorded.suffix.filter CampusTCPTwoExchangeLoss.isTimeoutOutput).length ≤
        (evidence.recorded.suffix.filter CampusTCPTwoProgressLossHistory.isDrop).length ∧
      (evidence.recorded.suffix.filter CampusTCPTwoProgressLossHistory.isDrop).length ≤ allowance := by
  rw [evidence.loss_suffix]
  apply evidence.core.losses.actual_budget
  rw [evidence.core.losses.wholeDropIDs, ← evidence.core.losses.dropIDs]
  exact evidence.core.lossBound

include evidence in
theorem Evidence.clock_bound (selected : Actor) :
    (endpoint current.endpoints selected).now ≤
      (endpoint cut.endpoints selected).now + monitor.exchange.slots * quantum := by
  have bound := evidence.recorded.now_le selected
  rw [← evidence.accounting.2.2] at bound
  exact bound

theorem Evidence.prefix (slot : Nat) (within : slot ≤ monitor.exchange.slots) :
    ∃ next : Cut input complete,
      next.report.final = CampusTCPSchedule.stateAt cut.report.final evidence.recorded.suffix slot ∧
      next.report.steps = cut.report.steps ++ evidence.recorded.suffix.take slot ∧
      CampusTCPTwoTransferClockBound.MoveChain cut (evidence.recorded.suffix.take slot) next ∧
      ∀ actor, (endpoint next.endpoints actor).now ≤
        (endpoint cut.endpoints actor).now + slot * quantum :=
  evidence.recorded.cut_now slot (by rw [← evidence.accounting.2.2]; exact within)

end Netlib.Check.CampusTCPTwoTransferEvidence
