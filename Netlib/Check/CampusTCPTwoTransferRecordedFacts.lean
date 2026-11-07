import Netlib.Check.CampusTCPTwoTransferRecorded
import Netlib.Check.CampusTCPTwoTransferAccounting

/-!
# Facts from the same current recorded transfer prefix

Current health derives passed steps, compliance and whole counters.
The same prefix also bounds each endpoint clock.
-/

namespace Netlib.Check.CampusTCPTwoTransferRecorded

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {config : CampusTCPTwoTransferMonitor.Config}
variable {monitor : CampusTCPTwoTransferMonitor.Monitor}

private theorem passed_of_fold (config : CampusTCPTwoTransferMonitor.Config) (monitor : CampusTCPTwoTransferMonitor.Monitor)
    (steps : List (Step input)) (healthy : (steps.foldl (CampusTCPTwoTransferMonitor.observe config) monitor).mode ≠ .invalid) :
    ∀ actual ∈ steps, actual.result.passed = true := by
  induction steps generalizing monitor with
  | nil => intro _ member; cases member
  | cons actual rest ih =>
    have nextHealthy := CampusTCPTwoTransferAccounting.fold_healthy config (CampusTCPTwoTransferMonitor.observe config monitor actual) rest healthy
    have passed := (CampusTCPTwoTransferAccounting.observe_checked config monitor actual nextHealthy).2.2.1
    intro chosen member
    rcases List.mem_cons.mp member with same | later
    · exact same ▸ passed
    · exact ih (CampusTCPTwoTransferMonitor.observe config monitor actual) healthy chosen later

theorem Recorded.passed (recorded : Recorded cut config current monitor) (healthy : monitor.mode ≠ .invalid) :
    ∀ actual ∈ recorded.suffix, actual.result.passed = true :=
  passed_of_fold config .initial recorded.suffix (by rw [recorded.observed]; exact healthy)

theorem Recorded.compliant (recorded : Recorded cut config current monitor) (healthy : monitor.mode ≠ .invalid)
    (prior : cut.report.compliant = true) : current.report.compliant = true :=
  CampusTCPRecoveryRoundOrigins.compliant_of_suffix cut.report current.report current.supported prior
    recorded.suffix recorded.history (recorded.passed healthy)

theorem Recorded.accounting (recorded : Recorded cut config current monitor) (healthy : monitor.mode ≠ .invalid) :
    monitor.exchange.drops = recorded.suffix.filterMap CampusTCPTwoProgressLossHistory.dropID ∧
      monitor.exchange.timeouts = (recorded.suffix.filter CampusTCPTwoExchangeLoss.isTimeoutOutput).length ∧
      monitor.exchange.slots = recorded.suffix.length := by
  have counted := CampusTCPTwoTransferAccounting.initial_accounting config recorded.suffix
    (by rw [recorded.observed]; exact healthy)
  rwa [recorded.observed] at counted

theorem Recorded.clock_bound (recorded : Recorded cut config current monitor) (healthy : monitor.mode ≠ .invalid) (actor : Actor) :
    (endpoint current.endpoints actor).now ≤
      (endpoint cut.endpoints actor).now + monitor.exchange.slots * config.exchange.forward.quantum := by
  have bound := recorded.now_le actor
  rw [← (recorded.accounting healthy).2.2] at bound
  exact bound

end Netlib.Check.CampusTCPTwoTransferRecorded
