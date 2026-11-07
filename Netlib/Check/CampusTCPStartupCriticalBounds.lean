import Netlib.Check.CampusTCPStartupCriticalRank
import Netlib.Check.CampusTCPStartupActionsProfile

/-!
# Critical startup rank from one whole Actions check

The actual report prefix bounds both endpoint clocks and the selected timer wait.
No future clock or timer bound is supplied.
-/

namespace Netlib.Check.CampusTCPStartupCriticalBounds

open CampusTCPModel

namespace E
export CampusTCPStartupTransferExecution (initial actions)
end E
namespace R
export CampusTCPStartupCriticalRank (rank rank_le)
end R
namespace P
export CampusTCPStartupSelection (Protection)
end P
namespace W
export CampusTCPRecoveryRoundMonitor (waitSlots)
end W

variable {input : Input} {events : List Event} {report : Report input events}
variable {config : CampusTCPStartupTransferMonitor.Config}
variable {current : TCPHandshakeRecovery.State input.active input.passive}

theorem Report.rank_at (report : Report input events)
    (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) report.steps = true)
    (within : slot ≤ report.steps.length)
    (connected : (CampusTCPSchedule.stateAt input.initial report.steps slot).connection = .recovering current)
    (held : Option P.Protection) :
    R.rank config.transfer.quantum (CampusTCPSchedule.stateAt input.initial report.steps slot) held ≤
      W.waitSlots config.transfer.quantum (1000 + config.transfer.quantum * slot) + 10 := by
  let prior := CampusTCPSchedule.Report.cut report slot within
  have clocks := CampusTCPStartupActionsProfile.Report.clock_actions report prep actions
  exact R.rank_le connected
    (CampusTCPRecoveryStartupOrigins.Report.recoveryReachable prior connected)
    (fun actor => CampusTCPStartupClockBounds.Report.recovering_clock_at report clocks within connected actor)

end Netlib.Check.CampusTCPStartupCriticalBounds
