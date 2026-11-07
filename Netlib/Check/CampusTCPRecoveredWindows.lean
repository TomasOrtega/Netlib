import Netlib.Check.CampusTCPRecoveredSetup
import Netlib.Check.TCPHandshakeRecoveryPhaseWindowsFacts

/-!
# Peer windows in the actual startup archive

The capacities follow the real recovery receives. Window markers remain the
values selected by those receives.
-/

namespace Netlib.Check.CampusTCPRecoveredWindows

open Protocol.TCP CampusTCPModel CampusTCPRecoveredSetup

theorem Prefix.windows (prior : Prefix input events archive) :
    archive.client.current.sendWindow = input.passive.capacity ∧
      archive.server.current.sendWindow = input.active.capacity :=
  (CampusTCPRecoveryStartupOrigins.Report.archiveReachable prior.report prior.archived).complete_windows archive.phase

end Netlib.Check.CampusTCPRecoveredWindows
