import Netlib.Check.TCPHandshakeRecoveryTimerBoundsFacts
import Netlib.Check.CampusTCPRecoveryStartupOrigins

/-!
# Startup timer bounds in the same campus report

Current and archived timers use the report's actual recovery projection.
Archive handoffs retain each endpoint's clock, interval, and RTT estimate.
-/

namespace Netlib.Check.CampusTCPStartupTimerBounds

open Protocol.TCP CampusTCPModel

variable {input : Input} {events : List Event}
variable {current : C.State input.active input.passive} {archive : RecoveryArchive input.active input.passive}

theorem Report.recovering_timers_bounded (report : Report input events)
    (connection : report.final.connection = .recovering current) : TCPHandshakeRecovery.TimersBounded current :=
  (CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connection).timers_bounded

theorem Report.archive_timers_bounded (report : Report input events)
    (present : report.final.recoveryArchive = some archive) : TCPHandshakeRecovery.TimersBounded archive.current :=
  (CampusTCPRecoveryStartupOrigins.Report.archiveReachable report present).timers_bounded

theorem RecoveryArchive.handoff (archive : RecoveryArchive active passive) (actor : Actor) :
    HandshakeTimer.handoff (archive.current.timer actor.recoverySide) = some (archive.data actor) := by
  cases actor
  · exact archive.activeHandoff
  · exact archive.passiveHandoff

theorem Report.archive_handoff_bounds (report : Report input events)
    (present : report.final.recoveryArchive = some archive) (actor : Actor) :
    (archive.data actor).now = (archive.current.timer actor.recoverySide).now ∧
      (archive.data actor).rto ≤ max 3000 (HandshakeTimer.clockEnvelope (archive.data actor).now) ∧
      ((archive.data actor).estimator = none ∨ ∃ sample, sample ≤ (archive.data actor).now ∧
        (archive.data actor).estimator = some (RTO.observe none sample)) :=
  (Report.archive_timers_bounded report present).handoff actor.recoverySide (RecoveryArchive.handoff archive actor)

end Netlib.Check.CampusTCPStartupTimerBounds
