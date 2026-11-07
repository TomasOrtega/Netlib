import Netlib.Check.CampusTCPStartupCriticalRank
import Netlib.Check.CampusTCPStartupClockStep
import Netlib.Check.CampusTCPStartupMonitor

/-!
# A serving clock reduces the protected startup rank

The proof uses the actual stored control step and current timer deadline.
The selected wait persists while its full target reduces the distance.
-/

namespace Netlib.Check.CampusTCPStartupCriticalClock

open CampusTCPModel

namespace P
export CampusTCPStartupSelection (phaseRank criticalTimer retain)
end P
namespace M
export CampusTCPStartupMonitor (Monitor advanceProtection)
end M
namespace R
export CampusTCPStartupCriticalRank (rank retain_timer)
end R

variable {input : Input} {config : CampusTCPStartupTransferMonitor.Config}
variable {current : TCPHandshakeRecovery.State input.active input.passive}
variable {actual : Step input} {monitor : M.Monitor} {actor : Actor} {flight : Protocol.TCP.HandshakeTimer.Flight}

theorem served_strict (connected : actual.before.connection = .recovering current)
    (held : P.retain actual.before monitor.protection = some (.timer actor))
    (pending : (current.timer actor.recoverySide).status = .pending flight)
    (early : (current.timer actor.recoverySide).now < flight.deadline)
    (positive : 0 < config.transfer.quantum)
    (event : actual.event = .startupClock actor
      (min ((current.timer actor.recoverySide).now + config.transfer.quantum) flight.deadline)) :
    R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) <
      R.rank config.transfer.quantum actual.before monitor.protection := by
  obtain ⟨clock⟩ := CampusTCPStartupClockStep.Step.recorded_clock actual connected event
  have phases : P.phaseRank actual.result.state = P.phaseRank actual.before := by
    simp only [P.phaseRank, connected, clock.after, clock.phase]
  have beforeRole := R.retain_timer held
  have afterRole : P.criticalTimer actual.result.state = some actor := by
    simpa only [P.criticalTimer, phases] using beforeRole
  have incomplete : P.phaseRank actual.before ≠ 4 := by
    intro complete
    simp only [P.criticalTimer, complete, reduceCtorEq] at beforeRole
  have retained := CampusTCPStartupMonitor.advanceProtection_timer_clock (config := config) held event
    (Nat.le_of_eq phases) afterRole
  have strict := CampusTCPStartupTimerWait.target_strict positive pending early
  simp only [R.rank, incomplete, ↓reduceIte, held, retained,
    CampusTCPStartupSelection.retain_timer afterRole, CampusTCPStartupSelection.timer, connected,
    clock.after, clock.selected, phases]
  exact Nat.add_lt_add_right strict _

end Netlib.Check.CampusTCPStartupCriticalClock
