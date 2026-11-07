import Netlib.Check.CampusTCPRecoveryStartupTimeoutEnabled
import Netlib.Check.CampusTCPStartupCriticalRank
import Netlib.Check.CampusTCPStartupMonitor

/-!
# A protected timer across the other endpoint's expiry

The actual timeout changes only its selected endpoint timer.
The protected peer keeps its exact pending demand.
-/

namespace Netlib.Check.CampusTCPStartupCriticalTimeoutPeer

open Protocol.TCP CampusTCPModel

namespace P
export CampusTCPStartupSelection (phaseRank criticalTimer retain timer timerDemand demand)
end P
namespace M
export CampusTCPStartupMonitor (Monitor advanceProtection expired)
end M
namespace R
export CampusTCPStartupCriticalRank (rank retain_timer)
end R
namespace T
export CampusTCPRecoveryStartupTimeoutEnabled (Timeout)
end T

variable {input : Input} {events : List Event} {report : Report input events}
variable {config : CampusTCPStartupTransferMonitor.Config} {monitor : M.Monitor}
variable {current : C.State input.active input.passive} {actor selected : Actor}
variable {generation : Nat} {flight : HandshakeTimer.Flight} {actual : Step input}

private theorem recovery_side_other (different : selected ≠ actor) :
    selected.recoverySide = actor.recoverySide.other := by
  cases actor <;> cases selected <;> first | rfl | exact False.elim (different rfl)

theorem control_timer (value : T.Timeout report current actor generation flight actual)
    (different : selected ≠ actor) :
    value.control.result.state.timer selected.recoverySide = current.timer selected.recoverySide := by
  rw [recovery_side_other different]
  exact value.peerTimer

theorem timer (value : T.Timeout report current actor generation flight actual)
    (connected : report.final.connection = .recovering current) (different : selected ≠ actor) :
    P.timer actual.result.state selected = P.timer actual.before selected := by
  simp only [P.timer, value.before, connected, value.connection]
  exact congrArg some (control_timer value different)

theorem phase (value : T.Timeout report current actor generation flight actual)
    (connected : report.final.connection = .recovering current) :
    P.phaseRank actual.result.state = P.phaseRank actual.before := by
  simp only [P.phaseRank, value.before, connected, value.connection, value.phase]

theorem protection (value : T.Timeout report current actor generation flight actual)
    (connected : report.final.connection = .recovering current)
    (held : P.retain actual.before monitor.protection = some (.timer selected)) (different : selected ≠ actor) :
    M.advanceProtection config monitor actual = some (.timer selected) := by
  have phases := phase value connected
  have afterRole : P.criticalTimer actual.result.state = some selected := by
    simpa only [P.criticalTimer, phases] using R.retain_timer held
  simp only [M.advanceProtection, phases, Nat.lt_irrefl, ↓reduceIte, held,
    M.expired, value.event, different, false_and, decide_false, Bool.false_eq_true]
  exact CampusTCPStartupSelection.retain_timer afterRole

theorem retained (value : T.Timeout report current actor generation flight actual)
    (connected : report.final.connection = .recovering current)
    (held : P.retain actual.before monitor.protection = some (.timer selected)) (different : selected ≠ actor) :
    P.retain actual.result.state (M.advanceProtection config monitor actual) = some (.timer selected) := by
  rw [protection value connected held different]
  have phases := phase value connected
  apply CampusTCPStartupSelection.retain_timer
  simpa only [P.criticalTimer, phases] using R.retain_timer held

theorem rank_eq (value : T.Timeout report current actor generation flight actual)
    (connected : report.final.connection = .recovering current)
    (held : P.retain actual.before monitor.protection = some (.timer selected)) (different : selected ≠ actor) :
    R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) =
      R.rank config.transfer.quantum actual.before monitor.protection := by
  have phases := phase value connected
  have afterHeld := retained (config := config) value connected held different
  by_cases complete : P.phaseRank actual.before = 4
  · simp only [R.rank, phases, complete, ↓reduceIte]
  simp only [R.rank, phases, complete, ↓reduceIte, afterHeld, held]
  rw [timer value connected different]

theorem nonincrease (value : T.Timeout report current actor generation flight actual)
    (connected : report.final.connection = .recovering current)
    (held : P.retain actual.before monitor.protection = some (.timer selected)) (different : selected ≠ actor) :
    R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) ≤
      R.rank config.transfer.quantum actual.before monitor.protection :=
  Nat.le_of_eq (rank_eq value connected held different)

theorem persistent (value : T.Timeout report current actor generation flight actual)
    (connected : report.final.connection = .recovering current)
    (held : P.retain actual.before monitor.protection = some (.timer selected)) (different : selected ≠ actor) :
    P.demand config actual.result.state (M.advanceProtection config monitor actual) =
      P.demand config actual.before monitor.protection := by
  have afterHeld := retained (config := config) value connected held different
  simp only [P.demand, afterHeld, held, P.timerDemand]
  rw [timer value connected different]

end Netlib.Check.CampusTCPStartupCriticalTimeoutPeer
