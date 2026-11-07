import Netlib.Check.CampusTCPRecoveryStartupLinkDelivery
import Netlib.Check.CampusTCPStartupCriticalRank
import Netlib.Check.CampusTCPStartupMonitor

/-!
# A protected timer across a same-level startup receipt

The actual receive keeps both timer states.
The retained timer keeps its exact pending demand.
-/

namespace Netlib.Check.CampusTCPStartupCriticalTimerReceive

open Protocol.TCP CampusTCPModel

namespace L
export CampusTCPRecoveryStartupLinkDelivery (Delivered)
end L
namespace P
export CampusTCPStartupSelection (phaseRank criticalTimer retain timer timerDemand demand)
end P
namespace M
export CampusTCPStartupMonitor (Monitor advanceProtection expired)
end M
namespace R
export CampusTCPStartupCriticalRank (rank retain_timer)
end R

variable {input : Input} {events : List Event} {report : Report input events}
variable {config : CampusTCPStartupTransferMonitor.Config} {monitor : M.Monitor}
variable {current : C.State input.active input.passive} {actual : Step input} {actor : Actor}
variable {source : CampusTCPStartupJobs.Source input} {index : Nat} {served : Served input}
variable {emission : W.Emission served.ticket.value.source.packet}

private theorem phase_level (connected : state.connection = .recovering current) :
    P.phaseRank state = TCPHandshakeRecovery.phaseLevel current.phase := by
  cases phase : current.phase <;> simp only [P.phaseRank, connected, phase, TCPHandshakeRecovery.phaseLevel]

theorem control_timers (value : L.Delivered report current source index served emission actual)
    (connected : report.final.connection = .recovering current)
    (sameLevel : P.phaseRank actual.result.state = P.phaseRank actual.before) :
    ∀ selected, value.delivery.control.result.state.timer selected = current.timer selected := by
  have computed := value.delivery.control.computed
  rw [value.delivery.controlEvent] at computed
  simp only [TCPHandshakeRecovery.ReceiveInput.event] at computed
  have phases : TCPHandshakeRecovery.phaseLevel value.delivery.control.result.state.phase =
      TCPHandshakeRecovery.phaseLevel value.delivery.control.before.phase := by
    have beforePhase : P.phaseRank actual.before =
        TCPHandshakeRecovery.phaseLevel value.delivery.control.before.phase := by
      rw [value.delivery.controlBefore]
      exact phase_level (by rw [value.delivery.before]; exact connected)
    have afterPhase : P.phaseRank actual.result.state =
        TCPHandshakeRecovery.phaseLevel value.delivery.control.result.state.phase := by
      exact phase_level value.delivery.connection
    exact afterPhase.symm.trans (sameLevel.trans beforePhase)
  have frames := TCPHandshakeRecovery.evaluate_receive_timer_frame computed phases
  simpa only [value.delivery.controlBefore] using frames

theorem timers (value : L.Delivered report current source index served emission actual)
    (connected : report.final.connection = .recovering current)
    (sameLevel : P.phaseRank actual.result.state = P.phaseRank actual.before) :
    ∀ selected, P.timer actual.result.state selected = P.timer actual.before selected := by
  intro selected
  simp only [P.timer, value.delivery.before, connected, value.delivery.connection]
  exact congrArg some (control_timers value connected sameLevel selected.recoverySide)

private theorem critical_timer (sameLevel : P.phaseRank actual.result.state = P.phaseRank actual.before) :
    P.criticalTimer actual.result.state = P.criticalTimer actual.before := by
  simp only [P.criticalTimer, sameLevel]

theorem protection (value : L.Delivered report current source index served emission actual)
    (sameLevel : P.phaseRank actual.result.state = P.phaseRank actual.before)
    (held : P.retain actual.before monitor.protection = some (.timer actor)) :
    M.advanceProtection config monitor actual = some (.timer actor) := by
  have afterRole : P.criticalTimer actual.result.state = some actor :=
    (critical_timer sameLevel).trans (R.retain_timer held)
  simp only [M.advanceProtection, sameLevel, Nat.lt_irrefl, ↓reduceIte, held,
    M.expired, value.delivery.event, Bool.false_eq_true]
  exact CampusTCPStartupSelection.retain_timer afterRole

theorem retained (value : L.Delivered report current source index served emission actual)
    (sameLevel : P.phaseRank actual.result.state = P.phaseRank actual.before)
    (held : P.retain actual.before monitor.protection = some (.timer actor)) :
    P.retain actual.result.state (M.advanceProtection config monitor actual) = some (.timer actor) := by
  rw [protection value sameLevel held]
  exact CampusTCPStartupSelection.retain_timer ((critical_timer sameLevel).trans (R.retain_timer held))

theorem rank_eq (value : L.Delivered report current source index served emission actual)
    (connected : report.final.connection = .recovering current)
    (sameLevel : P.phaseRank actual.result.state = P.phaseRank actual.before)
    (held : P.retain actual.before monitor.protection = some (.timer actor)) :
    R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) =
      R.rank config.transfer.quantum actual.before monitor.protection := by
  have afterHeld := retained (config := config) value sameLevel held
  by_cases complete : P.phaseRank actual.before = 4
  · simp only [R.rank, sameLevel, complete, ↓reduceIte]
  simp only [R.rank, sameLevel, complete, ↓reduceIte, afterHeld, held]
  rw [timers value connected sameLevel actor]

theorem nonincrease (value : L.Delivered report current source index served emission actual)
    (connected : report.final.connection = .recovering current)
    (sameLevel : P.phaseRank actual.result.state = P.phaseRank actual.before)
    (held : P.retain actual.before monitor.protection = some (.timer actor)) :
    R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) ≤
      R.rank config.transfer.quantum actual.before monitor.protection :=
  Nat.le_of_eq (rank_eq value connected sameLevel held)

theorem persistent (value : L.Delivered report current source index served emission actual)
    (connected : report.final.connection = .recovering current)
    (sameLevel : P.phaseRank actual.result.state = P.phaseRank actual.before)
    (held : P.retain actual.before monitor.protection = some (.timer actor)) :
    P.demand config actual.result.state (M.advanceProtection config monitor actual) =
      P.demand config actual.before monitor.protection := by
  have afterHeld := retained (config := config) value sameLevel held
  simp only [P.demand, afterHeld, held, P.timerDemand]
  rw [timers value connected sameLevel actor]

end Netlib.Check.CampusTCPStartupCriticalTimerReceive
