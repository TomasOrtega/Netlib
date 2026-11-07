import Netlib.Check.CampusTCPStartupCriticalTimeoutPath
import Netlib.Check.CampusTCPStartupCriticalTimeoutPeer
import Netlib.Check.CampusTCPStartupCriticalTimeout
import Netlib.Check.CampusTCPStartupCriticalDemand

/-!
# Rank laws for every actual due startup expiry

A protected path survives the fresh retry.
A protected timer either expires or retains its exact demand.
-/

namespace Netlib.Check.CampusTCPStartupCriticalTimeoutStep

open Protocol.TCP CampusTCPModel

namespace P
export CampusTCPStartupSelection (phaseRank criticalTimer retain path demand timerDemand)
end P
namespace M
export CampusTCPStartupMonitor (Monitor advanceProtection)
end M
namespace R
export CampusTCPStartupCriticalRank (rank)
end R
namespace T
export CampusTCPRecoveryStartupTimeoutEnabled (Timeout)
end T

variable {input : Input} {events : List Event} {report : Report input events}
variable {config : CampusTCPStartupTransferMonitor.Config} {monitor : M.Monitor}
variable {current : C.State input.active input.passive} {actor : Actor}
variable {generation : Nat} {flight : HandshakeTimer.Flight} {actual : Step input}

private theorem critical_exists (phases : P.phaseRank state = 1 ∨ P.phaseRank state = 2 ∨ P.phaseRank state = 3) :
    ∃ actor, P.criticalTimer state = some actor := by
  rcases phases with first | second | third
  · exact ⟨.client, by simp only [P.criticalTimer, first]⟩
  · exact ⟨.server, by simp only [P.criticalTimer, second]⟩
  · exact ⟨.server, by simp only [P.criticalTimer, third]⟩

theorem step_laws (report : Report input events)
    (connected : report.final.connection = .recovering current)
    (nocopy : ∀ selected ∈ report.steps, ∀ id, selected.event ≠ .copyPacket id)
    (value : T.Timeout report current actor generation flight actual)
    (phases : P.phaseRank actual.before = 1 ∨ P.phaseRank actual.before = 2 ∨ P.phaseRank actual.before = 3)
    (positive : 0 < config.transfer.quantum) :
    R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) ≤
        R.rank config.transfer.quantum actual.before monitor.protection ∧
      (R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) =
          R.rank config.transfer.quantum actual.before monitor.protection →
        P.demand config actual.result.state (M.advanceProtection config monitor actual) =
          P.demand config actual.before monitor.protection) := by
  have linear : CampusTCPStartupJobUnique.Linear actual.before := by
    rw [value.before]
    exact CampusTCPStartupJobUnique.Report.linear report nocopy
  rcases CampusTCPStartupCriticalDemand.effective_cases linear (critical_exists phases) (held := monitor.protection) with
    ⟨index, job, held, found⟩ | ⟨selected, held, _⟩
  · obtain ⟨_, equal, persistent⟩ :=
      CampusTCPStartupCriticalTimeoutPath.Timeout.persistent (config := config) value connected held found
    exact ⟨Nat.le_of_eq equal, fun _ => persistent⟩
  · by_cases same : selected = actor
    · subst selected
      have strict := CampusTCPStartupCriticalTimeout.served_strict report connected nocopy value held positive
      exact ⟨Nat.le_of_lt strict, fun equal => False.elim (Nat.ne_of_lt strict equal)⟩
    · have equal := CampusTCPStartupCriticalTimeoutPeer.rank_eq (config := config) value connected held same
      exact ⟨Nat.le_of_eq equal, fun _ =>
        CampusTCPStartupCriticalTimeoutPeer.persistent value connected held same⟩

theorem nonincrease (report : Report input events)
    (connected : report.final.connection = .recovering current)
    (nocopy : ∀ selected ∈ report.steps, ∀ id, selected.event ≠ .copyPacket id)
    (value : T.Timeout report current actor generation flight actual)
    (phases : P.phaseRank actual.before = 1 ∨ P.phaseRank actual.before = 2 ∨ P.phaseRank actual.before = 3)
    (positive : 0 < config.transfer.quantum) :
    R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) ≤
      R.rank config.transfer.quantum actual.before monitor.protection :=
  (step_laws report connected nocopy value phases positive).1

theorem persistent (report : Report input events)
    (connected : report.final.connection = .recovering current)
    (nocopy : ∀ selected ∈ report.steps, ∀ id, selected.event ≠ .copyPacket id)
    (value : T.Timeout report current actor generation flight actual)
    (phases : P.phaseRank actual.before = 1 ∨ P.phaseRank actual.before = 2 ∨ P.phaseRank actual.before = 3)
    (positive : 0 < config.transfer.quantum)
    (equal : R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) =
      R.rank config.transfer.quantum actual.before monitor.protection) :
    P.demand config actual.result.state (M.advanceProtection config monitor actual) =
      P.demand config actual.before monitor.protection :=
  (step_laws report connected nocopy value phases positive).2 equal

private theorem timer_demand_actor
    (demanded : P.timerDemand quantum state selected = some (.startupTimeout actor generation true)) :
    selected = actor := by
  cases current : CampusTCPStartupSelection.timer state selected with
  | none => simp only [P.timerDemand, current] at demanded; cases demanded
  | some timer =>
    cases status : timer.status with
    | idle | acknowledged flight atTime =>
      simp only [P.timerDemand, current, status] at demanded
      cases demanded
    | pending flight =>
      simp only [P.timerDemand, current, status] at demanded
      split at demanded
      · cases demanded
      · exact (Event.startupTimeout.inj (Option.some.inj demanded)).1

theorem served_strict (report : Report input events)
    (connected : report.final.connection = .recovering current)
    (nocopy : ∀ selected ∈ report.steps, ∀ id, selected.event ≠ .copyPacket id)
    (value : T.Timeout report current actor generation flight actual)
    (positive : 0 < config.transfer.quantum)
    (demanded : P.demand config actual.before monitor.protection = some actual.event) :
    R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) <
      R.rank config.transfer.quantum actual.before monitor.protection := by
  have expected := demanded.trans (congrArg some value.event)
  cases held : P.retain actual.before monitor.protection with
  | none =>
    simp only [P.demand, held] at expected
    split at expected <;> cases expected
  | some protection =>
    cases protection with
    | path index =>
      cases found : P.path actual.before index with
      | none => simp only [P.demand, held, found, Option.map_none] at expected; cases expected
      | some job =>
        have same : CampusTCPStartupSelection.Job.event config job = .startupTimeout actor generation true := by
          simpa only [P.demand, held, found, Option.map_some, Option.some.injEq] using expected
        cases job <;> cases same
    | timer selected =>
      have same : selected = actor := timer_demand_actor (by simpa only [P.demand, held] using expected)
      subst selected
      exact CampusTCPStartupCriticalTimeout.served_strict report connected nocopy value held positive

end Netlib.Check.CampusTCPStartupCriticalTimeoutStep
