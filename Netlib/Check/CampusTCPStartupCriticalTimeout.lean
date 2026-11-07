import Netlib.Check.CampusTCPRecoveryStartupTimeoutEnabled
import Netlib.Check.CampusTCPStartupCriticalRetryChoice
import Netlib.Check.CampusTCPStartupActionsProfile
import Netlib.Check.CampusTCPStartupMonitor

/-!
# A serving startup expiry reduces the protected rank

The due timer has one remaining service.
Its real retry supplies the next useful path.
-/

namespace Netlib.Check.CampusTCPStartupCriticalTimeout

open Protocol.TCP CampusTCPModel

namespace P
export CampusTCPStartupSelection (phaseRank criticalTimer retain choose timer timerDemand)
end P
namespace M
export CampusTCPStartupMonitor (Monitor advanceProtection expired)
end M
namespace R
export CampusTCPStartupCriticalRank (rank retain_timer)
end R
namespace U
export CampusTCPStartupJobUnique (Linear)
end U
namespace T
export CampusTCPRecoveryStartupTimeoutEnabled (Timeout)
end T

variable {input : Input} {events : List Event} {report : Report input events}
variable {config : CampusTCPStartupTransferMonitor.Config} {monitor : M.Monitor}
variable {current : C.State input.active input.passive} {actor : Actor}
variable {generation : Nat} {flight : HandshakeTimer.Flight} {actual : Step input}

theorem served_strict (report : Report input events)
    (connected : report.final.connection = .recovering current)
    (nocopy : ∀ selected ∈ report.steps, ∀ id, selected.event ≠ .copyPacket id)
    (value : T.Timeout report current actor generation flight actual)
    (held : P.retain actual.before monitor.protection = some (.timer actor))
    (positive : 0 < config.transfer.quantum) :
    R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) <
      R.rank config.transfer.quantum actual.before monitor.protection := by
  have phases : P.phaseRank actual.result.state = P.phaseRank actual.before := by
    simp only [P.phaseRank, value.before, connected, value.connection, value.phase]
  have critical := R.retain_timer held
  have incomplete : P.phaseRank actual.before ≠ 4 := by
    intro complete
    simp only [P.criticalTimer, complete, reduceCtorEq] at critical
  have demanded : P.timerDemand config.transfer.quantum actual.before actor =
      some (.startupTimeout actor generation true) := by
    simp only [P.timerDemand, P.timer, value.before, connected, value.pending,
      Nat.not_lt.mpr value.due, ↓reduceIte, value.generationEq]
  have choice : M.advanceProtection config monitor actual = P.choose actual.result.state := by
    simp only [M.advanceProtection, phases, Nat.lt_irrefl, ↓reduceIte, held,
      M.expired, value.event, demanded, true_and, decide_true]
  have distance := CampusTCPStartupTimerWait.due_distance positive value.pending value.due
  have beforeRank : R.rank config.transfer.quantum actual.before monitor.protection =
      1 + if P.phaseRank actual.before = 1 then 9 else 6 := by
    simp only [R.rank, incomplete, ↓reduceIte, held]
    simp only [P.timer, value.before, connected, distance]
  have prior : U.Linear actual.before := by
    rw [value.before]
    exact CampusTCPStartupJobUnique.Report.linear report nocopy
  have history : Theory.PacketCustody.History actual.before.custody := by
    rw [value.before]
    exact CampusTCPCustodyFacts.Report.history report
  have after : U.Linear actual.result.state := prior.step history (by
    intro id same
    rw [value.event] at same
    cases same)
  rw [choice, beforeRank]
  cases phase : current.phase with
  | idle | complete complete client server =>
    simp only [P.criticalTimer, P.phaseRank, value.before, connected, phase, reduceCtorEq] at critical
  | opened opened =>
    have actorEq : actor = .client := by
      simpa only [P.criticalTimer, P.phaseRank, value.before, connected, phase, Option.some.injEq] using critical.symm
    subst actor
    have beforePhase : P.phaseRank actual.before = 1 := by
      simp only [P.phaseRank, value.before, connected, phase]
    have afterPhase := phases.trans beforePhase
    have bound := CampusTCPStartupCriticalRetryChoice.rank_choose_opened (quantum := config.transfer.quantum) after afterPhase
      value.jobMember value.job_actor value.job_kind
    rw [beforePhase, ite_eq_left rfl]
    omega
  | answered answered =>
    have actorEq : actor = .server := by
      simpa only [P.criticalTimer, P.phaseRank, value.before, connected, phase, Option.some.injEq] using critical.symm
    subst actor
    have beforePhase : P.phaseRank actual.before = 2 := by
      simp only [P.phaseRank, value.before, connected, phase]
    have afterPhase := phases.trans beforePhase
    have bound := CampusTCPStartupCriticalChoice.rank_choose_answered (quantum := config.transfer.quantum) after afterPhase
      value.jobMember value.job_actor value.job_kind
    rw [beforePhase, ite_eq_right (by decide : (2 : Nat) ≠ 1)]
    omega
  | acknowledged acknowledged client =>
    have actorEq : actor = .server := by
      simpa only [P.criticalTimer, P.phaseRank, value.before, connected, phase, Option.some.injEq] using critical.symm
    subst actor
    have beforePhase : P.phaseRank actual.before = 3 := by
      simp only [P.phaseRank, value.before, connected, phase]
    have afterPhase := phases.trans beforePhase
    have bound := CampusTCPStartupCriticalRetryChoice.rank_choose_acknowledged (quantum := config.transfer.quantum) after afterPhase
      value.jobMember value.job_actor value.job_kind
    rw [beforePhase, ite_eq_right (by decide : (3 : Nat) ≠ 1)]
    omega

theorem served_strict_of_actions (report : Report input events)
    (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : CampusTCPStartupTransferExecution.actions config input.initial
      (CampusTCPStartupTransferExecution.initial config) report.steps = true)
    (connected : report.final.connection = .recovering current)
    (value : T.Timeout report current actor generation flight actual)
    (held : P.retain actual.before monitor.protection = some (.timer actor))
    (positive : 0 < config.transfer.quantum) :
    R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) <
      R.rank config.transfer.quantum actual.before monitor.protection :=
  served_strict report connected (CampusTCPStartupActionsProfile.Report.no_copy report prep actions) value held positive

end Netlib.Check.CampusTCPStartupCriticalTimeout
