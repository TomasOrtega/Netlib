import Netlib.Check.CampusTCPStartupCriticalClockFrame

/-!
# Serving the current clock demand reduces the critical rank

The demand supplies the actual selected actor and full clock target.
-/

namespace Netlib.Check.CampusTCPStartupCriticalClockStep

open Protocol.TCP CampusTCPModel CampusTCPStartupJobs

namespace P
export CampusTCPStartupSelection (phaseRank retain path timer timerDemand demand)
end P
namespace M
export CampusTCPStartupMonitor (Monitor advanceProtection)
end M
namespace R
export CampusTCPStartupCriticalRank (rank)
end R

variable {input : Input} {actual : Step input}
variable {current : C.State input.active input.passive}
variable {config : CampusTCPStartupTransferMonitor.Config} {monitor : M.Monitor}

theorem served_strict (connected : actual.before.connection = .recovering current)
    (positive : 0 < config.transfer.quantum)
    (event : actual.event = .startupClock actor millis)
    (selected : P.demand config actual.before monitor.protection = some actual.event) :
    R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) <
      R.rank config.transfer.quantum actual.before monitor.protection := by
  cases retained : P.retain actual.before monitor.protection with
  | none =>
    simp only [P.demand, retained] at selected
    split at selected <;> simp only [event, Option.some.injEq, reduceCtorEq] at selected
  | some protection =>
    cases protection with
    | path index =>
      cases found : P.path actual.before index with
      | none => simp only [P.demand, retained, found, Option.map_none, reduceCtorEq] at selected
      | some job =>
        simp only [P.demand, retained, found, Option.map_some, Option.some.injEq] at selected
        cases job <;> simp only [CampusTCPStartupSelection.Job.event, event, reduceCtorEq] at selected
    | timer target =>
      simp only [P.demand, retained, P.timerDemand, P.timer, connected] at selected
      cases status : (current.timer target.recoverySide).status with
      | idle => simp only [status, event, reduceCtorEq] at selected
      | acknowledged kind source => simp only [status, event, reduceCtorEq] at selected
      | pending flight =>
        simp only [status] at selected
        by_cases early : (current.timer target.recoverySide).now < flight.deadline
        · simp only [early, ite_true, event, Option.some.injEq, Event.startupClock.injEq] at selected
          obtain ⟨actorEq, timeEq⟩ := selected
          subst actor
          have serving : actual.event = .startupClock target
              (min ((current.timer target.recoverySide).now + config.transfer.quantum) flight.deadline) :=
            event.trans (congrArg (Event.startupClock target) timeEq.symm)
          exact CampusTCPStartupCriticalClock.served_strict connected retained status early positive serving
        · simp only [early, ite_false, event, Option.some.injEq, reduceCtorEq] at selected

end Netlib.Check.CampusTCPStartupCriticalClockStep
