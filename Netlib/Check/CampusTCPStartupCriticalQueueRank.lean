import Netlib.Check.CampusTCPStartupCriticalQueue
import Netlib.Check.CampusTCPStartupCriticalChoice
import Netlib.Check.CampusTCPStartupMonitor

/-!
# Rank changes for actual startup queue service

A retained path stays protected while its actual next stage costs one less.
-/

namespace Netlib.Check.CampusTCPStartupCriticalQueueRank

open CampusTCPModel CampusTCPStartupJobs

namespace P
export CampusTCPStartupSelection (phaseRank path useful criticalPath criticalTimer choose retain)
end P
namespace R
export CampusTCPStartupCriticalRank (rank pathCost)
end R
namespace M
export CampusTCPStartupMonitor (Monitor advanceProtection)
end M
namespace Q
export CampusTCPStartupCriticalQueue (StageStep)
end Q
namespace U
export CampusTCPStartupJobUnique (Linear)
end U

variable {input : Input} {state : State input} {job : Job input}
variable {actual : Step input} {config : CampusTCPStartupTransferMonitor.Config}

private theorem choose_useful (linear : U.Linear state)
    (chosen : P.choose state = some (.path index)) (selected : P.path state index = some job) :
    P.useful (P.phaseRank state) job = true := by
  cases current : P.criticalPath state with
  | none =>
    simp only [P.choose, current] at chosen
    cases timer : P.criticalTimer state with
    | none => simp only [timer, Option.map_none, reduceCtorEq] at chosen
    | some actor =>
      simp only [timer, Option.map_some] at chosen
      cases Option.some.inj chosen
  | some picked =>
    have outputIndex : picked.outputIndex = index := by simpa only [P.choose, current, Option.some.injEq,
      CampusTCPStartupSelection.Protection.path.injEq] using chosen
    obtain ⟨member, useful⟩ := CampusTCPStartupCriticalChoice.criticalPath_useful current
    have found := linear.path_eq picked member
    rw [outputIndex] at found
    have same : picked = job := Option.some.inj (found.symm.trans selected)
    subst picked
    exact useful

theorem retained_useful (linear : U.Linear state)
    (retained : P.retain state held = some (.path index)) (selected : P.path state index = some job) :
    P.useful (P.phaseRank state) job = true := by
  cases held with
  | none => exact choose_useful linear retained selected
  | some protection =>
    cases protection with
    | path priorIndex =>
      cases found : P.path state priorIndex with
      | none => exact choose_useful linear (by simpa only [P.retain, found] using retained) selected
      | some priorJob =>
        by_cases useful : P.useful (P.phaseRank state) priorJob = true
        · have sameIndex : priorIndex = index := by
            simpa only [P.retain, found, useful, ite_true, Option.some.injEq,
              CampusTCPStartupSelection.Protection.path.injEq] using retained
          rw [sameIndex] at found
          have same : priorJob = job := Option.some.inj (found.symm.trans selected)
          subst priorJob
          exact useful
        · exact choose_useful linear (by simpa only [P.retain, found, useful, Bool.false_eq_true, ↓reduceIte] using retained) selected
    | timer actor =>
      by_cases selectedActor : P.criticalTimer state = some actor
      · simp only [P.retain, selectedActor, ite_true] at retained
        cases Option.some.inj retained
      · exact choose_useful linear (by simpa only [P.retain, selectedActor, ite_false] using retained) selected

theorem rank_retained (retained : P.retain state held = some (.path index))
    (selected : P.path state index = some job) (incomplete : P.phaseRank state ≠ 4) :
    R.rank quantum state held = R.pathCost (P.phaseRank state) job := by
  simp only [R.rank, incomplete, ite_false, retained, selected, Option.map_some, Option.getD_some]

private theorem next_useful (progress : Q.StageStep job actual) (useful : P.useful (P.phaseRank actual.before) job = true) :
    P.useful (P.phaseRank actual.result.state) progress.next = true := by
  have actor : progress.next.actor = job.actor := by
    change Actor.ofRecovery progress.next.source.occurrence.actor = Actor.ofRecovery job.source.occurrence.actor
    rw [progress.source]
  have kind : progress.next.kind = job.kind := by
    change progress.next.source.occurrence.kind = job.source.occurrence.kind
    rw [progress.source]
  simpa only [P.useful, progress.phase, actor, kind] using useful

private theorem expired_path (state : State input) (index : Nat) (event : Event) :
    CampusTCPStartupMonitor.expired quantum state (some (.path index)) event = false := by
  cases event <;> rfl

theorem StageStep.protection (progress : Q.StageStep job actual) (linear : U.Linear actual.before) (monitor : M.Monitor)
    (retained : P.retain actual.before monitor.protection = some (.path job.outputIndex)) :
    M.advanceProtection config monitor actual = some (.path job.outputIndex) := by
  have useful := retained_useful linear retained progress.beforePath
  have nextUseful := next_useful progress useful
  simp only [M.advanceProtection, progress.phase, Nat.lt_irrefl, ↓reduceIte, retained, expired_path,
    Bool.false_eq_true]
  exact CampusTCPStartupSelection.retain_live_path progress.nextPath nextUseful

theorem StageStep.rank_step (progress : Q.StageStep job actual) (linear : U.Linear actual.before) (monitor : M.Monitor)
    (retained : P.retain actual.before monitor.protection = some (.path job.outputIndex))
    (incomplete : P.phaseRank actual.before ≠ 4) :
    R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) + 1 =
      R.rank config.transfer.quantum actual.before monitor.protection := by
  have useful := retained_useful linear retained progress.beforePath
  have nextUseful := next_useful progress useful
  have protection := StageStep.protection progress linear monitor retained (config := config)
  have afterRetained := CampusTCPStartupSelection.retain_live_path progress.nextPath nextUseful
  simp only [R.rank, progress.phase, incomplete, ite_false, protection, afterRetained, retained,
    progress.beforePath, progress.nextPath, Option.map_some, Option.getD_some]
  simpa only [progress.phase] using progress.cost

theorem StageStep.strict (progress : Q.StageStep job actual) (linear : U.Linear actual.before) (monitor : M.Monitor)
    (retained : P.retain actual.before monitor.protection = some (.path job.outputIndex))
    (incomplete : P.phaseRank actual.before ≠ 4) :
    R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) <
      R.rank config.transfer.quantum actual.before monitor.protection := by
  have step := StageStep.rank_step progress linear monitor retained incomplete (config := config)
  omega

theorem assignment_strict (actual : Step input) (report : Report input events)
    (before : actual.before = report.final)
    (nocopy : ∀ actual ∈ report.steps, ∀ id, actual.event ≠ .copyPacket id)
    (item : PacketItem input) (index : Nat) (source : Source input)
    (payload : item.value.payload = .ingress index source.produced) (pending : item ∈ report.final.custody.pending)
    (event : actual.event = .assign index ingress) (monitor : M.Monitor)
    (retained : P.retain actual.before monitor.protection = some (.path index))
    (incomplete : P.phaseRank actual.before ≠ 4) :
    R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) <
      R.rank config.transfer.quantum actual.before monitor.protection := by
  obtain ⟨progress⟩ := CampusTCPStartupCriticalQueue.assignment actual report before nocopy item index source payload pending event
  have linear : U.Linear actual.before := by rw [before]; exact CampusTCPStartupJobUnique.Report.linear report nocopy
  exact StageStep.strict progress linear monitor retained incomplete

theorem service_strict (actual : Step input) (report : Report input events)
    (before : actual.before = report.final)
    (nocopy : ∀ actual ∈ report.steps, ∀ id, actual.event ≠ .copyPacket id)
    (item : TicketItem input) (source : Source input) (production : item.value.produced = source.produced)
    (pending : item ∈ report.final.work.pending) (event : actual.event = .serve item.id observed)
    (served : Served input) (recorded : actual.result.service = some served)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (monitor : M.Monitor)
    (retained : P.retain actual.before monitor.protection = some (.path item.value.outputIndex))
    (incomplete : P.phaseRank actual.before ≠ 4) :
    R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) <
      R.rank config.transfer.quantum actual.before monitor.protection := by
  obtain ⟨progress⟩ := CampusTCPStartupCriticalQueue.service actual report before nocopy item source production pending event served recorded emission emitted
  have linear : U.Linear actual.before := by rw [before]; exact CampusTCPStartupJobUnique.Report.linear report nocopy
  exact StageStep.strict progress linear monitor retained incomplete

end Netlib.Check.CampusTCPStartupCriticalQueueRank
