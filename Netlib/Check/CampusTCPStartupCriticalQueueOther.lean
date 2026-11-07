import Netlib.Check.CampusTCPStartupCriticalQueueRank

/-!
# Other startup queue work retains the protected path

Assignment and service do not replace a different output's literal job.
-/

namespace Netlib.Check.CampusTCPStartupCriticalQueueOther

open CampusTCPModel CampusTCPStartupJobs

namespace U
export CampusTCPStartupJobUnique (Linear packetIndex ticketIndex)
end U
namespace P
export CampusTCPStartupSelection (path phaseRank retain demand)
end P
namespace R
export CampusTCPStartupCriticalRank (rank pathCost)
end R
namespace M
export CampusTCPStartupMonitor (Monitor advanceProtection)
end M

variable {input : Input} {job : Job input} {actual : Step input}
variable {config : CampusTCPStartupTransferMonitor.Config}

structure PathFrame (job : Job input) (actual : Step input) where
  beforePath : P.path actual.before job.outputIndex = some job
  afterPath : P.path actual.result.state job.outputIndex = some job
  phase : P.phaseRank actual.result.state = P.phaseRank actual.before

private theorem packet_index (item : PacketItem input) (selected : packetJob item = some job) :
    job.outputIndex = U.packetIndex item := by
  unfold packetJob at selected
  split at selected
  · split at selected <;> cases selected
    all_goals simp_all only [Job.outputIndex, U.packetIndex, CampusTCPStartupJobUnique.transitIndex]
  · split at selected <;> cases selected
    all_goals simp_all only [Job.outputIndex, U.packetIndex, CampusTCPStartupJobUnique.transitIndex]

private theorem ticket_index (item : TicketItem input) (selected : ticketJob item = some job) :
    job.outputIndex = U.ticketIndex item := by
  unfold ticketJob at selected
  split at selected <;> cases selected <;> rfl

private theorem after_linear (actual : Step input) (report : Report input events)
    (before : actual.before = report.final)
    (nocopy : ∀ actual ∈ report.steps, ∀ id, actual.event ≠ .copyPacket id)
    (notCopy : ∀ id, actual.event ≠ .copyPacket id) : U.Linear actual.result.state := by
  have prior : U.Linear actual.before := by rw [before]; exact CampusTCPStartupJobUnique.Report.linear report nocopy
  have history : Theory.PacketCustody.History actual.before.custody := by
    rw [before]
    exact CampusTCPCustodyFacts.Report.history report
  exact prior.step history notCopy

theorem assignment_frame (actual : Step input) (report : Report input events)
    (before : actual.before = report.final)
    (nocopy : ∀ actual ∈ report.steps, ∀ id, actual.event ≠ .copyPacket id)
    (selected : P.path actual.before job.outputIndex = some job)
    (different : index ≠ job.outputIndex) (event : actual.event = .assign index ingress) :
    PathFrame job actual := by
  have oldMember := CampusTCPStartupSelection.selected_member selected
  have history : Theory.PacketCustody.History actual.before.custody := by
    rw [before]
    exact CampusTCPCustodyFacts.Report.history report
  obtain ⟨packetID, resolved, chosen, resolvedAt, predicate, _⟩ :=
    CampusTCPCustodyFacts.Step.assign actual index ingress event history
  obtain ⟨produced, payload⟩ := CampusTCPCustodyFacts.ingress_stage _ _ predicate
  have source : actual.before.outputs[index]? = some produced := by
    have sourced := CampusTCPCustodyFacts.Report.sources report resolved.item
      (List.mem_append_right _ (by rw [← before]; exact resolved.member))
    simpa only [payload, CampusTCPCustodyFacts.Sourced, before] using sourced
  obtain ⟨custody, prepared, frame⟩ := CampusTCPRoundAssignment.Step.assign_frame actual index ingress event produced source
  have custodyEq : custody = resolved.state := by
    simpa only [prepareCustody, chosen, resolvedAt, Except.mapError, bind, Except.bind,
      pure, Except.pure, Except.ok.injEq] using prepared.symm
  have removed : U.packetIndex resolved.item = index := by
    simp only [U.packetIndex, payload, CampusTCPStartupJobUnique.transitIndex]
  have member : job ∈ inventory actual.result.state := by
    rcases inventory_member.mp oldMember with ⟨item, pending, found⟩ | ⟨item, pending, found⟩
    · have sameIndex := packet_index item found
      have rest : item ∈ resolved.state.pending := by
        have current := List.mem_cons.mp (resolved.completed.pendingPerm.mem_iff.mp pending)
        rcases current with same | remaining
        · have impossible := congrArg U.packetIndex same
          change U.packetIndex item = U.packetIndex resolved.item at impossible
          rw [removed, ← sameIndex] at impossible
          exact False.elim (different impossible.symm)
        · exact remaining
      apply inventory_member.mpr
      left
      refine ⟨item, ?_, found⟩
      simpa only [frame, custodyEq] using rest
    · apply inventory_member.mpr
      right
      refine ⟨item, ?_, found⟩
      rw [frame]
      exact List.mem_append_left _ pending
  have linear := after_linear actual report before nocopy (fun id impossible => by rw [event] at impossible; cases impossible)
  exact ⟨selected, linear.path_eq job member, by simp only [P.phaseRank, frame]⟩

private theorem service_output_none (actual : Step input) (event : actual.event = .serve ticketID observed) :
    actual.result.output = none := by
  obtain ⟨effect, custody, computed, final⟩ := actual.processed
  rw [event] at computed
  simp only [processCore] at computed
  repeat' first
    | (solve |
      rw [final]
      exact (congrArg (fun value : Effect input => value.output) (Except.ok.inj computed)).symm)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

theorem service_frame (actual : Step input) (report : Report input events)
    (before : actual.before = report.final)
    (nocopy : ∀ actual ∈ report.steps, ∀ id, actual.event ≠ .copyPacket id)
    (selected : P.path actual.before job.outputIndex = some job)
    (event : actual.event = .serve ticketID observed)
    (served : Served input) (recorded : actual.result.service = some served)
    (different : served.ticket.value.outputIndex ≠ job.outputIndex) : PathFrame job actual := by
  have oldMember := CampusTCPStartupSelection.selected_member selected
  obtain ⟨completed, _, ticket, _, work, _, connection, _, _⟩ :=
    CampusTCPRoundService.Step.serve_frame actual ticketID observed event served recorded
  have removed : U.ticketIndex completed.item = served.ticket.value.outputIndex := by rw [← ticket]; rfl
  have noOutput := service_output_none actual event
  have packets : ∀ item ∈ actual.before.custody.pending, item ∈ actual.result.state.custody.pending := by
    obtain ⟨effect, custody, computed, prepared, final⟩ := actual.transaction
    have noOutput : effect.output = none := by simpa only [final] using noOutput
    have service : effect.service = some served := by simpa only [final] using recorded
    have custodyEq : custody = actual.before.custody := by
      simpa only [event, prepareCustody, pure, Except.pure, Except.ok.injEq] using prepared.symm
    intro item pending
    rw [final, custodyEq]
    simp only [finishCustody, noOutput, service]
    split
    · exact pending
    · exact List.mem_append_left _ pending
  have member : job ∈ inventory actual.result.state := by
    rcases inventory_member.mp oldMember with ⟨item, pending, found⟩ | ⟨item, pending, found⟩
    · exact inventory_member.mpr (Or.inl ⟨item, packets item pending, found⟩)
    · have sameIndex := ticket_index item found
      have rest : item ∈ completed.state.pending := by
        have current := List.mem_cons.mp (completed.pendingPerm.mem_iff.mp pending)
        rcases current with same | remaining
        · have impossible := congrArg U.ticketIndex same
          rw [removed, ← sameIndex] at impossible
          exact False.elim (different impossible.symm)
        · exact remaining
      exact inventory_member.mpr (Or.inr ⟨item, by rw [work]; exact rest, found⟩)
  have linear := after_linear actual report before nocopy (fun id impossible => by rw [event] at impossible; cases impossible)
  exact ⟨selected, linear.path_eq job member, by simp only [P.phaseRank, connection]⟩

private theorem expired_path (state : State input) (index : Nat) (event : Event) :
    CampusTCPStartupMonitor.expired quantum state (some (.path index)) event = false := by
  cases event <;> rfl

theorem PathFrame.protection (frame : PathFrame job actual) (linear : U.Linear actual.before) (monitor : M.Monitor)
    (retained : P.retain actual.before monitor.protection = some (.path job.outputIndex)) :
    M.advanceProtection config monitor actual = some (.path job.outputIndex) := by
  have useful := CampusTCPStartupCriticalQueueRank.retained_useful linear retained frame.beforePath
  have afterUseful : CampusTCPStartupSelection.useful (P.phaseRank actual.result.state) job = true := by
    simpa only [frame.phase] using useful
  simp only [M.advanceProtection, frame.phase, Nat.lt_irrefl, ↓reduceIte, retained, expired_path, Bool.false_eq_true]
  exact CampusTCPStartupSelection.retain_live_path frame.afterPath afterUseful

theorem PathFrame.rank (frame : PathFrame job actual) (linear : U.Linear actual.before) (monitor : M.Monitor)
    (retained : P.retain actual.before monitor.protection = some (.path job.outputIndex)) :
    R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) =
      R.rank config.transfer.quantum actual.before monitor.protection := by
  by_cases complete : P.phaseRank actual.before = 4
  · simp only [R.rank, frame.phase, complete, ite_true]
  · have useful := CampusTCPStartupCriticalQueueRank.retained_useful linear retained frame.beforePath
    have afterUseful : CampusTCPStartupSelection.useful (P.phaseRank actual.result.state) job = true := by
      simpa only [frame.phase] using useful
    have protection := frame.protection linear monitor retained (config := config)
    have afterRetained := CampusTCPStartupSelection.retain_live_path frame.afterPath afterUseful
    simp only [R.rank, frame.phase, complete, ite_false, protection, afterRetained, retained,
      frame.beforePath, frame.afterPath, Option.map_some, Option.getD_some]

theorem PathFrame.pending (frame : PathFrame job actual) (linear : U.Linear actual.before) (monitor : M.Monitor)
    (retained : P.retain actual.before monitor.protection = some (.path job.outputIndex)) :
    P.demand config actual.result.state (M.advanceProtection config monitor actual) =
      P.demand config actual.before monitor.protection := by
  have useful := CampusTCPStartupCriticalQueueRank.retained_useful linear retained frame.beforePath
  have afterUseful : CampusTCPStartupSelection.useful (P.phaseRank actual.result.state) job = true := by
    simpa only [frame.phase] using useful
  have protection := frame.protection linear monitor retained (config := config)
  have afterRetained := CampusTCPStartupSelection.retain_live_path frame.afterPath afterUseful
  simp only [P.demand, protection, afterRetained, retained, frame.beforePath, frame.afterPath]

end Netlib.Check.CampusTCPStartupCriticalQueueOther
