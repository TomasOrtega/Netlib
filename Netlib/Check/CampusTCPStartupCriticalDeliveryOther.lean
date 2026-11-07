import Netlib.Check.CampusTCPStartupCriticalQueueOther

/-!
# A different delivery retains the protected startup job

A receipt can change the handshake phase while another literal path survives.
-/

namespace Netlib.Check.CampusTCPStartupCriticalDeliveryOther

open CampusTCPModel CampusTCPStartupJobs

namespace U
export CampusTCPStartupJobUnique (Linear packetIndex)
end U
namespace P
export CampusTCPStartupSelection (path phaseRank)
end P
namespace Q
export CampusTCPStartupCriticalQueueOther (PathFrame)
end Q

variable {input : Input} {job : Job input}

private theorem startup_quiet (computed : startup input before event = .ok effect) :
    effect.state.work = before.work ∧ effect.service = none := by
  unfold startup at computed
  repeat' first
    | (solve | cases computed; exact ⟨rfl, rfl⟩)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [pure, Except.pure] at computed)

private theorem application_quiet (computed : applyApplication input before actor event = .ok effect) :
    effect.state.work = before.work ∧ effect.service = none := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; exact ⟨rfl, rfl⟩)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

private theorem recovery_quiet (computed : runRecovery input before event = .ok effect) :
    effect.state.work = before.work ∧ effect.service = none := by
  unfold runRecovery at computed
  split at computed
  · cases computed; exact ⟨rfl, rfl⟩
  · cases computed; exact ⟨rfl, rfl⟩
  · split at computed
    · cases computed
    · rename_i current connected result evaluated
      cases result with
      | mk state decision output receipt application =>
        cases output <;> simp only [pure, Except.pure, Except.ok.injEq] at computed
        all_goals subst effect; exact ⟨rfl, rfl⟩

private theorem delivery_quiet (computed : processCore input before (.deliver index bytes policy) = .ok effect) :
    effect.state.work = before.work ∧ effect.service = none := by
  simp only [processCore] at computed
  repeat' first
    | (solve |
      have quiet := startup_quiet (input := input) (before := before) (by assumption)
      cases computed
      exact quiet)
    | (solve |
      have quiet := application_quiet (input := input) (before := before) (by assumption)
      cases computed
      exact quiet)
    | (solve |
      have quiet := recovery_quiet (input := input) (before := before) (by assumption)
      cases computed
      exact quiet)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

private theorem packet_index (item : PacketItem input) (selected : packetJob item = some job) :
    job.outputIndex = U.packetIndex item := by
  unfold packetJob at selected
  split at selected
  · split at selected <;> cases selected
    all_goals simp_all only [Job.outputIndex, U.packetIndex, CampusTCPStartupJobUnique.transitIndex]
  · split at selected <;> cases selected
    all_goals simp_all only [Job.outputIndex, U.packetIndex, CampusTCPStartupJobUnique.transitIndex]

theorem delivery_other_path (actual : Step input) (report : Report input events)
    (before : actual.before = report.final)
    (nocopy : ∀ actual ∈ report.steps, ∀ id, actual.event ≠ .copyPacket id)
    (selected : P.path actual.before job.outputIndex = some job)
    (item : PacketItem input) (serviceIndex : Nat) (served : Served input)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (payload : item.value.payload = .link serviceIndex served emission emitted)
    (pending : item ∈ report.final.custody.pending)
    (different : served.ticket.value.outputIndex ≠ job.outputIndex)
    (event : actual.event = .deliver serviceIndex bytes policy) :
    P.path actual.result.state job.outputIndex = some job := by
  have linear : U.Linear actual.before := by rw [before]; exact CampusTCPStartupJobUnique.Report.linear report nocopy
  have history : Theory.PacketCustody.History actual.before.custody := by
    rw [before]
    exact CampusTCPCustodyFacts.Report.history report
  obtain ⟨packetID, resolved, chosen, computed, link, bytesEq, _⟩ :=
    CampusTCPCustodyFacts.Step.deliver actual serviceIndex bytes policy event history
  obtain ⟨other, rewritten, rewrittenAt, resolvedPayload⟩ := CampusTCPCustodyFacts.link_stage _ _ link
  have serviceAt : actual.before.services[serviceIndex]? = some served := by
    have sourced := CampusTCPCustodyFacts.Report.sources report item (List.mem_append_right _ pending)
    simpa only [payload, CampusTCPCustodyFacts.Sourced, before] using sourced
  have otherAt : actual.before.services[serviceIndex]? = some other := by
    have sourced := CampusTCPCustodyFacts.Report.sources report resolved.item
      (List.mem_append_right _ (by rw [← before]; exact resolved.member))
    simpa only [resolvedPayload, CampusTCPCustodyFacts.Sourced, before] using sourced
  have same : other = served := Option.some.inj (otherAt.symm.trans serviceAt)
  subst other
  have removed : U.packetIndex resolved.item = served.ticket.value.outputIndex := by
    simp only [U.packetIndex, resolvedPayload, CampusTCPStartupJobUnique.transitIndex]
  obtain ⟨effect, custody, core, prepared, final⟩ := actual.transaction
  rw [event] at core prepared
  obtain ⟨work, service⟩ := delivery_quiet core
  simp only [prepareCustody, chosen, computed, Except.mapError, bind, Except.bind,
    bytesEq, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at prepared
  subst custody
  have packets : ∀ packet ∈ resolved.state.pending, packet ∈ actual.result.state.custody.pending := by
    intro packet present
    rw [final]
    simp only [finishCustody, service]
    split
    · exact present
    · exact List.mem_append_left _ present
  have member : job ∈ inventory actual.result.state := by
    rcases inventory_member.mp (CampusTCPStartupSelection.selected_member selected) with
      ⟨packet, present, found⟩ | ⟨ticket, present, found⟩
    · have sameIndex := packet_index packet found
      have rest : packet ∈ resolved.state.pending := by
        rcases List.mem_cons.mp (resolved.completed.pendingPerm.mem_iff.mp present) with same | remaining
        · have impossible := congrArg U.packetIndex same
          change U.packetIndex packet = U.packetIndex resolved.item at impossible
          rw [removed, ← sameIndex] at impossible
          exact False.elim (different impossible.symm)
        · exact remaining
      exact inventory_member.mpr (Or.inl ⟨packet, packets packet rest, found⟩)
    · exact inventory_member.mpr (Or.inr ⟨ticket, by simpa only [final, work] using present, found⟩)
  have after := linear.step history (fun id impossible => by rw [event] at impossible; cases impossible)
  exact after.path_eq job member

theorem delivery_frame (actual : Step input) (report : Report input events)
    (before : actual.before = report.final)
    (nocopy : ∀ actual ∈ report.steps, ∀ id, actual.event ≠ .copyPacket id)
    (selected : P.path actual.before job.outputIndex = some job)
    (item : PacketItem input) (serviceIndex : Nat) (served : Served input)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (payload : item.value.payload = .link serviceIndex served emission emitted)
    (pending : item ∈ report.final.custody.pending)
    (different : served.ticket.value.outputIndex ≠ job.outputIndex)
    (event : actual.event = .deliver serviceIndex bytes policy)
    (phase : P.phaseRank actual.result.state = P.phaseRank actual.before) : Q.PathFrame job actual :=
  ⟨selected, delivery_other_path actual report before nocopy selected item serviceIndex served emission emitted
    payload pending different event, phase⟩

end Netlib.Check.CampusTCPStartupCriticalDeliveryOther
