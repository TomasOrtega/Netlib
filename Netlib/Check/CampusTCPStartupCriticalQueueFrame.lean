import Netlib.Check.CampusTCPStartupCriticalQueueRank

/-!
# Consumed startup paths cannot reappear

A delivery resolves its old output index before minting a fresh response.
-/

namespace Netlib.Check.CampusTCPStartupCriticalQueueFrame

open CampusTCPModel CampusTCPStartupJobs

namespace U
export CampusTCPStartupJobUnique (Linear packetIndex ticketIndex outputIndices count)
end U
namespace P
export CampusTCPStartupSelection (path)
end P

variable {input : Input}

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

theorem path_none_of_absent (absent : index ∉ U.outputIndices state) : P.path state index = none := by
  cases found : P.path state index with
  | none => rfl
  | some job =>
    have member := CampusTCPStartupSelection.selected_member found
    have same := CampusTCPStartupSelection.selected_index found
    have positive : 0 < ((inventory state).map Job.outputIndex).count index :=
      List.count_pos_iff.mpr (List.mem_map.mpr ⟨job, member, same⟩)
    have bound := CampusTCPStartupJobUnique.inventory_count_le state index
    rw [CampusTCPStartupJobUnique.count_eq] at bound
    have empty := List.count_eq_zero_of_not_mem absent
    omega

theorem deliver_path_none (actual : Step input) (report : Report input events)
    (before : actual.before = report.final)
    (nocopy : ∀ actual ∈ report.steps, ∀ id, actual.event ≠ .copyPacket id)
    (item : PacketItem input) (serviceIndex : Nat) (served : Served input)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (payload : item.value.payload = .link serviceIndex served emission emitted)
    (pending : item ∈ report.final.custody.pending)
    (event : actual.event = .deliver serviceIndex bytes policy) :
    P.path actual.result.state served.ticket.value.outputIndex = none := by
  have linear : U.Linear actual.before := by rw [before]; exact CampusTCPStartupJobUnique.Report.linear report nocopy
  have history : Theory.PacketCustody.History actual.before.custody := by
    rw [before]
    exact CampusTCPCustodyFacts.Report.history report
  obtain ⟨packetID, resolved, selected, computed, link, bytesEq, _⟩ :=
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
  let tag := served.ticket.value.outputIndex
  have resolvedIndex : U.packetIndex resolved.item = tag := by
    simp only [U.packetIndex, resolvedPayload, CampusTCPStartupJobUnique.transitIndex, tag]
  let rest := resolved.state.pending.map U.packetIndex ++ actual.before.work.pending.map U.ticketIndex
  have permutation : (U.outputIndices actual.before).Perm (tag :: rest) := by
    have packets := (resolved.completed.pendingPerm.map U.packetIndex).append_right
      (actual.before.work.pending.map U.ticketIndex)
    change (U.outputIndices actual.before).Perm (U.packetIndex resolved.item :: rest) at packets
    rw [resolvedIndex] at packets
    exact packets
  have absent : tag ∉ rest := (List.nodup_cons.mp (permutation.nodup linear.outputIndices_nodup)).1
  have oldMember : tag ∈ U.outputIndices actual.before := permutation.mem_iff.mpr (by simp only [List.mem_cons, true_or])
  have past : tag < actual.before.outputs.length := linear.output_index_lt oldMember
  obtain ⟨effect, custody, core, prepared, final⟩ := actual.transaction
  rw [event] at core prepared
  obtain ⟨work, service⟩ := delivery_quiet core
  simp only [prepareCustody, selected, computed, Except.mapError, bind, Except.bind,
    bytesEq, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at prepared
  subst custody
  apply path_none_of_absent
  rw [final]
  change tag ∉ (finishCustody actual.before effect resolved.state).pending.map U.packetIndex ++
    effect.state.work.pending.map U.ticketIndex
  rw [work]
  cases output : effect.output with
  | none => simpa only [finishCustody, output, service] using absent
  | some produced =>
    have different : tag ≠ actual.before.outputs.length := Nat.ne_of_lt past
    simpa only [finishCustody, output, service, Theory.PacketCustody.mint_pending,
      List.map_append, List.map_cons, List.map_nil, Theory.PacketCustody.newItem,
      Theory.Outstanding.newItem, U.packetIndex, CampusTCPStartupJobUnique.transitIndex,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or, different, false_or,
      rest] using absent

end Netlib.Check.CampusTCPStartupCriticalQueueFrame
