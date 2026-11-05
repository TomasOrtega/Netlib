import Netlib.Protocol.SafeHandoffCommonFacts

namespace Netlib.Protocol.SafeHandoff

open Packet
open StatefulFailover (Gateway Leg)

private def handed (before : State) (selectedLeg : Leg) (gateway : Gateway) : State :=
  { before with gateways := { before.gateways with
    owners := before.gateways.owners.set selectedLeg gateway
    epoch := before.gateways.epoch + 1 } }

private theorem handed_uses (before : State) (selectedLeg : Leg) (gateway selected : Gateway)
    (used : (handed before selectedLeg gateway).uses selected = true) :
    before.uses selected = true ∨ selected = gateway := by
  rcases (State.uses_iff _ _).mp used with client | server | ⟨item, member, same⟩
  · change (before.gateways.owners.set selectedLeg gateway).client = selected at client
    cases selectedLeg
    · exact Or.inr client.symm
    · exact Or.inl ((State.uses_iff _ _).mpr (Or.inl client))
  · change (before.gateways.owners.set selectedLeg gateway).server = selected at server
    cases selectedLeg
    · exact Or.inl ((State.uses_iff _ _).mpr (Or.inr (Or.inl server)))
    · exact Or.inr server.symm
  · have old := before.uses_pending item member
    exact Or.inl (by simpa only [same] using old)

theorem handoff_core_completes (before : State) (selectedLeg : Leg) (gateway : Gateway)
    (safe : before.Safe) (binding : before.binding = some entry)
    (ready : TrackedFlow.Ready (before.gateways.table gateway) entry)
    (unfenced : before.gateways.isFenced gateway = false) :
    ∃ raw, core before (.handoff selectedLeg gateway) = .ok raw ∧ raw.state.Safe := by
  have checkedA := (ConntrackLifecycle.State.check_correct _).mpr safe.1.1
  have checkedB := (ConntrackLifecycle.State.check_correct _).mpr safe.1.2
  have readyBool := (TrackedFlow.ready_correct _ _).mpr ready
  let after := handed before selectedLeg gateway
  let operated : StatefulFailover.Result := ⟨after.gateways, safe.1, none, none⟩
  have computed : StatefulFailover.step before.gateways (.handoff selectedLeg gateway) = .ok operated := by
    simp only [StatefulFailover.step, checkedA, checkedB, and_self, dite_true, pure, Except.pure]
    rfl
  let raw : RawResult := ⟨after, none, none, none⟩
  refine ⟨raw, ?_, ?_⟩
  · simp only [core, binding, readyBool, Bool.not_true, Bool.false_eq_true, ite_false, unfenced]
    change (do
      let result ← StatefulFailover.step before.gateways (.handoff selectedLeg gateway)
      pure (⟨{ before with gateways := result.state }, none, none, result.packet⟩ : RawResult)) = .ok raw
    rw [computed]
    rfl
  · have flow := safe.flow binding
    apply State.safe_of_flow after entry binding safe.1 safe.2.1
    · apply (State.unfenced_iff _).mpr
      intro selected used
      rcases handed_uses before selectedLeg gateway selected used with old | same
      · exact safe.unfenced selected old
      · subst selected
        exact unfenced
    · exact flow.1
    · exact flow.2.1
    · exact flow.2.2.1
    · intro used
      rcases handed_uses before selectedLeg gateway .standby used with old | same
      · exact safe.ready binding .standby old
      · rw [← same] at ready
        exact ready

theorem install_core_completes (before : State) (gateway : Gateway) (configuration : Configuration)
    (safe : before.Safe) :
    ∃ raw, core before (.install gateway configuration) = .ok raw ∧ raw.state.Safe := by
  refine ⟨_, rfl, ?_⟩
  exact safe

theorem forget_core_completes (before : State) (safe : before.Safe) :
    ∃ raw, core before .forget = .ok raw ∧ raw.state.Safe := by
  have checkedA := (ConntrackLifecycle.State.check_correct _).mpr safe.1.1
  have checkedB := (ConntrackLifecycle.State.check_correct _).mpr safe.1.2
  let next := { before.gateways with cache := none, epoch := before.gateways.epoch + 1 }
  let operated : StatefulFailover.Result := ⟨next, safe.1, none, none⟩
  have computed : StatefulFailover.step before.gateways .forget = .ok operated := by
    simp only [StatefulFailover.step, checkedA, checkedB, and_self, dite_true, pure, Except.pure]
    rfl
  let raw : RawResult := ⟨{ before with gateways := next }, none, none, none⟩
  refine ⟨raw, ?_, safe⟩
  change (do
    let result ← StatefulFailover.step before.gateways .forget
    pure (⟨{ before with gateways := result.state }, none, none, result.packet⟩ : RawResult)) = .ok raw
  rw [computed]
  rfl

theorem fence_core_completes (before : State) (gateway : Gateway) (safe : before.Safe)
    (client : before.gateways.owners.client ≠ gateway) (server : before.gateways.owners.server ≠ gateway)
    (drained : before.outstanding gateway = 0) :
    ∃ raw, core before (.fence gateway) = .ok raw ∧ raw.state.Safe := by
  have checkedA := (ConntrackLifecycle.State.check_correct _).mpr safe.1.1
  have checkedB := (ConntrackLifecycle.State.check_correct _).mpr safe.1.2
  have inactive : ¬(before.gateways.owners.client = gateway ∨ before.gateways.owners.server = gateway) :=
    not_or.mpr ⟨client, server⟩
  have unused : ¬before.uses gateway = true := by
    intro used
    rcases (State.uses_iff _ _).mp used with owner | owner | ⟨item, member, same⟩
    · exact client owner
    · exact server owner
    · exact ((State.outstanding_zero _ _).mp drained item member) same
  let next := { before.gateways with
    fenced := gateway :: before.gateways.fenced
    epoch := before.gateways.epoch + 1 }
  let after : State := { before with gateways := next }
  let operated : StatefulFailover.Result := ⟨next, safe.1, none, none⟩
  have computed : StatefulFailover.step before.gateways (.fence gateway) = .ok operated := by
    simp only [StatefulFailover.step, checkedA, checkedB, and_self, dite_true, pure, Except.pure]
    rfl
  let raw : RawResult := ⟨after, none, none, none⟩
  refine ⟨raw, ?_, ?_⟩
  · simp only [core, inactive, ite_false, drained, bne_self_eq_false, Bool.false_eq_true]
    change (do
      let result ← StatefulFailover.step before.gateways (.fence gateway)
      pure (⟨{ before with gateways := result.state }, none, none, result.packet⟩ : RawResult)) = .ok raw
    rw [computed]
    rfl
  · refine ⟨safe.1, safe.2.1, ?_, safe.2.2.2⟩
    apply (State.unfenced_iff _).mpr
    intro selected used
    have oldUsed : before.uses selected = true := used
    have different : gateway ≠ selected := by
      intro same
      apply unused
      simpa only [same] using oldUsed
    have notEqual : decide (gateway = selected) = false := by simp [different]
    change (gateway :: before.gateways.fenced).any (fun other => decide (other = selected)) = false
    simp only [List.any_cons, notEqual, Bool.false_or]
    exact safe.unfenced selected oldUsed

theorem commit_core_completes (before : State) (timeout : Nat) (selection : ConntrackReplication.Selection)
    (safe : before.Safe) (binding : before.binding = some entry) (cached : before.gateways.cache = some selection)
    (same : selection.record.entry = entry) (bounded : 0 < timeout ∧ timeout < 4294967296)
    (fresh : ∀ direction, entry.flow.key direction ∉ before.gateways.standby.model.keys) :
    ∃ raw, core before (.commit timeout) = .ok raw ∧ raw.state.Safe := by
  have selectedFresh : ∀ direction, selection.recordForInstall.entry.flow.key direction ∉
      before.gateways.standby.model.keys := by
    simpa only [ConntrackReplication.Selection.recordForInstall, same] using fresh
  obtain ⟨installed, committed⟩ := ConntrackReplication.commit_completes _ _ _ safe.1.2 bounded selectedFresh
  have fields := ConntrackReplication.commit_fields _ _ _ _ committed
  have ready : TrackedFlow.Ready installed.state entry := by
    refine ⟨installed.selection.recordForInstall, installed.selected_member, ?_⟩
    rw [fields.2.1]
    exact same
  let next := { before.gateways with
    standby := installed.state
    epoch := before.gateways.epoch + 1 }
  let after : State := { before with gateways := next }
  have valid : next.Valid := ⟨safe.1.1, installed.valid⟩
  let operated : StatefulFailover.Result := ⟨next, valid, none, some installed⟩
  have checkedA := (ConntrackLifecycle.State.check_correct _).mpr safe.1.1
  have computed : StatefulFailover.step before.gateways (.commit timeout) = .ok operated := by
    simp only [StatefulFailover.step, checkedA, dite_true, cached, committed,
      Except.mapError, bind, Except.bind, pure, Except.pure]
    simp only [operated, next, cached]
    rfl

  let raw : RawResult := ⟨after, none, none, none⟩
  refine ⟨raw, ?_, ?_⟩
  · simp only [core, binding, cached, same, ne_self_iff_false, ite_false]
    change (do
      let result ← StatefulFailover.step before.gateways (.commit timeout)
      pure (⟨{ before with gateways := result.state }, none, none, result.packet⟩ : RawResult)) = .ok raw
    rw [computed]
    rfl
  · have flow := safe.flow binding
    apply State.safe_of_flow after entry binding valid safe.2.1 safe.2.2.1 flow.1 flow.2.1 flow.2.2.1
    intro _
    exact ready

private theorem stage_selected (source : ConntrackLifecycle.State) (epoch zone : Nat) (key : Header)
    (entry : NetfilterNAT.Entry) (direction : FlowNAT.Direction) (valid : source.Valid)
    (ready : TrackedFlow.Ready source entry) (supported : ConntrackReplication.Profile ⟨entry, false⟩)
    (attached : entry.flow.key direction = (zone, key)) :
    ∃ selection, ConntrackReplication.stage source epoch zone key = .ok selection ∧ selection.record.entry = entry := by
  obtain ⟨record, member, same⟩ := ready
  have profile : ConntrackReplication.Profile record := by
    simpa only [ConntrackReplication.Profile, same] using supported
  have checked := (ConntrackLifecycle.State.check_correct _).mpr valid
  have available : TrackedFlow.Ready source entry := ⟨record, member, same⟩
  have found := available.lookup valid direction
  have coordinates : (entry.flow.zone direction, entry.flow.input direction) = (zone, key) := attached
  rw [(Prod.mk.inj coordinates).1, (Prod.mk.inj coordinates).2] at found
  have row := TrackedFlow.find_record source valid record member
  rw [same] at row
  let selection : ConntrackReplication.Selection :=
    ⟨epoch, source, valid, record, member, profile, direction, zone, key, by rw [same]; exact attached⟩
  refine ⟨selection, ?_, same⟩
  unfold ConntrackReplication.stage
  simp only [checked, dite_true]
  split
  · rename_i missed
    rw [found] at missed
    cases missed
  · rename_i hit equation
    have equal := Option.some.inj (equation.symm.trans found)
    subst hit
    split
    · rename_i missed
      rw [row] at missed
      cases missed
    · rename_i selected equation
      have equal := Option.some.inj (equation.symm.trans row)
      subst selected
      simp only [profile, dite_true, pure, Except.pure]
      rfl

theorem stage_core_completes (before : State) (zone : Nat) (key : Header) (entry : NetfilterNAT.Entry)
    (direction : FlowNAT.Direction) (safe : before.Safe) (supported : FlowSupported entry)
    (primary : TrackedFlow.Ready before.gateways.primary entry)
    (binding : before.binding = none ∨ before.binding = some entry)
    (standby : before.uses .standby = true → TrackedFlow.Ready before.gateways.standby entry)
    (attached : entry.flow.key direction = (zone, key)) :
    ∃ raw, core before (.stage zone key) = .ok raw ∧ raw.state.Safe := by
  obtain ⟨selection, staged, same⟩ := stage_selected before.gateways.primary before.gateways.epoch zone key
    entry direction safe.1.1 primary supported.2 attached
  have checkedA := (ConntrackLifecycle.State.check_correct _).mpr safe.1.1
  have checkedB := (ConntrackLifecycle.State.check_correct _).mpr safe.1.2
  let next := { before.gateways with
    cache := some selection
    epoch := before.gateways.epoch + 1 }
  let operated : StatefulFailover.Result := ⟨next, safe.1, none, none⟩
  have computed : StatefulFailover.step before.gateways (.stage zone key) = .ok operated := by
    simp only [StatefulFailover.step, checkedA, checkedB, and_self, dite_true, staged,
      Except.mapError, bind, Except.bind, pure, Except.pure]
    rfl
  let after : State := { before with gateways := next, binding := some entry }
  let raw : RawResult := ⟨after, none, none, none⟩
  refine ⟨raw, ?_, ?_⟩
  · rcases binding with absent | current
    · simp only [core, computed, bind, Except.bind, operated, next, absent, same, pure, Except.pure]
      rfl
    · simp only [core, computed, bind, Except.bind, operated, next, current, same, ne_self_iff_false, ite_false, pure, Except.pure]
      rfl
  · apply State.safe_of_flow after entry rfl safe.1 safe.2.1 safe.2.2.1 supported primary
    · rcases binding with absent | current
      · have empty : before.work.pending = [] := by simpa only [absent] using safe.2.2.2
        simp only [after, empty, List.not_mem_nil, false_implies, implies_true]
      · exact (safe.flow current).2.2.1
    · exact standby

theorem core_install_configuration (before : State) (gateway : Gateway) (configuration : Configuration)
    (raw : RawResult) (computed : core before (.install gateway configuration) = .ok raw) (selected : Gateway) :
    raw.state.configurations selected =
      if selected = gateway then configuration else before.configurations selected := by
  cases computed
  rfl

end Netlib.Protocol.SafeHandoff
