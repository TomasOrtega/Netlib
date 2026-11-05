import Netlib.Protocol.SafeHandoff
namespace Netlib.Protocol.SafeHandoff
open Packet
open StatefulFailover (Gateway Leg)

theorem State.uses_iff (state : State) (gateway : Gateway) : state.uses gateway = true ↔
    state.gateways.owners.client = gateway ∨ state.gateways.owners.server = gateway ∨
      ∃ item ∈ state.work.pending, item.value.gateway = gateway := by
  simp [State.uses, Bool.or_eq_true, List.any_eq_true, or_assoc]

theorem State.unfenced_iff (state : State) : state.Unfenced ↔
    ∀ gateway, state.uses gateway = true → state.gateways.isFenced gateway = false := by
  constructor
  · intro safe gateway used
    cases gateway
    · exact safe.1 used
    · exact safe.2 used
  · intro safe
    exact ⟨safe .primary, safe .standby⟩

theorem State.uses_mono (before after : State) (owners : after.gateways.owners = before.gateways.owners)
    (pending : ∀ item ∈ after.work.pending, before.uses item.value.gateway = true) :
    ∀ gateway, after.uses gateway = true → before.uses gateway = true := by
  intro gateway used
  rcases (State.uses_iff after gateway).mp used with client | server | ⟨item, member, same⟩
  · apply (State.uses_iff before gateway).mpr
    exact Or.inl (by rw [← owners]; exact client)
  · apply (State.uses_iff before gateway).mpr
    exact Or.inr (Or.inl (by rw [← owners]; exact server))
  · have old := pending item member
    simpa only [same] using old

theorem State.unfenced_transfer (before after : State) (safe : before.Unfenced)
    (uses : ∀ gateway, after.uses gateway = true → before.uses gateway = true)
    (fenced : after.gateways.fenced = before.gateways.fenced) : after.Unfenced := by
  apply (State.unfenced_iff after).mpr
  intro gateway used
  have old := (State.unfenced_iff before).mp safe gateway (uses gateway used)
  simpa only [StatefulFailover.State.isFenced, fenced] using old

theorem State.safe_of_flow (state : State) (entry : NetfilterNAT.Entry) (binding : state.binding = some entry)
    (valid : state.gateways.Valid) (work : state.work.Valid) (unfenced : state.Unfenced)
    (supported : FlowSupported entry) (primary : TrackedFlow.Ready state.gateways.primary entry)
    (pending : ∀ item ∈ state.work.pending, item.value.entry = entry)
    (standby : state.uses .standby = true → TrackedFlow.Ready state.gateways.standby entry) : state.Safe := by
  exact ⟨valid, work, unfenced, by simpa only [binding, State.FlowSafe] using And.intro supported ⟨primary, pending, standby⟩⟩

theorem State.safe_epoch (state : State) (epoch : Nat) (safe : state.Safe) :
    ({ state with gateways := { state.gateways with epoch := epoch } } : State).Safe := safe

theorem State.safe_configurations (state : State) (configurations : Gateway → Configuration) (safe : state.Safe) :
    ({ state with configurations := configurations } : State).Safe := safe

theorem step_of_core (before : State) (event : Event) (raw : RawResult) (safe : before.Safe)
    (computed : core before event = .ok raw) (after : raw.state.Safe) :
    ∃ result, step before event = .ok result ∧ result.toRawResult = raw := by
  have checked := (State.check_correct _).mpr safe
  have afterChecked := (State.check_correct _).mpr after
  refine ⟨{ raw with safe := after }, ?_, rfl⟩
  simp only [step, checked, dite_true, computed, bind, Except.bind, afterChecked, pure, Except.pure]

theorem State.outstanding_eq_count (state : State) (gateway : Gateway) :
    state.outstanding gateway = Theory.Outstanding.count state.work (fun ticket => decide (ticket.gateway = gateway)) := by
  simp only [State.outstanding, Theory.Outstanding.count, List.countP_eq_length_filter]
theorem State.outstanding_zero (state : State) (gateway : Gateway) : state.outstanding gateway = 0 ↔
    ∀ item ∈ state.work.pending, item.value.gateway ≠ gateway := by
  simp [State.outstanding, List.length_eq_zero_iff, List.filter_eq_nil_iff]

end Netlib.Protocol.SafeHandoff
