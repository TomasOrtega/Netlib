import Netlib.Protocol.SafeHandoffFacts

/-!
# Installed policies and packet outputs in actual handoff steps

Only installation changes stored configurations.
An established protected binding persists through every accepted step.
-/

namespace Netlib.Protocol.SafeHandoff

open Packet
open StatefulFailover (Gateway)

def nextConfigurations (before : State) : Event → Gateway → Configuration
  | .install gateway configuration => fun selected =>
      if selected = gateway then configuration else before.configurations selected
  | _ => before.configurations

private theorem control_result (before : State) (event : StatefulFailover.Event) (raw : RawResult)
    (computed : (do
      let operated ← StatefulFailover.step before.gateways event
      pure (⟨{ before with gateways := operated.state }, none, none, operated.packet⟩ : RawResult)) = .ok raw) :
    ∃ operated, StatefulFailover.step before.gateways event = .ok operated ∧
      raw = ⟨{ before with gateways := operated.state }, none, none, operated.packet⟩ := by
  cases found : StatefulFailover.step before.gateways event with
  | error reason => simp [found, bind, Except.bind] at computed
  | ok operated =>
    simp only [found, bind, Except.bind, pure, Except.pure] at computed
    cases computed
    exact ⟨operated, rfl, rfl⟩

private theorem failover_no_packet (before : StatefulFailover.State) (event : StatefulFailover.Event)
    (result : StatefulFailover.Result) (absent : ∀ call, event ≠ .packet call)
    (computed : StatefulFailover.step before event = .ok result) : result.packet = none := by
  cases event with
  | packet call => exact False.elim (absent call rfl)
  | stage zone key | commit timeout | handoff leg gateway | fence gateway | erase gateway zone key | forget =>
    simp only [StatefulFailover.step] at computed
    repeat' first
      | (cases computed; rfl)
      | (split at computed <;> try simp [bind, Except.bind, Except.mapError, pure, throw] at computed)

private theorem control_configurations (before : State) (event : StatefulFailover.Event) (raw : RawResult)
    (computed : (do
      let operated ← StatefulFailover.step before.gateways event
      pure (⟨{ before with gateways := operated.state }, none, none, operated.packet⟩ : RawResult)) = .ok raw) :
    raw.state.configurations = before.configurations := by
  obtain ⟨_, _, rfl⟩ := control_result before event raw computed
  rfl

private theorem core_configurations (before : State) (event : Event) (raw : RawResult)
    (computed : core before event = .ok raw) : raw.state.configurations = nextConfigurations before event := by
  cases event with
  | establish call =>
    simp only [core] at computed
    split at computed
    · simp [throw, bind, Except.bind] at computed
    · change (do
        let operated ← StatefulFailover.step before.gateways
          (.packet ⟨.primary, .client, (before.configurations .primary).pipeline, call⟩)
        pure (⟨{ before with gateways := operated.state }, none, none, operated.packet⟩ : RawResult)) = .ok raw at computed
      obtain ⟨_, _, rfl⟩ := control_result before _ raw computed
      rfl
  | stage zone key =>
    simp only [core] at computed
    repeat' first
      | (cases computed; rfl)
      | (split at computed <;> try simp [bind, Except.bind, pure, throw] at computed)
  | commit timeout =>
    simp only [core] at computed
    repeat' (split at computed <;> try simp [bind, Except.bind, throw] at computed)
    exact control_configurations before (.commit timeout) raw computed
  | handoff leg gateway =>
    simp only [core] at computed
    repeat' (split at computed <;> try simp [bind, Except.bind, throw] at computed)
    exact control_configurations before (.handoff leg gateway) raw computed
  | fence gateway =>
    simp only [core] at computed
    repeat' (split at computed <;> try simp [bind, Except.bind, throw] at computed)
    exact control_configurations before (.fence gateway) raw computed
  | forget =>
    change (do
      let operated ← StatefulFailover.step before.gateways .forget
      pure (⟨{ before with gateways := operated.state }, none, none, operated.packet⟩ : RawResult)) = .ok raw at computed
    obtain ⟨_, _, rfl⟩ := control_result before _ raw computed
    rfl
  | install gateway configuration =>
    funext selected
    exact core_install_configuration before gateway configuration raw computed selected
  | assign direction source =>
    simp only [core] at computed
    repeat' first
      | (cases computed; rfl)
      | (split at computed <;> try simp [bind, Except.bind, pure, throw] at computed)
  | serve id =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, configurations, _⟩ := core_serve_facts before id raw computed
    exact configurations

theorem step_configurations (before : State) (event : Event) (result : Result)
    (accepted : step before event = .ok result) :
    result.state.configurations = nextConfigurations before event := by
  obtain ⟨_, raw, computed, same⟩ := step_core before event result accepted
  have fields := core_configurations before event raw computed
  rw [← same] at fields
  exact fields

private theorem control_binding (before : State) (event : StatefulFailover.Event) (raw : RawResult)
    (computed : (do
      let operated ← StatefulFailover.step before.gateways event
      pure (⟨{ before with gateways := operated.state }, none, none, operated.packet⟩ : RawResult)) = .ok raw) :
    raw.state.binding = before.binding := by
  obtain ⟨_, _, rfl⟩ := control_result before event raw computed
  rfl

private theorem core_binding (before : State) (event : Event) (raw : RawResult) (entry : NetfilterNAT.Entry)
    (binding : before.binding = some entry) (computed : core before event = .ok raw) :
    raw.state.binding = some entry := by
  cases event with
  | establish call => simp [core, binding, throw, bind, Except.bind] at computed
  | stage zone key =>
    simp only [core, binding, bind, Except.bind] at computed
    repeat' first
      | (cases computed; first | rfl | simp_all)
      | (split at computed <;> try simp [pure, throw] at computed)
  | commit timeout =>
    simp only [core, binding] at computed
    repeat' (split at computed <;> try simp [bind, Except.bind, throw] at computed)
    exact (control_binding before (.commit timeout) raw computed).trans binding
  | handoff leg gateway =>
    simp only [core, binding] at computed
    repeat' (split at computed <;> try simp [bind, Except.bind, throw] at computed)
    exact (control_binding before (.handoff leg gateway) raw computed).trans binding
  | fence gateway =>
    simp only [core] at computed
    repeat' (split at computed <;> try simp [bind, Except.bind, throw] at computed)
    exact (control_binding before (.fence gateway) raw computed).trans binding
  | forget => exact (control_binding before .forget raw computed).trans binding
  | install gateway configuration => cases computed; exact binding
  | assign direction source =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, same, _⟩ := core_assign_facts before direction source raw computed
    exact same.trans binding
  | serve id =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, same, _⟩ := core_serve_facts before id raw computed
    exact same.trans binding

theorem step_binding (before : State) (event : Event) (result : Result) (entry : NetfilterNAT.Entry)
    (binding : before.binding = some entry) (accepted : step before event = .ok result) :
    result.state.binding = some entry := by
  obtain ⟨_, raw, computed, same⟩ := step_core before event result accepted
  have fields := core_binding before event raw entry binding computed
  rw [← same] at fields
  exact fields

private theorem control_no_outputs (before : State) (event : StatefulFailover.Event) (raw : RawResult)
    (computed : (do
      let operated ← StatefulFailover.step before.gateways event
      pure (⟨{ before with gateways := operated.state }, none, none, operated.packet⟩ : RawResult)) = .ok raw)
    (absent : ∀ call, event ≠ .packet call) : raw.served = none ∧ raw.established = none := by
  obtain ⟨operated, accepted, rfl⟩ := control_result before event raw computed
  exact ⟨rfl, failover_no_packet before.gateways event operated absent accepted⟩

private theorem core_no_outputs (before : State) (event : Event) (raw : RawResult)
    (computed : core before event = .ok raw)
    (notServe : ∀ id, event ≠ .serve id) (notEstablish : ∀ call, event ≠ .establish call) :
    raw.served = none ∧ raw.established = none := by
  cases event with
  | establish call => exact False.elim (notEstablish call rfl)
  | serve id => exact False.elim (notServe id rfl)
  | stage zone key =>
    simp only [core] at computed
    repeat' first
      | (cases computed; exact ⟨rfl, rfl⟩)
      | (split at computed <;> try simp [bind, Except.bind, pure, throw] at computed)
  | commit timeout =>
    simp only [core] at computed
    repeat' (split at computed <;> try simp [bind, Except.bind, throw] at computed)
    exact control_no_outputs before (.commit timeout) raw computed (by intro call impossible; cases impossible)
  | handoff leg gateway =>
    simp only [core] at computed
    repeat' (split at computed <;> try simp [bind, Except.bind, throw] at computed)
    exact control_no_outputs before (.handoff leg gateway) raw computed (by intro call impossible; cases impossible)
  | fence gateway =>
    simp only [core] at computed
    repeat' (split at computed <;> try simp [bind, Except.bind, throw] at computed)
    exact control_no_outputs before (.fence gateway) raw computed (by intro call impossible; cases impossible)
  | forget => exact control_no_outputs before .forget raw computed (by intro call impossible; cases impossible)
  | install gateway configuration => cases computed; exact ⟨rfl, rfl⟩
  | assign direction source =>
    simp only [core] at computed
    repeat' first
      | (cases computed; exact ⟨rfl, rfl⟩)
      | (split at computed <;> try simp [bind, Except.bind, pure, throw] at computed)

theorem step_no_outputs (before : State) (event : Event) (result : Result)
    (accepted : step before event = .ok result)
    (notServe : ∀ id, event ≠ .serve id) (notEstablish : ∀ call, event ≠ .establish call) :
    result.served = none ∧ result.established = none := by
  obtain ⟨_, raw, computed, same⟩ := step_core before event result accepted
  have fields := core_no_outputs before event raw computed notServe notEstablish
  rw [← same] at fields
  exact fields

private theorem core_establish_facts (before : State) (call : WireForwarding.Input) (raw : RawResult)
    (computed : core before (.establish call) = .ok raw) :
    ∃ outcome, WireForwarding.step (before.configurations .primary).pipeline before.gateways.primary call = .ok outcome ∧
      raw.served = none ∧ raw.established = some ⟨⟨.primary, .client, (before.configurations .primary).pipeline, call⟩, outcome⟩ := by
  simp only [core] at computed
  split at computed
  · simp [throw, bind, Except.bind] at computed
  · obtain ⟨operated, accepted, rfl⟩ := control_result before _ raw computed
    obtain ⟨_, _, outcome, forwarded, stored, _⟩ := StatefulFailover.step_packet before.gateways _ operated accepted
    exact ⟨outcome, forwarded, rfl, stored⟩

theorem step_establish_facts (before : State) (call : WireForwarding.Input) (result : Result)
    (accepted : step before (.establish call) = .ok result) :
    ∃ outcome, WireForwarding.step (before.configurations .primary).pipeline before.gateways.primary call = .ok outcome ∧
      result.served = none ∧
      result.established = some ⟨⟨.primary, .client, (before.configurations .primary).pipeline, call⟩, outcome⟩ := by
  obtain ⟨_, raw, computed, same⟩ := step_core before (.establish call) result accepted
  have fields := core_establish_facts before call raw computed
  rw [← same] at fields
  exact fields

private theorem core_serve_established_none (before : State) (id : Nat) (raw : RawResult)
    (computed : core before (.serve id) = .ok raw) : raw.established = none := by
  simp only [core, bind, Except.bind, Except.mapError] at computed
  repeat' first
    | (cases computed; rfl)
    | (split at computed <;> try simp [pure, throw] at computed)

private theorem core_served_event (before : State) (event : Event) (raw : RawResult)
    (computed : core before event = .ok raw) (served : PacketResult) (stored : raw.served = some served) :
    ∃ id, event = .serve id := by
  cases event with
  | serve id => exact ⟨id, rfl⟩
  | establish call =>
    obtain ⟨_, _, absent, _⟩ := core_establish_facts before call raw computed
    rw [absent] at stored
    cases stored
  | stage zone key | commit timeout | handoff leg gateway | fence gateway | forget
      | install gateway configuration | assign direction source =>
    have absent := (core_no_outputs before _ raw computed
      (by intro id impossible; cases impossible) (by intro call impossible; cases impossible)).1
    rw [absent] at stored
    cases stored

theorem step_served_event (before : State) (event : Event) (result : Result)
    (accepted : step before event = .ok result) (served : PacketResult) (stored : result.served = some served) :
    ∃ id, event = .serve id := by
  obtain ⟨_, raw, computed, same⟩ := step_core before event result accepted
  have actual : raw.served = some served := by rw [← same]; exact stored
  exact core_served_event before event raw computed served actual

private theorem core_established_event (before : State) (event : Event) (raw : RawResult)
    (computed : core before event = .ok raw) (established : StatefulFailover.PacketResult)
    (stored : raw.established = some established) : ∃ call, event = .establish call := by
  cases event with
  | establish call => exact ⟨call, rfl⟩
  | serve id =>
    rw [core_serve_established_none before id raw computed] at stored
    cases stored
  | stage zone key | commit timeout | handoff leg gateway | fence gateway | forget
      | install gateway configuration | assign direction source =>
    have absent := (core_no_outputs before _ raw computed
      (by intro id impossible; cases impossible) (by intro call impossible; cases impossible)).2
    rw [absent] at stored
    cases stored

theorem step_established_event (before : State) (event : Event) (result : Result)
    (accepted : step before event = .ok result) (established : StatefulFailover.PacketResult)
    (stored : result.established = some established) : ∃ call, event = .establish call := by
  obtain ⟨_, raw, computed, same⟩ := step_core before event result accepted
  have actual : raw.established = some established := by rw [← same]; exact stored
  exact core_established_event before event raw computed established actual

end Netlib.Protocol.SafeHandoff
