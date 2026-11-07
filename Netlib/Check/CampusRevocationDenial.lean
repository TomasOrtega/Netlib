import Netlib.Check.CampusRevocationRank
import Netlib.Protocol.SafeHandoffPolicyFrames

/-!
# No new arrivals after both checked deny targets install

Packet processing uses the actual stored configuration and tracker.
Earlier queue contents remain separate from new wire output.
-/

namespace Netlib.Check.CampusRevocationModel

open Packet Protocol
open StatefulFailover (Gateway)
open CampusRevocationTargets

theorem handoff_outputs_none (targets : Targets input after) (closed : revoked input after = true)
    (before : Protocol.SafeHandoff.State) (event : Protocol.SafeHandoff.Event)
    (result : Protocol.SafeHandoff.Result)
    (installed : ∀ gateway, before.configurations gateway = targets.get gateway)
    (accepted : Protocol.SafeHandoff.step before event = .ok result) :
    (∀ served, result.served = some served → served.outcome.output = none) ∧
      (∀ established, result.established = some established → established.outcome.output = none) := by
  constructor
  · intro served stored
    obtain ⟨id, selected⟩ := Protocol.SafeHandoff.step_served_event before event result accepted served stored
    rw [selected] at accepted
    have equivalent : Examples.SessionFirewallDeployment.ForwardEquivalent
        (before.configurations served.ticket.value.gateway).pipeline
        (targets.checked served.ticket.value.gateway).compiled := by
      rw [installed served.ticket.value.gateway]
      exact targets.forward_equivalent served.ticket.value.gateway
    exact Examples.SafeHandoffDeployment.serve_output_none_of_denied
      (targets.checked served.ticket.value.gateway).compiled (SessionFirewall.stateAt_safe input.authentication after)
      (revoked_denied input after closed) before id result served accepted stored equivalent
  · intro established stored
    obtain ⟨call, selected⟩ := Protocol.SafeHandoff.step_established_event before event result accepted established stored
    rw [selected] at accepted
    obtain ⟨outcome, computed, _, reported⟩ := Protocol.SafeHandoff.step_establish_facts before call result accepted
    have same : established =
        (⟨⟨.primary, .client, (before.configurations .primary).pipeline, call⟩, outcome⟩ : StatefulFailover.PacketResult) :=
      Option.some.inj (stored.symm.trans reported)
    cases same
    apply targets.wire_output_none closed .primary before.gateways.primary call outcome
    simpa only [installed .primary] using computed

theorem Payload.arrivals_nil (payload : Payload input budget before) (targets : Targets input after)
    (closed : revoked input after = true)
    (installed : ∀ gateway, before.campus.deployment.handoff.configurations gateway = targets.get gateway) :
    payload.arrivals = [] := by
  cases payload with
  | campus observation result computed =>
    have same := CampusDeployment.step_before input budget before.campus observation result computed
    have current : ∀ gateway, result.before.deployment.handoff.configurations gateway = targets.get gateway := by
      intro gateway
      rw [same]
      exact installed gateway
    cases oldPayload : result.payload with
    | authentication evidence => simp [Payload.arrivals, campusDatagrams, oldPayload]
    | withdraw evidence => simp [Payload.arrivals, campusDatagrams, oldPayload]
    | network evidence =>
      have excluded := handoff_outputs_none targets closed result.before.deployment.handoff
        evidence.event evidence.model current evidence.actual_step.1
      cases served : evidence.model.served with
      | some packet =>
        have absent := excluded.1 packet served
        simp [Payload.arrivals, campusDatagrams, oldPayload, served, absent]
      | none =>
        cases established : evidence.model.established with
        | none => simp [Payload.arrivals, campusDatagrams, oldPayload, served, established]
        | some packet =>
          have absent := excluded.2 packet established
          simp [Payload.arrivals, campusDatagrams, oldPayload, served, established, absent]
  | packet call outcome computed certificate =>
    have absent := targets.wire_output_none closed call.gateway
      (before.campus.deployment.handoff.gateways.table call.gateway) call.input outcome
      (by simpa only [State.packet, PacketCall.input, installed call.gateway] using computed)
    simp only [Payload.arrivals, absent]
    rfl
  | deliver capacity => rfl
  | idle => rfl

theorem Payload.backlog_nonincrease (payload : Payload input budget before) (targets : Targets input after)
    (closed : revoked input after = true)
    (installed : ∀ gateway, before.campus.deployment.handoff.configurations gateway = targets.get gateway) :
    payload.state.queue.pending.length ≤ before.queue.pending.length := by
  change (Theory.Queue.advance before.queue payload.tick).pending.length ≤ before.queue.pending.length
  have empty := payload.arrivals_nil targets closed installed
  have bounded := Theory.Queue.backlog_bounded before.queue payload.tick
  simpa only [Payload.tick, empty, List.length_nil, Nat.add_zero] using bounded

theorem Payload.queue_served_nil (payload : Payload input budget before) (targets : Targets input after)
    (closed : revoked input after = true)
    (installed : ∀ gateway, before.campus.deployment.handoff.configurations gateway = targets.get gateway)
    (empty : before.queue.pending = []) :
    (Theory.Queue.step before.queue payload.tick).served = [] := by
  have absent := payload.arrivals_nil targets closed installed
  simp [Theory.Queue.step, Payload.tick, absent, empty]

theorem Step.arrivals_nil_of_ready (actual : Step input budget) (targets : Targets input after)
    (closed : revoked input after = true)
    (installed : CampusRevocationControl.ready targets actual.before = true) :
    actual.effect.payload.arrivals = [] := by
  apply actual.effect.payload.arrivals_nil targets closed
  intro gateway
  exact (CampusRevocationControl.installed_correct targets actual.before gateway).mp
    ((CampusRevocationControl.ready_correct targets actual.before).mp installed gateway)

end Netlib.Check.CampusRevocationModel
