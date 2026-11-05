import Netlib.Check.ReassemblyForwarding
import Netlib.Examples.WireNATDeployment

/-! Current session permission applies when ingress buffering produces a datagram. -/

namespace Netlib.Examples.ReassemblyDeployment

open Packet Protocol

variable {context : Context} {session : EAPSession.State} {requirements : List Compile.SessionFirewall.Intent}

theorem process_current_permission
    (compiled : Compile.SessionFirewall.Certified context session requirements) (safe : session.Safe context)
    (active : ReassemblyForwarding.Pipeline)
    (installed : SessionFirewallDeployment.ForwardEquivalent active.forwarding.forwarding compiled)
    (reassembled : IPv4Reassembly.Output) (source : ReassemblyForwarding.Source reassembled)
    (wire : WireForwarding.Input) (same : wire.packet = source.packet)
    (prepared : ConntrackLifecycle.Prepared wire.lifecycle) (outcome : ReassemblyForwarding.Outcome wire.packet)
    (accepted : ReassemblyForwarding.process active reassembled source wire same prepared = .ok outcome)
    (emission : WireForwarding.Emission wire.packet) (forwarded : outcome.output = some emission) :
    WireNATDeployment.OutputFacts wire.packet emission ∧ 1 < wire.packet.ip.packet.ttl.toNat ∧
      ∃ requirement ∈ requirements, requirement.test.Holds outcome.afterDestination ∧
        Session.Valid context session.session requirement.scope ∧
        EAPAuth.State.Ready (EAPSession.authContext context) session.auth := by
  obtain ⟨cap, sized⟩ := ReassemblyForwarding.process_output_has_cap active reassembled source wire same
    prepared outcome accepted emission forwarded
  obtain ⟨_, parent, _, live, _, _, finished, sameOutcome, parentOutput⟩ :=
    ReassemblyForwarding.process_output_cap active reassembled source wire same prepared outcome accepted cap sized emission forwarded
  obtain ⟨model, computed, sameParent⟩ :=
    WireForwarding.finish_realizes active.forwarding.forwarding wire (same ▸ source.valid) prepared parent finished
  obtain ⟨other, otherComputed, _, _, otherOutput⟩ :=
    WireForwarding.finish_output active.forwarding.forwarding wire (same ▸ source.valid) prepared parent finished emission parentOutput
  have equal : other = model := Except.ok.inj (otherComputed.symm.trans computed)
  subst other
  have permitted := (ConntrackLifecycle.process_filters active.forwarding.forwarding prepared model emission.target
    computed otherOutput).2.1
  have native : compiled.statefulSnapshot.evaluate prepared.attachment.classification model.afterDestination = .permit :=
    (installed prepared.attachment.classification model.afterDestination).symm.trans permitted
  have allowed : compiled.snapshot.permits model.afterDestination = true := by
    rw [← compiled.statefulSnapshot_permits prepared.attachment.classification model.afterDestination]
    simp [Import.NftablesStateful.Snapshot.permits, native]
  have destination : outcome.afterDestination = model.afterDestination := by
    rw [sameOutcome, sameParent]
    rfl
  have permission := compiled.permitted_valid safe model.afterDestination allowed
  rw [← destination] at permission
  exact ⟨WireNATDeployment.output_facts emission, live, permission⟩

theorem step_current_permission
    (compiled : Compile.SessionFirewall.Certified context session requirements) (safe : session.Safe context)
    (active : ReassemblyForwarding.Pipeline)
    (installed : SessionFirewallDeployment.ForwardEquivalent active.forwarding.forwarding compiled)
    (policy : IPv4Reassembly.Policy) (before : ReassemblyForwarding.State) (input : ReassemblyForwarding.Input)
    (result : ReassemblyForwarding.Result) (completed : ReassemblyForwarding.Completed)
    (accepted : ReassemblyForwarding.step active policy before input = .ok result)
    (completion : result.completed = some completed) (emission : WireForwarding.Emission completed.wire.packet)
    (forwarded : completed.outcome.output = some emission) :
    WireNATDeployment.OutputFacts completed.wire.packet emission ∧ 1 < completed.wire.packet.ip.packet.ttl.toNat ∧
      ∃ requirement ∈ requirements, requirement.test.Holds completed.outcome.afterDestination ∧
        Session.Valid context session.session requirement.scope ∧
        EAPAuth.State.Ready (EAPSession.authContext context) session.auth := by
  obtain ⟨prepared, _, _, _, _, _, computed, _, _⟩ :=
    Check.ReassemblyForwarding.step_completed active policy before input result completed accepted completion
  exact process_current_permission compiled safe active installed completed.reassembled completed.source completed.wire
    completed.same prepared completed.outcome computed emission forwarded

theorem process_output_none_of_denied
    (compiled : Compile.SessionFirewall.Certified context session requirements) (safe : session.Safe context)
    (active : ReassemblyForwarding.Pipeline)
    (installed : SessionFirewallDeployment.ForwardEquivalent active.forwarding.forwarding compiled)
    (denied : ∀ requirement ∈ requirements, session.session.permits context requirement.scope = false)
    (reassembled : IPv4Reassembly.Output) (source : ReassemblyForwarding.Source reassembled)
    (wire : WireForwarding.Input) (same : wire.packet = source.packet)
    (prepared : ConntrackLifecycle.Prepared wire.lifecycle) (outcome : ReassemblyForwarding.Outcome wire.packet)
    (accepted : ReassemblyForwarding.process active reassembled source wire same prepared = .ok outcome) : outcome.output = none := by
  cases output : outcome.output with
  | none => rfl
  | some emission =>
    obtain ⟨_, _, requirement, member, _, valid, _⟩ :=
      process_current_permission compiled safe active installed reassembled source wire same prepared outcome accepted emission output
    have allowed := (Session.permits_iff _ _ _).mpr valid
    simp [denied requirement member] at allowed

theorem postlogoff_output_none (context : Context) (before : EAPSession.State) (safe : before.Safe context)
    (compiled : Compile.SessionFirewall.Certified context (EAPSession.step context before (.authentication .logoff)) requirements)
    (active : ReassemblyForwarding.Pipeline)
    (installed : SessionFirewallDeployment.ForwardEquivalent active.forwarding.forwarding compiled)
    (reassembled : IPv4Reassembly.Output) (source : ReassemblyForwarding.Source reassembled)
    (wire : WireForwarding.Input) (same : wire.packet = source.packet)
    (prepared : ConntrackLifecycle.Prepared wire.lifecycle) (outcome : ReassemblyForwarding.Outcome wire.packet)
    (accepted : ReassemblyForwarding.process active reassembled source wire same prepared = .ok outcome) : outcome.output = none := by
  have currentSafe := EAPSession.step_safe context before (.authentication .logoff) safe
  apply process_output_none_of_denied compiled currentSafe active installed ?_ reassembled source wire same prepared outcome accepted
  intro requirement _
  exact EAPSession.unauthorized_denied context _ requirement.scope currentSafe.2.1 rfl

theorem postrevoke_output_none (context : Context) (before : EAPSession.State) (safe : before.Safe context)
    (compiled : Compile.SessionFirewall.Certified context (EAPSession.step context before (.application .revoke)) requirements)
    (active : ReassemblyForwarding.Pipeline)
    (installed : SessionFirewallDeployment.ForwardEquivalent active.forwarding.forwarding compiled)
    (reassembled : IPv4Reassembly.Output) (source : ReassemblyForwarding.Source reassembled)
    (wire : WireForwarding.Input) (same : wire.packet = source.packet)
    (prepared : ConntrackLifecycle.Prepared wire.lifecycle) (outcome : ReassemblyForwarding.Outcome wire.packet)
    (accepted : ReassemblyForwarding.process active reassembled source wire same prepared = .ok outcome) : outcome.output = none := by
  apply process_output_none_of_denied compiled (EAPSession.step_safe _ _ _ safe) active installed ?_
    reassembled source wire same prepared outcome accepted
  intro requirement _
  have missing : (EAPSession.step context before (.application .revoke)).session.credential = none := rfl
  simp [Session.permits, Session.claims, missing]

end Netlib.Examples.ReassemblyDeployment
