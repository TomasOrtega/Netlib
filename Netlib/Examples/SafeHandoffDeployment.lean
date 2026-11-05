import Netlib.Protocol.SafeHandoffFacts
import Netlib.Examples.WireNATDeployment

/-!
# Outstanding route assignments and current session permission

Tickets retain their route assignment and bytes, without retaining admission-time permission.
The current assigned-gateway pipeline must match the current certified session policy.
-/

namespace Netlib.Examples.SafeHandoffDeployment

open Packet Protocol

variable {context : Context} {session : EAPSession.State} {requirements : List Compile.SessionFirewall.Intent}

theorem serve_current_permission
    (compiled : Compile.SessionFirewall.Certified context session requirements) (safe : session.Safe context)
    (before : SafeHandoff.State) (id : Nat) (result : SafeHandoff.Result) (served : SafeHandoff.PacketResult)
    (accepted : SafeHandoff.step before (.serve id) = .ok result) (stored : result.served = some served)
    (installed : SessionFirewallDeployment.ForwardEquivalent (before.configurations served.ticket.value.gateway).pipeline compiled)
    (emission : WireForwarding.Emission served.ticket.value.source.packet) (forwarded : served.outcome.output = some emission) :
    WireNATDeployment.OutputFacts served.ticket.value.source.packet emission ∧
      1 < served.ticket.value.source.packet.ip.packet.ttl.toNat ∧
      ∃ requirement ∈ requirements, requirement.test.Holds served.outcome.afterDestination ∧
        Session.Valid context session.session requirement.scope ∧
        EAPAuth.State.Ready (EAPSession.authContext context) session.auth := by
  obtain ⟨_, raw, computed, same⟩ := SafeHandoff.step_core before (.serve id) result accepted
  have rawStored : raw.served = some served := by rw [← same]; exact stored
  obtain ⟨completed, outcome, _, found, _, _, _, wireStep, _⟩ := SafeHandoff.core_serve_facts before id raw computed
  have equal : (⟨completed.item, before.configurations completed.item.value.gateway, outcome⟩ : SafeHandoff.PacketResult) = served :=
    Option.some.inj (found.symm.trans rawStored)
  subst served
  obtain ⟨model, processed, output, destination, _, _, live⟩ :=
    WireForwarding.step_output _ _ _ _ wireStep emission forwarded
  have permission := SessionFirewallDeployment.output_current_permission compiled safe _ installed _
    (TrackedFlow.wireInput completed.item.value.entry completed.item.value.direction completed.item.value.source.packet).lifecycle
    model emission.target processed output
  rw [← destination] at permission
  exact ⟨WireNATDeployment.output_facts emission, live, permission⟩

theorem serve_output_none_of_denied
    (compiled : Compile.SessionFirewall.Certified context session requirements) (safe : session.Safe context)
    (denied : ∀ requirement ∈ requirements, session.session.permits context requirement.scope = false)
    (before : SafeHandoff.State) (id : Nat) (result : SafeHandoff.Result) (served : SafeHandoff.PacketResult)
    (accepted : SafeHandoff.step before (.serve id) = .ok result) (stored : result.served = some served)
    (installed : SessionFirewallDeployment.ForwardEquivalent (before.configurations served.ticket.value.gateway).pipeline compiled) :
    served.outcome.output = none := by
  cases output : served.outcome.output with
  | none => rfl
  | some emission =>
    obtain ⟨_, _, requirement, member, _, valid, _⟩ :=
      serve_current_permission compiled safe before id result served accepted stored installed emission output
    have allowed := (Session.permits_iff _ _ _).mpr valid
    simp [denied requirement member] at allowed

theorem postlogoff_output_none (context : Context) (session : EAPSession.State) (safe : session.Safe context)
    (compiled : Compile.SessionFirewall.Certified context (EAPSession.step context session (.authentication .logoff)) requirements)
    (before : SafeHandoff.State) (id : Nat) (result : SafeHandoff.Result) (served : SafeHandoff.PacketResult)
    (accepted : SafeHandoff.step before (.serve id) = .ok result) (stored : result.served = some served)
    (installed : SessionFirewallDeployment.ForwardEquivalent (before.configurations served.ticket.value.gateway).pipeline compiled) :
    served.outcome.output = none := by
  have current := EAPSession.step_safe context session (.authentication .logoff) safe
  apply serve_output_none_of_denied compiled current ?_ before id result served accepted stored installed
  intro requirement _
  exact EAPSession.unauthorized_denied context _ requirement.scope current.2.1 rfl

theorem postrevoke_output_none (context : Context) (session : EAPSession.State) (safe : session.Safe context)
    (compiled : Compile.SessionFirewall.Certified context (EAPSession.step context session (.application .revoke)) requirements)
    (before : SafeHandoff.State) (id : Nat) (result : SafeHandoff.Result) (served : SafeHandoff.PacketResult)
    (accepted : SafeHandoff.step before (.serve id) = .ok result) (stored : result.served = some served)
    (installed : SessionFirewallDeployment.ForwardEquivalent (before.configurations served.ticket.value.gateway).pipeline compiled) :
    served.outcome.output = none := by
  apply serve_output_none_of_denied compiled (EAPSession.step_safe _ _ _ safe) ?_
    before id result served accepted stored installed
  intro requirement _
  have missing : (EAPSession.step context session (.application .revoke)).session.credential = none := rfl
  simp [Session.permits, Session.claims, missing]

end Netlib.Examples.SafeHandoffDeployment
