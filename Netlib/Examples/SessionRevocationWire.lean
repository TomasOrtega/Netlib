import Netlib.Examples.SessionFirewallDeployment
import Netlib.Protocol.WireForwarding

/-!
# Current session denial at wire forwarding

The actual wire step uses the installed forward policy.
Cached and fresh attachments obey the same compiled denial.
-/

namespace Netlib.Examples.SessionRevocationWire

open Packet Protocol
open SessionFirewallDeployment

variable {context : Context} {session : EAPSession.State}
  {requirements : List Compile.SessionFirewall.Intent}

theorem wire_output_none_of_denied
    (compiled : Compile.SessionFirewall.Certified context session requirements)
    (active : ConntrackLifecycle.Pipeline) (installed : ForwardEquivalent active compiled)
    (denied : ∀ requirement ∈ requirements,
      session.session.permits context requirement.scope = false)
    (tracker : ConntrackLifecycle.State) (input : WireForwarding.Input)
    (outcome : WireForwarding.Outcome input.packet)
    (accepted : WireForwarding.step active tracker input = .ok outcome) :
    outcome.output = none := by
  cases output : outcome.output with
  | none => rfl
  | some emission =>
    obtain ⟨model, processed, emitted, _⟩ :=
      WireForwarding.step_output active tracker input outcome accepted emission output
    have permitted := output_compiled_permit compiled active installed tracker
      input.lifecycle model emission.target processed emitted
    obtain ⟨requirement, member, allowed, _⟩ :=
      (compiled.permits_iff model.afterDestination).mp permitted
    simp [denied requirement member] at allowed

theorem wire_output_none_of_unauthorized
    (compiled : Compile.SessionFirewall.Certified context session requirements)
    (active : ConntrackLifecycle.Pipeline) (installed : ForwardEquivalent active compiled)
    (coupled : session.Coupled) (unauthorized : session.auth.authorized = false)
    (tracker : ConntrackLifecycle.State) (input : WireForwarding.Input)
    (outcome : WireForwarding.Outcome input.packet)
    (accepted : WireForwarding.step active tracker input = .ok outcome) :
    outcome.output = none :=
  wire_output_none_of_denied compiled active installed
    (fun requirement _ =>
      EAPSession.unauthorized_denied context session requirement.scope coupled unauthorized)
    tracker input outcome accepted

theorem wire_output_none_without_credential
    (compiled : Compile.SessionFirewall.Certified context session requirements)
    (active : ConntrackLifecycle.Pipeline) (installed : ForwardEquivalent active compiled)
    (missing : session.session.credential = none)
    (tracker : ConntrackLifecycle.State) (input : WireForwarding.Input)
    (outcome : WireForwarding.Outcome input.packet)
    (accepted : WireForwarding.step active tracker input = .ok outcome) :
    outcome.output = none := by
  apply wire_output_none_of_denied compiled active installed _ tracker input outcome accepted
  intro requirement _
  simp [Session.permits, Session.claims, missing]

end Netlib.Examples.SessionRevocationWire
