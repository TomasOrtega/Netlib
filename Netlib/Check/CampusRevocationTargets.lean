import Netlib.Check.CampusRevocationModel
import Netlib.Examples.SessionRevocationWire

/-!
# Fixed checked targets for session revocation

Each target retains the native policy check at one authentication prefix.
Configuration comparison covers every stored pipeline field.
-/

namespace Netlib.Check.CampusRevocationTargets

open Packet Protocol
open StatefulFailover (Gateway)

abbrev Input := CampusRevocationModel.Input

def sameConfiguration (first second : Protocol.SafeHandoff.Configuration) : Bool :=
  decide (first.id = second.id ∧
    first.pipeline.routes = second.pipeline.routes ∧
    first.pipeline.forward = second.pipeline.forward ∧
    first.pipeline.forwardDefault = second.pipeline.forwardDefault ∧
    first.pipeline.late = second.pipeline.late ∧
    first.pipeline.lateDefault = second.pipeline.lateDefault)

theorem sameConfiguration_correct (first second : Protocol.SafeHandoff.Configuration) :
    sameConfiguration first second = true ↔ first = second := by
  rcases first with ⟨firstId, ⟨firstRoutes, firstForward, firstDefault, firstLate, firstLateDefault⟩⟩
  rcases second with ⟨secondId, ⟨secondRoutes, secondForward, secondDefault, secondLate, secondLateDefault⟩⟩
  simp [sameConfiguration]

@[simp] theorem sameConfiguration_self (configuration : Protocol.SafeHandoff.Configuration) :
    sameConfiguration configuration configuration = true :=
  (sameConfiguration_correct configuration configuration).mpr rfl

structure Target (input : Input) (after : Nat) where
  configuration : Protocol.SafeHandoff.Configuration
  checked : SessionInstallation.Checked input.authentication input.requirements after configuration
  passed : checked.passed = true

structure Targets (input : Input) (after : Nat) where
  primary : Target input after
  standby : Target input after

def Targets.get (targets : Targets input after) : Gateway → Protocol.SafeHandoff.Configuration
  | .primary => targets.primary.configuration
  | .standby => targets.standby.configuration

def Targets.checked (targets : Targets input after) (gateway : Gateway) :
    SessionInstallation.Checked input.authentication input.requirements after (targets.get gateway) :=
  match gateway with
  | .primary => targets.primary.checked
  | .standby => targets.standby.checked

theorem Targets.passed (targets : Targets input after) (gateway : Gateway) :
    (targets.checked gateway).passed = true := by
  cases gateway
  · exact targets.primary.passed
  · exact targets.standby.passed

theorem Targets.forward_equivalent (targets : Targets input after) (gateway : Gateway) :
    Examples.SessionFirewallDeployment.ForwardEquivalent (targets.get gateway).pipeline
      (targets.checked gateway).compiled :=
  (targets.checked gateway).forward_equivalent (targets.passed gateway)

def Target.check (input : Input) (after : Nat) (gateway : Gateway)
    (sourceConfig : Check.ConntrackLifecycle.Config) (budget : Nat := 100000) :
    Except String (Target input after) := do
  let configuration := Check.SafeHandoff.configuration input.handoff.routing gateway sourceConfig
  let checked ← SessionInstallation.check input.authentication input.requirements after configuration
    input.handoff.configs budget
  if passed : checked.passed = true then
    return ⟨configuration, checked, passed⟩
  else throw "The revocation target differs from the policy at the selected authentication prefix."

def Targets.check (input : Input) (after : Nat)
    (primarySource standbySource : Check.ConntrackLifecycle.Config) (budget : Nat := 100000) :
    Except String (Targets input after) := do
  let primary ← Target.check input after .primary primarySource budget
  let standby ← Target.check input after .standby standbySource budget
  return ⟨primary, standby⟩

def revoked (input : Input) (after : Nat) : Bool :=
  !(SessionInstallation.current input.authentication after).auth.authorized ||
    (SessionInstallation.current input.authentication after).session.credential.isNone

theorem revoked_correct (input : Input) (after : Nat) :
    revoked input after = true ↔
      (SessionInstallation.current input.authentication after).auth.authorized = false ∨
      (SessionInstallation.current input.authentication after).session.credential = none := by
  simp [revoked]

theorem revoked_denied (input : Input) (after : Nat) (closed : revoked input after = true) :
    ∀ requirement ∈ input.requirements,
      (SessionInstallation.current input.authentication after).session.permits
        input.authentication.context requirement.scope = false := by
  have safe := Check.SessionFirewall.stateAt_safe input.authentication after
  rcases (revoked_correct input after).mp closed with unauthorized | missing
  · intro requirement _
    exact EAPSession.unauthorized_denied input.authentication.context _ requirement.scope safe.2.1 unauthorized
  · intro requirement _
    simp [Session.permits, Session.claims, missing]

theorem Target.wire_output_none (target : Target input after) (closed : revoked input after = true)
    (tracker : ConntrackLifecycle.State) (packet : Protocol.WireForwarding.Input)
    (outcome : Protocol.WireForwarding.Outcome packet.packet)
    (accepted : Protocol.WireForwarding.step target.configuration.pipeline tracker packet = .ok outcome) :
    outcome.output = none :=
  Examples.SessionRevocationWire.wire_output_none_of_denied target.checked.compiled
    target.configuration.pipeline (target.checked.forward_equivalent target.passed)
    (revoked_denied input after closed) tracker packet outcome accepted

theorem Targets.wire_output_none (targets : Targets input after) (closed : revoked input after = true)
    (gateway : Gateway) (tracker : ConntrackLifecycle.State) (packet : Protocol.WireForwarding.Input)
    (outcome : Protocol.WireForwarding.Outcome packet.packet)
    (accepted : Protocol.WireForwarding.step (targets.get gateway).pipeline tracker packet = .ok outcome) :
    outcome.output = none :=
  Examples.SessionRevocationWire.wire_output_none_of_denied (targets.checked gateway).compiled
    (targets.get gateway).pipeline (targets.forward_equivalent gateway)
    (revoked_denied input after closed) tracker packet outcome accepted

end Netlib.Check.CampusRevocationTargets
