import Netlib.Check.CampusTCPModel

/-!
# Fixed native targets for TCP revocation

Each target keeps the source selected from its gateway table.
The checks use the actual authentication and interface state at the cut.
-/

namespace Netlib.Check.CampusTCPRevocationTargets

open Packet Protocol
open CampusTCPModel (Input State Gateway)

structure Names where
  configuration : String
  guard : String
  deriving Repr, DecidableEq

structure Raw where
  primary : Names
  standby : Names
  deriving Repr, DecidableEq

def Raw.get (raw : Raw) : Gateway → Names
  | .primary => raw.primary
  | .standby => raw.standby

def active (input : Input) (gateway : Gateway) (configuration : ConntrackLifecycle.Config) :
    SafeHandoff.Configuration :=
  ⟨configuration.id, configuration.pipeline (input.contextFor gateway).routing⟩

def current (input : Input) (cut : State input) (gateway : Gateway) : IngressAttachment.Current :=
  CampusTCPService.current (input.contextFor gateway) (CampusTCPModel.beforeService input cut gateway)

def attachments (cut : State input) (gateway : Gateway) : List IngressAttachment.ExpectedAttachment :=
  (cut.resident gateway).attachments.map (·.value)

structure Target (input : Input) (cut : State input) (gateway : Gateway) where
  names : Names
  configured : input.configured gateway = true
  configuration : ConntrackLifecycle.Config
  configurationFound : (input.contextFor gateway).configs.find? (·.id == names.configuration) = some configuration
  forward : SessionInstallation.Checked input.context.authentication input.context.requirements
    cut.authentication (active input gateway configuration)
  forwardComputed : SessionInstallation.check input.context.authentication input.context.requirements
    cut.authentication (active input gateway configuration) (input.contextFor gateway).configs 100000 = .ok forward
  forwardPassed : forward.passed = true
  guard : CampusTCPModel.Guard
  guardFound : (input.deployment gateway).guards.find? (·.id == names.guard) = some guard
  ingress : IngressGuard.Checked (current input cut gateway) (input.contextFor gateway).executionNS
    (attachments cut gateway) [] (input.contextFor gateway).application
  ingressComputed : IngressGuard.check (current input cut gateway) (input.contextFor gateway).executionNS
    (attachments cut gateway) [] (input.contextFor gateway).application guard.source 1000000 = .ok ingress
  ingressSource : ingress.source = guard.source
  ingressPassed : ingress.passed = true

structure Targets (input : Input) (cut : State input) where
  primary : Target input cut .primary
  standby : Target input cut .standby

def Targets.get (targets : Targets input cut) : (gateway : Gateway) → Target input cut gateway
  | .primary => targets.primary
  | .standby => targets.standby

def Target.ForwardInstalled (target : Target input cut gateway) (state : State input) : Prop :=
  (state.resident gateway).configuration = target.configuration

def Target.IngressInstalled (target : Target input cut gateway) (state : State input) : Prop :=
  (state.resident gateway).guard = target.guard

def Target.Installed (target : Target input cut gateway) (state : State input) : Prop :=
  target.ForwardInstalled state ∧ target.IngressInstalled state

def Target.CurrentAt (_target : Target input cut gateway) (state : State input) : Prop :=
  state.authentication = cut.authentication ∧
    (state.resident gateway).live = (cut.resident gateway).live ∧
    attachments state gateway = attachments cut gateway

def Targets.Installed (targets : Targets input cut) (state : State input) : Prop :=
  ∀ gateway, (targets.get gateway).Installed state

def Targets.CurrentAt (targets : Targets input cut) (state : State input) : Prop :=
  ∀ gateway, (targets.get gateway).CurrentAt state

private def witnessed (value : Except String α) : Except String { result : α // value = .ok result } :=
  match value with
  | .error reason => .error reason
  | .ok result => .ok ⟨result, rfl⟩

private theorem ingress_source (value : IngressGuard.Checked now executionNS expected maintenance application)
    (computed : IngressGuard.check now executionNS expected maintenance application source budget = .ok value) :
    value.source = source := by
  unfold IngressGuard.check at computed
  repeat' first
    | (cases computed; rfl)
    | (split at computed <;> try simp [bind, Except.bind, pure, throw] at computed)

def Target.check (input : Input) (cut : State input) (gateway : Gateway) (names : Names) :
    Except String (Target input cut gateway) := do
  if configured : input.configured gateway = true then
    match configurationFound : (input.contextFor gateway).configs.find? (·.id == names.configuration) with
    | none => throw "The fixed TCP configuration target is unknown."
    | some configuration =>
      let forward ← witnessed (SessionInstallation.check input.context.authentication input.context.requirements
        cut.authentication (active input gateway configuration) (input.contextFor gateway).configs 100000)
      if forwardPassed : forward.val.passed = true then
        match guardFound : (input.deployment gateway).guards.find? (·.id == names.guard) with
        | none => throw "The fixed TCP ingress target is unknown."
        | some guard =>
          let ingress ← witnessed (IngressGuard.check (current input cut gateway) (input.contextFor gateway).executionNS
            (attachments cut gateway) [] (input.contextFor gateway).application guard.source 1000000)
          if ingressPassed : ingress.val.passed = true then
            return ⟨names, configured, configuration, configurationFound, forward.val, forward.property,
              forwardPassed, guard, guardFound, ingress.val, ingress.property,
              ingress_source ingress.val ingress.property, ingressPassed⟩
          else throw "The fixed TCP ingress target differs from the current attachment policy."
      else throw "The fixed TCP configuration target differs from the current session policy."
  else throw "The fixed TCP target gateway has no deployment."

def Targets.check (input : Input) (cut : State input) (raw : Raw) : Except String (Targets input cut) := do
  let primary ← Target.check input cut .primary raw.primary
  let standby ← Target.check input cut .standby raw.standby
  return ⟨primary, standby⟩

def revoked (input : Input) (after : Nat) : Bool :=
  !(SessionInstallation.current input.context.authentication after).auth.authorized ||
    (SessionInstallation.current input.context.authentication after).session.credential.isNone

theorem revoked_correct (input : Input) (after : Nat) :
    revoked input after = true ↔
      (SessionInstallation.current input.context.authentication after).auth.authorized = false ∨
      (SessionInstallation.current input.context.authentication after).session.credential = none := by
  simp [revoked]

theorem revoked_denied (input : Input) (after : Nat) (closed : revoked input after = true) :
    ∀ scope, (SessionInstallation.current input.context.authentication after).session.permits
      input.context.authentication.context scope = false := by
  have safe := Check.SessionFirewall.stateAt_safe input.context.authentication after
  rcases (revoked_correct input after).mp closed with unauthorized | missing
  · intro scope
    exact EAPSession.unauthorized_denied input.context.authentication.context _ scope safe.2.1 unauthorized
  · intro scope
    simp [Session.permits, Session.claims, missing]

end Netlib.Check.CampusTCPRevocationTargets
