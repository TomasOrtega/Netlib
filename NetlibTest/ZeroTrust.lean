import Netlib.Security.ZeroTrust

namespace NetlibTest.ZeroTrust

open Netlib Netlib.ZeroTrust

private inductive Operation
  | read | write
  deriving DecidableEq, BEq

private def policy : Policy Bool Nat Operation where
  authenticated principal := principal
  authorized request := request.resource == 7 && request.operation == .read

private def accepted : Request Bool Nat Operation := ⟨true, 7, .read⟩
private def unauthorized : Request Bool Nat Operation := ⟨true, 7, .write⟩
private def unauthenticated : Request Bool Nat Operation := ⟨false, 7, .read⟩
private def otherResource : Request Bool Nat Operation := ⟨true, 8, .read⟩

example : policy.allows accepted = true := by decide
example : policy.allows unauthorized = false := by decide
example : policy.allows unauthenticated = false := by decide
example : policy.allows otherResource = false := by decide
example : policy.Admitted accepted := (Policy.allows_iff _ _).mp (by decide)
example : policy.authorized unauthenticated = true := by decide
example : policy.authenticated unauthorized.principal = true := by decide

private inductive Node
  | client | pep | server
  deriving DecidableEq

private def chain : Network Node where
  link source target :=
    (source = .client ∧ target = .pep) ∨ (source = .pep ∧ target = .server)

private def sources : Node → Prop := (· = .client)
private def targets : Node → Prop := (· = .server)
private def gateways : Node → Prop := (· = .pep)

private theorem sourceOutside (node : Node) (source : sources node) : ¬gateways node := by
  subst node
  intro impossible
  cases impossible

private theorem targetOutside (node : Node) (target : targets node) : ¬gateways node := by
  subst node
  intro impossible
  cases impossible

private theorem chainMediated : chain.Mediated sources targets gateways := by
  apply Network.mediated_of_cut sources
  · intro source target link _ targetOutside inside
    subst source
    have isGateway : target = .pep := by simpa [chain] using link
    exact False.elim (targetOutside isGateway)
  · exact fun _ h => h
  · intro target isTarget isSource
    subst target
    cases isSource

private theorem chainAvailable : chain.Reachable .client .server :=
  .step (.inl ⟨rfl, rfl⟩) (.single (.inr ⟨rfl, rfl⟩))

example : enforce chain gateways policy accepted = chain :=
  allowed_network_eq chain gateways policy accepted (by decide)

example : (enforce chain gateways policy accepted).Reachable .client .server :=
  (admitted_reachable_iff chain gateways policy accepted
    ((Policy.allows_iff _ _).mp (by decide)) _ _).mpr chainAvailable

example : (enforce chain gateways policy unauthorized).Isolated sources targets :=
  unauthorized_isolated chainMediated sourceOutside targetOutside policy unauthorized (by decide)

example : (enforce chain gateways policy unauthenticated).Isolated sources targets :=
  unauthenticated_isolated chainMediated sourceOutside targetOutside policy unauthenticated (by decide)

example : (enforce chain gateways policy otherResource).Isolated sources targets :=
  denied_isolated chainMediated sourceOutside targetOutside policy otherResource (by decide)

example : enforce chain gateways policy unauthorized = chain.without gateways :=
  denied_network_eq_without chain gateways policy unauthorized (by decide)

private def bypassNet : Network Node where
  link source target := chain.link source target ∨ (source = .client ∧ target = .server)

private theorem directBypass : bypassNet.Bypass gateways .client .server := by
  refine ⟨sourceOutside .client rfl, targetOutside .server rfl, .single ?_⟩
  exact ⟨.inr ⟨rfl, rfl⟩, sourceOutside .client rfl, targetOutside .server rfl⟩

example : (enforce bypassNet gateways policy unauthorized).Reachable .client .server :=
  bypass_survives_denial directBypass policy unauthorized (by decide)

example : ¬(enforce bypassNet gateways policy unauthorized).Isolated sources targets := by
  intro isolated
  exact isolated .client .server rfl rfl
    (bypass_survives_denial directBypass policy unauthorized (by decide))

example : ¬bypassNet.Mediated sources targets gateways := by
  intro mediated
  exact mediated .client .server rfl rfl directBypass

example : (enforce chain gateways policy unauthorized).Isolated sources targets ↔
    chain.Mediated sources targets gateways :=
  denied_isolated_iff_mediated chain sources targets gateways sourceOutside targetOutside
    policy unauthorized (by decide)

example : (enforce chain gateways policy unauthorized).Reachable .pep .pep := .refl _

example : ¬(enforce chain gateways policy unauthorized).Isolated gateways gateways := by
  intro isolated
  exact isolated .pep .pep rfl rfl (.refl _)

private def denyAll : Policy Bool Nat Operation where
  authenticated _ := false
  authorized _ := false

private theorem denyAllRefines : denyAll.Refines policy := by
  intro request impossible
  simp [Policy.allows, denyAll] at impossible

example : (enforce chain gateways denyAll accepted).Isolated sources targets := by
  apply denied_isolated chainMediated sourceOutside targetOutside
  rfl

example : (enforce chain gateways denyAll unauthorized).Isolated sources targets :=
  isolation_of_refines denyAllRefines unauthorized
    (unauthorized_isolated chainMediated sourceOutside targetOutside policy unauthorized (by decide))

end NetlibTest.ZeroTrust
