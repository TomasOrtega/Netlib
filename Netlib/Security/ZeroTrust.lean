import Netlib.Network.Basic

/-!
# Request enforcement

A request names a principal, a resource, and an operation.
The policy supplies identity and permission checks.
A policy enforcement point checks links that enter or leave its gateway set.
These definitions assume that the supplied identity checks are correct.
They do not model cryptography or device behavior.
-/

namespace Netlib.ZeroTrust

/-- A principal asks to perform an operation on a resource. -/
structure Request (Principal : Type u) (Resource : Type v) (Operation : Type w) where
  principal : Principal
  resource : Resource
  operation : Operation
  deriving Repr, BEq, DecidableEq

/-- Identity and permission checks are explicit inputs to the model. -/
structure Policy (Principal : Type u) (Resource : Type v) (Operation : Type w) where
  authenticated : Principal → Bool
  authorized : Request Principal Resource Operation → Bool

namespace Policy

/-- Both checks must pass before the policy permits a request. -/
def allows (policy : Policy Principal Resource Operation)
    (request : Request Principal Resource Operation) : Bool :=
  policy.authenticated request.principal && policy.authorized request

/-- An admitted request passes the identity and permission checks. -/
def Admitted (policy : Policy Principal Resource Operation)
    (request : Request Principal Resource Operation) : Prop :=
  policy.authenticated request.principal = true ∧ policy.authorized request = true

@[simp] theorem allows_iff (policy : Policy Principal Resource Operation)
    (request : Request Principal Resource Operation) :
    policy.allows request = true ↔ policy.Admitted request := by
  simp [allows, Admitted]

theorem denied_of_unauthenticated (policy : Policy Principal Resource Operation)
    (request : Request Principal Resource Operation)
    (failed : policy.authenticated request.principal = false) :
    policy.allows request = false := by simp [allows, failed]

theorem denied_of_unauthorized (policy : Policy Principal Resource Operation)
    (request : Request Principal Resource Operation) (failed : policy.authorized request = false) :
    policy.allows request = false := by simp [allows, failed]

/-- A stronger policy permits no extra requests. -/
def Refines (stronger weaker : Policy Principal Resource Operation) : Prop :=
  ∀ request, stronger.allows request = true → weaker.allows request = true

theorem refines_refl (policy : Policy Principal Resource Operation) : policy.Refines policy :=
  fun _ => id

theorem Refines.trans {a b c : Policy Principal Resource Operation}
    (ab : a.Refines b) (bc : b.Refines c) : a.Refines c :=
  fun request accepted => bc request (ab request accepted)

end Policy

/-- A denied request cannot enter or leave an enforcement gateway. -/
def enforce (net : Network Node) (gateways : Node → Prop)
    (policy : Policy Principal Resource Operation) (request : Request Principal Resource Operation) :
    Network Node :=
  net.restrict fun source target =>
    (gateways source ∨ gateways target) → policy.allows request = true

/-- An admitted request keeps every base forwarding step. -/
theorem allowed_network_eq (net : Network Node) (gateways : Node → Prop)
    (policy : Policy Principal Resource Operation) (request : Request Principal Resource Operation)
    (allowed : policy.allows request = true) : enforce net gateways policy request = net := by
  cases net with
  | mk link =>
    unfold enforce Network.restrict
    congr 1
    funext source target
    apply propext
    simp [allowed]

/-- Denial removes exactly the links incident to the gateway set. -/
theorem denied_network_eq_without (net : Network Node) (gateways : Node → Prop)
    (policy : Policy Principal Resource Operation) (request : Request Principal Resource Operation)
    (denied : policy.allows request = false) :
    enforce net gateways policy request = net.without gateways := by
  unfold enforce Network.without Network.restrict
  congr 1
  funext source target
  apply propext
  simp [denied]

/-- Enforcement cannot add a path to the base network. -/
theorem reachable_original {net : Network Node} {gateways : Node → Prop}
    {policy : Policy Principal Resource Operation} {request : Request Principal Resource Operation}
    {source target : Node} (path : (enforce net gateways policy request).Reachable source target) :
    net.Reachable source target := Network.reachable_restrict _ path

/-- An admitted request has exactly the base network paths. -/
theorem admitted_reachable_iff (net : Network Node) (gateways : Node → Prop)
    (policy : Policy Principal Resource Operation) (request : Request Principal Resource Operation)
    (admitted : policy.Admitted request) (source target : Node) :
    (enforce net gateways policy request).Reachable source target ↔ net.Reachable source target := by
  rw [allowed_network_eq net gateways policy request ((Policy.allows_iff _ _).mpr admitted)]

/-- Mediation and denial isolate endpoints outside the gateway set. -/
theorem denied_isolated {net : Network Node} {sources targets gateways : Node → Prop}
    (mediated : net.Mediated sources targets gateways)
    (sourceOutside : ∀ source, sources source → ¬gateways source)
    (targetOutside : ∀ target, targets target → ¬gateways target)
    (policy : Policy Principal Resource Operation) (request : Request Principal Resource Operation)
    (denied : policy.allows request = false) :
    (enforce net gateways policy request).Isolated sources targets := by
  rw [denied_network_eq_without net gateways policy request denied]
  exact Network.isolated_without_of_mediated mediated sourceOutside targetOutside

/-- Identity failure blocks a request when every path uses an enforcement gateway. -/
theorem unauthenticated_isolated {net : Network Node} {sources targets gateways : Node → Prop}
    (mediated : net.Mediated sources targets gateways)
    (sourceOutside : ∀ source, sources source → ¬gateways source)
    (targetOutside : ∀ target, targets target → ¬gateways target)
    (policy : Policy Principal Resource Operation) (request : Request Principal Resource Operation)
    (failed : policy.authenticated request.principal = false) :
    (enforce net gateways policy request).Isolated sources targets :=
  denied_isolated mediated sourceOutside targetOutside policy request
    (policy.denied_of_unauthenticated request failed)

/-- Permission failure blocks a request under the same gateway assumptions. -/
theorem unauthorized_isolated {net : Network Node} {sources targets gateways : Node → Prop}
    (mediated : net.Mediated sources targets gateways)
    (sourceOutside : ∀ source, sources source → ¬gateways source)
    (targetOutside : ∀ target, targets target → ¬gateways target)
    (policy : Policy Principal Resource Operation) (request : Request Principal Resource Operation)
    (failed : policy.authorized request = false) :
    (enforce net gateways policy request).Isolated sources targets :=
  denied_isolated mediated sourceOutside targetOutside policy request
    (policy.denied_of_unauthorized request failed)

/-- A bypass path survives denial at every gateway. -/
theorem bypass_survives_denial {net : Network Node} {gateways : Node → Prop}
    {source target : Node} (bypass : net.Bypass gateways source target)
    (policy : Policy Principal Resource Operation) (request : Request Principal Resource Operation)
    (denied : policy.allows request = false) :
    (enforce net gateways policy request).Reachable source target := by
  rw [denied_network_eq_without net gateways policy request denied]
  exact bypass.2.2

/-- Denial isolates outside endpoints exactly when the gateways mediate their paths. -/
theorem denied_isolated_iff_mediated (net : Network Node) (sources targets gateways : Node → Prop)
    (sourceOutside : ∀ source, sources source → ¬gateways source)
    (targetOutside : ∀ target, targets target → ¬gateways target)
    (policy : Policy Principal Resource Operation) (request : Request Principal Resource Operation)
    (denied : policy.allows request = false) :
    (enforce net gateways policy request).Isolated sources targets ↔
      net.Mediated sources targets gateways := by
  constructor
  · intro isolated source target isSource isTarget bypass
    exact isolated source target isSource isTarget (bypass_survives_denial bypass policy request denied)
  · intro mediated
    exact denied_isolated mediated sourceOutside targetOutside policy request denied

/-- A stronger policy cannot add request paths. -/
theorem reachable_of_refines {net : Network Node} {gateways : Node → Prop}
    {stronger weaker : Policy Principal Resource Operation} (refines : stronger.Refines weaker)
    (request : Request Principal Resource Operation) {source target : Node}
    (path : (enforce net gateways stronger request).Reachable source target) :
    (enforce net gateways weaker request).Reachable source target :=
  Network.Reachable.mono (net := enforce net gateways stronger request)
    (net' := enforce net gateways weaker request)
    (fun _ _ edge => ⟨edge.1, fun incident => refines request (edge.2 incident)⟩) path

/-- A stronger policy preserves request isolation. -/
theorem isolation_of_refines {net : Network Node} {gateways sources targets : Node → Prop}
    {stronger weaker : Policy Principal Resource Operation} (refines : stronger.Refines weaker)
    (request : Request Principal Resource Operation)
    (isolated : (enforce net gateways weaker request).Isolated sources targets) :
    (enforce net gateways stronger request).Isolated sources targets := by
  intro source target isSource isTarget path
  exact isolated source target isSource isTarget (reachable_of_refines refines request path)

end Netlib.ZeroTrust
