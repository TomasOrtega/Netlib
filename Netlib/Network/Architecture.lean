import Netlib.Network.Basic

namespace Netlib

universe u v w

/-- A physical architecture simulates each step by an abstract path. -/
structure Refinement {Physical : Type u} {Abstract : Type v}
    (physical : Network Physical) (abstract : Network Abstract) where
  project : Physical → Abstract
  simulate : ∀ a b, physical.link a b →
    Network.Reachable abstract (project a) (project b)

namespace Refinement

variable {Physical : Type u} {Abstract : Type v} {Higher : Type w}
variable {physical : Network Physical} {abstract : Network Abstract} {higher : Network Higher}

/-- Identity refinement records that the model itself is an architecture. -/
def identity (net : Network Physical) : Refinement net net where
  project := id
  simulate _ _ edge := .single edge

/-- Refinements connect several abstraction levels. -/
def comp (lower : Refinement physical abstract) (upper : Refinement abstract higher) :
    Refinement physical higher where
  project := upper.project ∘ lower.project
  simulate _ _ edge := (lower.simulate _ _ edge).map upper.project upper.simulate

theorem reachable (refinement : Refinement physical abstract) {a b : Physical}
    (path : Network.Reachable physical a b) :
    Network.Reachable abstract (refinement.project a) (refinement.project b) :=
  path.map refinement.project refinement.simulate

/-- Abstract segmentation protects all physical replicas of the designated zones. -/
theorem isolated (refinement : Refinement physical abstract)
    {sources targets : Abstract → Prop}
    (secure : abstract.Isolated sources targets) :
    physical.Isolated (sources ∘ refinement.project) (targets ∘ refinement.project) := by
  intro a b source target path
  exact secure _ _ source target (refinement.reachable path)

end Refinement

/-- Cluster-internal links may collapse to a single abstract node. -/
structure StutteringRefinement {Physical : Type u} {Abstract : Type v}
    (physical : Network Physical) (abstract : Network Abstract) where
  project : Physical → Abstract
  simulate : ∀ a b, physical.link a b →
    project a = project b ∨ abstract.link (project a) (project b)

namespace StutteringRefinement

variable {Physical : Type u} {Abstract : Type v} {Higher : Type w}
variable {physical : Network Physical} {abstract : Network Abstract} {higher : Network Higher}

def toRefinement (refinement : StutteringRefinement physical abstract) :
    Refinement physical abstract where
  project := refinement.project
  simulate a b edge := by
    rcases refinement.simulate a b edge with same | step
    · rw [same]
      exact .refl _
    · exact .single step

def comp (lower : StutteringRefinement physical abstract)
    (upper : StutteringRefinement abstract higher) : StutteringRefinement physical higher where
  project := upper.project ∘ lower.project
  simulate a b edge := by
    rcases lower.simulate a b edge with same | step
    · exact .inl (congrArg upper.project same)
    · exact upper.simulate _ _ step

/-- A bypass projection must not add an abstract gateway. -/
def without (refinement : StutteringRefinement physical abstract) (gateways : Abstract → Prop) :
    StutteringRefinement (physical.without (gateways ∘ refinement.project))
      (abstract.without gateways) where
  project := refinement.project
  simulate a b edge := by
    rcases refinement.simulate a b edge.1 with same | step
    · exact .inl same
    · exact .inr ⟨step, edge.2⟩

/-- Gateway replicas preserve mediation when each replica has the same abstract role. -/
theorem mediated (refinement : StutteringRefinement physical abstract)
    {sources targets gateways : Abstract → Prop}
    (secure : abstract.Mediated sources targets gateways) :
    physical.Mediated (sources ∘ refinement.project) (targets ∘ refinement.project)
      (gateways ∘ refinement.project) := by
  intro a b source target bypass
  apply secure _ _ source target
  exact ⟨bypass.1, bypass.2.1,
    (refinement.without gateways).toRefinement.reachable bypass.2.2⟩

/-- A disabled subset of physical links remains a valid refinement. -/
def restrict (refinement : StutteringRefinement physical abstract)
    (allowed : Physical → Physical → Prop) :
    StutteringRefinement (physical.restrict allowed) abstract where
  project := refinement.project
  simulate a b edge := refinement.simulate a b edge.1

/-- Link removal during failover preserves gateway mediation. -/
theorem mediated_during_failover (refinement : StutteringRefinement physical abstract)
    {sources targets gateways : Abstract → Prop}
    (secure : abstract.Mediated sources targets gateways)
    (activeLink : Physical → Physical → Prop) :
    (physical.restrict activeLink).Mediated (sources ∘ refinement.project)
      (targets ∘ refinement.project) (gateways ∘ refinement.project) :=
  (refinement.restrict activeLink).mediated secure

end StutteringRefinement

namespace Network

variable {Node : Type u} {net : Network Node} {sources targets : Node → Prop}

/-- Availability requires a permitted path for every designated endpoint pair. -/
def Available (net : Network Node) (sources targets : Node → Prop) : Prop :=
  ∀ a b, sources a → targets b → net.Reachable a b

/-- Extra paths preserve availability. Link removal needs a separate proof. -/
theorem available_mono {larger : Network Node} (available : net.Available sources targets)
    (subset : ∀ a b, net.link a b → larger.link a b) :
    larger.Available sources targets := by
  intro a b source target
  exact (available a b source target).mono subset

/-- A retained forwarding subnet is an explicit availability certificate for failover. -/
theorem available_after_failover {retained failed : Network Node}
    (certificate : retained.Available sources targets)
    (retainedPresent : ∀ a b, retained.link a b → failed.link a b) :
    failed.Available sources targets :=
  available_mono certificate retainedPresent

end Network
end Netlib
