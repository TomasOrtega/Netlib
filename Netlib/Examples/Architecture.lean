import Netlib.Network.Architecture

namespace Netlib.Examples

/-- A reference pattern with mandatory policy enforcement. -/
inductive ReferenceNode
  | client | gateway | server
  deriving DecidableEq

open ReferenceNode in
def reference : Netlib.Network ReferenceNode where
  link a b := (a = client ∧ b = gateway) ∨ (a = gateway ∧ b = server)

theorem reference_mediated : reference.Mediated (· = .client) (· = .server) (· = .gateway) := by
  apply Netlib.Network.mediated_of_cut (· = .client)
  · intro a b edge outsideA outsideB inside
    subst a
    simp [reference] at edge
    exact False.elim (outsideB edge)
  · exact fun _ h => h
  · intro b target inside
    subst b
    cases inside

/-- The physical gateway is a pair of interchangeable replicas. -/
inductive PhysicalNode
  | client | primary | standby | server
  deriving DecidableEq

open PhysicalNode in
def physical : Netlib.Network PhysicalNode where
  link a b :=
    (a = client ∧ (b = primary ∨ b = standby)) ∨
    ((a = primary ∨ a = standby) ∧ b = server) ∨
    (a = primary ∧ b = standby) ∨ (a = standby ∧ b = primary)

def role : PhysicalNode → ReferenceNode
  | .client => .client
  | .primary | .standby => .gateway
  | .server => .server

def clusterRefinement : Netlib.StutteringRefinement physical reference where
  project := role
  simulate a b edge := by
    cases a <;> cases b <;> simp_all [physical, reference, role]

/-- Every physical path passes through at least one gateway replica. -/
theorem cluster_mediated : physical.Mediated (fun n => role n = .client)
    (fun n => role n = .server) (fun n => role n = .gateway) :=
  clusterRefinement.mediated reference_mediated

/-- Link failures preserve mediation. They can remove availability. -/
theorem cluster_failover_mediated (activeLink : PhysicalNode → PhysicalNode → Prop) :
    (physical.restrict activeLink).Mediated (fun n => role n = .client)
      (fun n => role n = .server) (fun n => role n = .gateway) :=
  clusterRefinement.mediated_during_failover reference_mediated activeLink

/-- A surviving replica supplies a concrete availability witness. -/
theorem primary_survives (activeLink : PhysicalNode → PhysicalNode → Prop)
    (ingress : activeLink .client .primary) (egress : activeLink .primary .server) :
    (physical.restrict activeLink).Reachable .client .server := by
  exact .step ⟨by simp [physical], ingress⟩
    (.step ⟨by simp [physical], egress⟩ (.refl _))

/-- The other replica also supplies an availability witness. -/
theorem standby_survives (activeLink : PhysicalNode → PhysicalNode → Prop)
    (ingress : activeLink .client .standby) (egress : activeLink .standby .server) :
    (physical.restrict activeLink).Reachable .client .server := by
  exact .step ⟨by simp [physical], ingress⟩
    (.step ⟨by simp [physical], egress⟩ (.refl _))

end Netlib.Examples

namespace Netlib.Examples

/-- A topology pattern for two distinct mandatory encryption layers. -/
inductive LayerNode
  | red | inner | gray | outer | black
  deriving DecidableEq

open LayerNode in
def layered : Netlib.Network LayerNode where
  link a b := (a = red ∧ b = inner) ∨ (a = inner ∧ b = gray) ∨
    (a = gray ∧ b = outer) ∨ (a = outer ∧ b = black)

theorem inner_mediated : layered.Mediated (· = .red) (· = .black) (· = .inner) := by
  apply Netlib.Network.mediated_of_cut (· = .red)
  · intro a b edge outsideA outsideB inside
    subst a
    simp [layered] at edge
    exact False.elim (outsideB edge)
  · exact fun _ h => h
  · intro b target inside
    subst b
    cases inside

theorem outer_mediated : layered.Mediated (· = .red) (· = .black) (· = .outer) := by
  apply Netlib.Network.mediated_of_cut
    (fun n => n = .red ∨ n = .inner ∨ n = .gray)
  · intro a b edge outsideA outsideB inside
    cases a <;> cases b <;> simp_all [layered]
  · intro a source
    exact .inl source
  · intro b target inside
    subst b
    simp at inside

/-- The mandatory-layer result applies to arbitrary paths, including paths with loops. -/
theorem layered_paths_have_two_gateways {trace : List LayerNode}
    (walk : layered.Walk .red .black trace) :
    ∃ inside ∈ trace, ∃ outside ∈ trace,
      inside = .inner ∧ outside = .outer ∧ inside ≠ outside := by
  apply Netlib.Network.two_distinct_gateways inner_mediated outer_mediated
    (fun node inner outer => ?_) rfl rfl walk
  subst node
  cases outer

/-- This path proves that the endpoints have a connection. -/
theorem layered_available : layered.Reachable .red .black := by
  exact .step (next := .inner) (by simp [layered])
    (.step (next := .gray) (by simp [layered])
      (.step (next := .outer) (by simp [layered])
        (.step (next := .black) (by simp [layered]) (.refl _))))

theorem inner_shutdown_isolates :
    (layered.without (· = .inner)).Isolated (· = .red) (· = .black) := by
  apply Netlib.Network.isolated_without_of_mediated inner_mediated
  · intro a source gateway
    subst a
    cases gateway
  · intro b target gateway
    subst b
    cases gateway

/-- A direct red-to-black link violates both mandatory-layer policies. -/
def bypassed : Netlib.Network LayerNode where
  link a b := layered.link a b ∨ (a = .red ∧ b = .black)

theorem bypass_breaks_inner :
    ¬bypassed.Mediated (· = .red) (· = .black) (· = .inner) := by
  intro mediated
  apply mediated .red .black rfl rfl
  exact ⟨by decide, by decide, .single ⟨.inr ⟨rfl, rfl⟩, by decide, by decide⟩⟩

theorem bypass_breaks_outer :
    ¬bypassed.Mediated (· = .red) (· = .black) (· = .outer) := by
  intro mediated
  apply mediated .red .black rfl rfl
  exact ⟨by decide, by decide, .single ⟨.inr ⟨rfl, rfl⟩, by decide, by decide⟩⟩

/-- Path simulation alone can hide skipped security roles. -/
def bypassPathRefinement : Netlib.Refinement bypassed layered where
  project := id
  simulate a b edge := by
    rcases edge with original | ⟨source, target⟩
    · exact .single original
    · subst a
      subst b
      exact layered_available

/-- This counterexample shows why gateway transfer needs a stuttering refinement. -/
theorem path_refinement_insufficient_for_mediation :
    Nonempty (Netlib.Refinement bypassed layered) ∧
      ¬bypassed.Mediated (· = .red) (· = .black) (· = .inner) :=
  ⟨⟨bypassPathRefinement⟩, bypass_breaks_inner⟩

end Netlib.Examples
