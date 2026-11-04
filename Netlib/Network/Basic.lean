import Std

namespace Netlib

universe u v

/-- A directed graph of permitted forwarding steps for one traffic class. -/
structure Network (Node : Type u) where
  link : Node → Node → Prop

namespace Network

variable {Node : Type u} {Other : Type v}

/-- Reachability includes the zero-hop path. -/
inductive Reachable (net : Network Node) : Node → Node → Prop
  | refl (node) : Reachable net node node
  | step {source next target} : net.link source next →
      Reachable net next target → Reachable net source target

namespace Reachable

variable {net net' : Network Node} {a b c : Node}

theorem single (edge : net.link a b) : Reachable net a b :=
  .step edge (.refl b)

theorem trans (left : Reachable net a b) (right : Reachable net b c) :
    Reachable net a c := by
  induction left with
  | refl => exact right
  | step edge _ ih => exact .step edge (ih right)

/-- Link removal cannot create a path. -/
theorem mono (subset : ∀ a b, net.link a b → net'.link a b)
    (path : Reachable net a b) : Reachable net' a b := by
  induction path with
  | refl node => exact .refl node
  | step edge _ ih => exact .step (subset _ _ edge) ih

/-- Each concrete step can map to a finite abstract path. -/
theorem map (f : Node → Other) {abstract : Network Other}
    (simulate : ∀ a b, net.link a b → Reachable abstract (f a) (f b))
    (path : Reachable net a b) : Reachable abstract (f a) (f b) := by
  induction path with
  | refl node => exact .refl (f node)
  | step edge _ ih => exact (simulate _ _ edge).trans ih

end Reachable

/-- Keep the links that satisfy the extra predicate. -/
def restrict (net : Network Node) (allowed : Node → Node → Prop) : Network Node :=
  ⟨fun a b => net.link a b ∧ allowed a b⟩

/-- Disable each link to or from a node in the set. -/
def without (net : Network Node) (disabled : Node → Prop) : Network Node :=
  net.restrict fun a b => ¬disabled a ∧ ¬disabled b

/-- A path whose endpoints and forwarding steps avoid every gateway. -/
def Bypass (net : Network Node) (gateways : Node → Prop) (a b : Node) : Prop :=
  ¬gateways a ∧ ¬gateways b ∧ Reachable (net.without gateways) a b

/-- No permitted path connects any source to any target. -/
def Isolated (net : Network Node) (sources targets : Node → Prop) : Prop :=
  ∀ a b, sources a → targets b → ¬Reachable net a b

/-- Every path between the designated zones must visit a gateway. -/
def Mediated (net : Network Node) (sources targets gateways : Node → Prop) : Prop :=
  ∀ a b, sources a → targets b → ¬Bypass net gateways a b

variable {net net' : Network Node} {sources targets gateways : Node → Prop}

theorem reachable_restrict (allowed : Node → Node → Prop) {a b : Node}
    (path : Reachable (net.restrict allowed) a b) : Reachable net a b :=
  Reachable.mono (net := net.restrict allowed) (net' := net) (fun _ _ edge => edge.1) path

theorem isolated_mono (isolated : net.Isolated sources targets)
    (subset : ∀ a b, net'.link a b → net.link a b) :
    net'.Isolated sources targets := by
  intro a b source target path
  exact isolated a b source target (path.mono subset)

theorem mediated_mono (mediated : net.Mediated sources targets gateways)
    (subset : ∀ a b, net'.link a b → net.link a b) :
    net'.Mediated sources targets gateways := by
  intro a b source target bypass
  apply mediated a b source target
  exact ⟨bypass.1, bypass.2.1,
    Reachable.mono (net := net'.without gateways) (net' := net.without gateways)
      (fun _ _ edge => ⟨subset _ _ edge.1, edge.2⟩) bypass.2.2⟩

/-- A gateway cut blocks traffic when both endpoint zones lie outside the cut. -/
theorem isolated_without_of_mediated
    (mediated : net.Mediated sources targets gateways)
    (sourceOutside : ∀ a, sources a → ¬gateways a)
    (targetOutside : ∀ b, targets b → ¬gateways b) :
    (net.without gateways).Isolated sources targets := by
  intro a b source target path
  exact mediated a b source target ⟨sourceOutside a source, targetOutside b target, path⟩

/-- A closed region separates its source nodes from outside target nodes. -/
theorem isolated_of_closed (region : Node → Prop)
    (closed : ∀ a b, net.link a b → region a → region b)
    (sourceInside : ∀ a, sources a → region a)
    (targetOutside : ∀ b, targets b → ¬region b) :
    net.Isolated sources targets := by
  intro a b source target path
  apply targetOutside b target
  have preserve : ∀ {x y}, Reachable net x y → region x → region y := by
    intro x y path
    induction path with
    | refl => exact id
    | step edge _ ih => exact fun inside => ih (closed _ _ edge inside)
  exact preserve path (sourceInside a source)

/-- Check each source zone before their union. -/
theorem isolated_union_sources :
    net.Isolated (fun a => sources a ∨ gateways a) targets ↔
      net.Isolated sources targets ∧ net.Isolated gateways targets := by
  constructor
  · intro h
    exact ⟨fun a b ha hb => h a b (.inl ha) hb,
      fun a b ha hb => h a b (.inr ha) hb⟩
  · rintro ⟨left, right⟩ a b (ha | ha) hb
    · exact left a b ha hb
    · exact right a b ha hb

/-- Check each target zone before their union. -/
theorem isolated_union_targets :
    net.Isolated sources (fun a => targets a ∨ gateways a) ↔
      net.Isolated sources targets ∧ net.Isolated sources gateways := by
  constructor
  · intro h
    exact ⟨fun a b ha hb => h a b ha (.inl hb),
      fun a b ha hb => h a b ha (.inr hb)⟩
  · rintro ⟨left, right⟩ a b ha (hb | hb)
    · exact left a b ha hb
    · exact right a b ha hb

end Network
end Netlib

namespace Netlib.Network

universe u
variable {Node : Type u}

/-- A forwarding path together with its complete, nonempty vertex trace. -/
inductive Walk (net : Netlib.Network Node) : Node → Node → List Node → Prop
  | nil (node) : Walk net node node [node]
  | cons {source next target trace} : net.link source next →
      Walk net next target trace → Walk net source target (source :: trace)

namespace Walk

variable {net : Netlib.Network Node} {a b : Node} {trace : List Node}

theorem reachable (walk : Walk net a b trace) : Reachable net a b := by
  induction walk with
  | nil node => exact .refl node
  | cons edge _ ih => exact .step edge ih

theorem exists_of_reachable (path : Reachable net a b) :
    ∃ trace, Walk net a b trace := by
  induction path with
  | refl node => exact ⟨[node], .nil node⟩
  | @step source next target edge _ ih =>
    obtain ⟨trace, walk⟩ := ih
    exact ⟨source :: trace, .cons edge walk⟩

theorem bypass_of_avoids {gateways : Node → Prop} (walk : Walk net a b trace)
    (avoids : ∀ node ∈ trace, ¬gateways node) : Bypass net gateways a b := by
  induction walk with
  | nil node =>
    have outside := avoids node (by simp)
    exact ⟨outside, outside, .refl node⟩
  | @cons source next target trace edge _ ih =>
    have sourceOutside := avoids source (by simp)
    have tail := ih (fun node member => avoids node (by simp [member]))
    exact ⟨sourceOutside, tail.2.1, .step ⟨edge, sourceOutside, tail.1⟩ tail.2.2⟩

/-- Bypass reachability has a concrete vertex trace avoiding all gateways. -/
theorem exists_avoiding_of_bypass {gateways : Node → Prop}
    (bypass : Bypass net gateways a b) :
    ∃ trace, Walk net a b trace ∧ ∀ node ∈ trace, ¬gateways node := by
  obtain ⟨outside, targetOutside, path⟩ := bypass
  induction path with
  | refl node => exact ⟨[node], .nil node, by simpa using outside⟩
  | @step source next target edge _ ih =>
    obtain ⟨trace, walk, avoids⟩ := ih edge.2.2 targetOutside
    refine ⟨source :: trace, .cons edge.1 walk, ?_⟩
    intro node member
    rcases List.mem_cons.mp member with rfl | member
    · exact edge.2.1
    · exact avoids node member

end Walk

/-- Mediation is equivalent to gateway occurrence on every full path trace. -/
theorem mediated_iff_every_walk {net : Netlib.Network Node}
    {sources targets gateways : Node → Prop} :
    net.Mediated sources targets gateways ↔
      ∀ a b trace, sources a → targets b → Walk net a b trace →
        ∃ node ∈ trace, gateways node := by
  classical
  constructor
  · intro mediated a b trace source target walk
    apply Classical.byContradiction
    intro noGateway
    apply mediated a b source target
    apply walk.bypass_of_avoids
    intro node member gateway
    exact noGateway ⟨node, member, gateway⟩
  · intro every a b source target bypass
    obtain ⟨trace, walk, avoids⟩ := Walk.exists_avoiding_of_bypass bypass
    obtain ⟨node, member, gateway⟩ := every a b trace source target walk
    exact avoids node member gateway

end Netlib.Network

namespace Netlib.Network

universe u
variable {Node : Type u} {net : Netlib.Network Node}

/-- A boundary link must have a gateway endpoint. -/
theorem mediated_of_cut {sources targets gateways : Node → Prop} (region : Node → Prop)
    (closedWithoutGateways : ∀ a b, net.link a b → ¬gateways a → ¬gateways b →
      region a → region b)
    (sourceInside : ∀ a, sources a → region a)
    (targetOutside : ∀ b, targets b → ¬region b) :
    net.Mediated sources targets gateways := by
  have cut : (net.without gateways).Isolated sources targets :=
    isolated_of_closed region
      (fun a b edge => closedWithoutGateways a b edge.1 edge.2.1 edge.2.2)
      sourceInside targetOutside
  intro a b source target bypass
  exact cut a b source target bypass.2.2

/-- Disjoint mandatory gateway layers contribute two distinct vertices to every path. -/
theorem two_distinct_gateways {sources targets inner outer : Node → Prop}
    (innerMediated : net.Mediated sources targets inner)
    (outerMediated : net.Mediated sources targets outer)
    (disjoint : ∀ node, inner node → ¬outer node)
    {a b : Node} {trace : List Node}
    (source : sources a) (target : targets b) (walk : Walk net a b trace) :
    ∃ inside ∈ trace, ∃ outside ∈ trace, inner inside ∧ outer outside ∧ inside ≠ outside := by
  obtain ⟨inside, insideMem, inner⟩ :=
    mediated_iff_every_walk.mp innerMediated a b trace source target walk
  obtain ⟨outside, outsideMem, outer⟩ :=
    mediated_iff_every_walk.mp outerMediated a b trace source target walk
  refine ⟨inside, insideMem, outside, outsideMem, inner, outer, ?_⟩
  intro same
  subst outside
  exact disjoint inside inner outer

end Netlib.Network
