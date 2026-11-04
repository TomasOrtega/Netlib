import Netlib.Network.Architecture
import Netlib.Network.Change

/-!
# Domain contracts

Connected domain graphs retain disjoint node types.
Border links must satisfy the same abstract contract as local forwarding steps.
-/

namespace Netlib.Network

universe u v w

variable {Node : Type u}

def union (left right : Network Node) : Network Node :=
  ⟨fun a b => left.link a b ∨ right.link a b⟩

theorem closed_union_iff (left right : Network Node) (region : Node → Prop) :
    (union left right).Closed region ↔ left.Closed region ∧ right.Closed region := by
  constructor
  · intro closed
    exact ⟨fun a b inside edge => closed a b inside (.inl edge),
      fun a b inside edge => closed a b inside (.inr edge)⟩
  · rintro ⟨leftClosed, rightClosed⟩ a b inside (edge | edge)
    · exact leftClosed a b inside edge
    · exact rightClosed a b inside edge

/-- A common local invariant protects paths that alternate between domains. -/
theorem isolated_union_of_closed {left right : Network Node}
    {sources targets region : Node → Prop}
    (leftClosed : left.Closed region) (rightClosed : right.Closed region)
    (sourceInside : ∀ a, sources a → region a)
    (targetOutside : ∀ b, targets b → ¬region b) :
    (union left right).Isolated sources targets :=
  isolated_of_closed region
    (fun a b edge inside =>
      (closed_union_iff left right region).mpr ⟨leftClosed, rightClosed⟩ a b inside edge)
    sourceInside targetOutside

/-- Both domains must preserve the same cut after gateway removal. -/
theorem mediated_union_of_closed {left right : Network Node}
    {sources targets gateways region : Node → Prop}
    (leftClosed : (left.without gateways).Closed region)
    (rightClosed : (right.without gateways).Closed region)
    (sourceInside : ∀ a, sources a → region a)
    (targetOutside : ∀ b, targets b → ¬region b) :
    (union left right).Mediated sources targets gateways := by
  apply mediated_of_cut region
    (sourceInside := sourceInside) (targetOutside := targetOutside)
  intro a b edge outsideA outsideB inside
  rcases edge with edge | edge
  · exact leftClosed a b inside ⟨edge, outsideA, outsideB⟩
  · exact rightClosed a b inside ⟨edge, outsideA, outsideB⟩

/-- An explicit interface joins local availability guarantees. -/
theorem available_union_via {left right : Network Node}
    {sources targets : Node → Prop} (interface : Node → Prop)
    (sourceToInterface : ∀ a, sources a → ∃ middle, interface middle ∧ left.Reachable a middle)
    (interfaceToTarget : right.Available interface targets) :
    (union left right).Available sources targets := by
  intro a b source target
  obtain ⟨middle, exposed, path⟩ := sourceToInterface a source
  exact (path.mono (net' := union left right) (fun _ _ edge => .inl edge)).trans
    ((interfaceToTarget middle b exposed target).mono (net' := union left right)
      (fun _ _ edge => .inr edge))

/-- The sum keeps private node identities disjoint across domains. -/
def interconnect {Left : Type u} {Right : Type v}
    (left : Network Left) (right : Network Right)
    (leftToRight : Left → Right → Prop) (rightToLeft : Right → Left → Prop) :
    Network (Sum Left Right) where
  link
    | .inl a, .inl b => left.link a b
    | .inr a, .inr b => right.link a b
    | .inl a, .inr b => leftToRight a b
    | .inr a, .inl b => rightToLeft a b

theorem reachable_interconnect_forward {Left : Type u} {Right : Type v}
    {left : Network Left} {right : Network Right}
    {leftToRight : Left → Right → Prop} {rightToLeft : Right → Left → Prop}
    {source exit : Left} {entry target : Right}
    (leftPath : left.Reachable source exit) (border : leftToRight exit entry)
    (rightPath : right.Reachable entry target) :
    (interconnect left right leftToRight rightToLeft).Reachable (.inl source) (.inr target) := by
  have before : (interconnect left right leftToRight rightToLeft).Reachable
      (.inl source) (.inl exit) :=
    leftPath.map Sum.inl (fun _ _ edge => .single edge)
  have after : (interconnect left right leftToRight rightToLeft).Reachable
      (.inr entry) (.inr target) :=
    rightPath.map Sum.inr (fun _ _ edge => .single edge)
  have crossing : (interconnect left right leftToRight rightToLeft).Reachable
      (.inl exit) (.inr entry) := .single border
  exact (before.trans crossing).trans after

end Netlib.Network

namespace Netlib.StutteringRefinement

universe u v w

/-- Local contracts compose only when each border step also satisfies the contract. -/
def interconnect {Left : Type u} {Right : Type v} {Abstract : Type w}
    {left : Network Left} {right : Network Right} {abstract : Network Abstract}
    (leftContract : StutteringRefinement left abstract)
    (rightContract : StutteringRefinement right abstract)
    (leftToRight : Left → Right → Prop) (rightToLeft : Right → Left → Prop)
    (forward : ∀ a b, leftToRight a b → leftContract.project a = rightContract.project b ∨
      abstract.link (leftContract.project a) (rightContract.project b))
    (backward : ∀ a b, rightToLeft a b → rightContract.project a = leftContract.project b ∨
      abstract.link (rightContract.project a) (leftContract.project b)) :
    StutteringRefinement (Network.interconnect left right leftToRight rightToLeft) abstract where
  project := Sum.elim leftContract.project rightContract.project
  simulate a b edge := by
    cases a with
    | inl a =>
      cases b with
      | inl b => exact leftContract.simulate a b edge
      | inr b => exact forward a b edge
    | inr a =>
      cases b with
      | inl b => exact backward a b edge
      | inr b => exact rightContract.simulate a b edge

end Netlib.StutteringRefinement
