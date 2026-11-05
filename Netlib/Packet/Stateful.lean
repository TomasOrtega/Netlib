import Netlib.Packet.Processor
import Netlib.Packet.Transfer

namespace Netlib.Packet.Stateful

universe u v

structure Vertex (Node : Type u) (Store : Type v) where
  node : Node
  header : Header
  store : Store
  deriving Repr, DecidableEq

/-- Each successful forwarding step threads the complete processor store. -/
def network (physical : Network Node) (programs : Node → Node → Processor Store) :
    Network (Vertex Node Store) where
  link before after := physical.link before.node after.node ∧
    (programs before.node after.node).run before.store before.header = (after.store, some after.header)

def physicalProjection (physical : Network Node) (programs : Node → Node → Processor Store) :
    StutteringRefinement (network physical programs) physical where
  project := Vertex.node
  simulate _ _ edge := .inr edge.1

theorem reachable_physical (physical : Network Node) (programs : Node → Node → Processor Store)
    {before after : Vertex Node Store} (path : (network physical programs).Reachable before after) :
    physical.Reachable before.node after.node :=
  (physicalProjection physical programs).toRefinement.reachable path

theorem isolated_of_physical (physical : Network Node) (programs : Node → Node → Processor Store)
    {sources targets : Node → Prop} (isolated : physical.Isolated sources targets) :
    (network physical programs).Isolated (fun vertex => sources vertex.node) (fun vertex => targets vertex.node) :=
  (physicalProjection physical programs).toRefinement.isolated isolated

theorem mediated_of_physical (physical : Network Node) (programs : Node → Node → Processor Store)
    {sources targets gateways : Node → Prop} (mediated : physical.Mediated sources targets gateways) :
    (network physical programs).Mediated (fun vertex => sources vertex.node)
      (fun vertex => targets vertex.node) (fun vertex => gateways vertex.node) :=
  (physicalProjection physical programs).mediated mediated

theorem invariant (physical : Network Node) (programs : Node → Node → Processor Store)
    (property : Store → Prop) (preserved : ∀ source target, (programs source target).Preserves property)
    {before after : Vertex Node Store} (path : (network physical programs).Reachable before after)
    (initial : property before.store) : property after.store := by
  induction path with
  | refl => exact initial
  | @step before middle after edge _ ih =>
    have safe := preserved before.node middle.node before.store before.header initial
    rw [edge.2] at safe
    exact ih safe

def stateless (programs : Node → Node → Header → Option Header) : Node → Node → Processor Store :=
  fun source target => Processor.stateless (programs source target)

def statelessTransfer (physical : Network Node) (programs : Node → Node → Header → Option Header) : Transfer Node :=
  Transfer.ofPrograms physical (fun source target => ⟨fun before after => programs source target before = some after⟩)

def statelessProjection (physical : Network Node) (programs : Node → Node → Header → Option Header) :
    StutteringRefinement (network physical (stateless programs : Node → Node → Processor Store))
      (statelessTransfer physical programs).network where
  project vertex := (vertex.node, vertex.header)
  simulate before after edge := by
    apply Or.inr
    refine ⟨edge.1, ?_⟩
    exact congrArg Prod.snd edge.2

theorem stateless_store (physical : Network Node) (programs : Node → Node → Header → Option Header)
    {before after : Vertex Node Store}
    (path : (network physical (stateless programs)).Reachable before after) : after.store = before.store := by
  induction path with
  | refl => rfl
  | step edge _ ih =>
    exact ih.trans (congrArg Prod.fst edge.2).symm

theorem stateless_lift (physical : Network Node) (programs : Node → Node → Header → Option Header)
    {before after : Node × Header} (store : Store)
    (path : (statelessTransfer physical programs).network.Reachable before after) :
    (network physical (stateless programs)).Reachable
      ⟨before.1, before.2, store⟩ ⟨after.1, after.2, store⟩ := by
  induction path with
  | refl => exact .refl _
  | @step before middle after edge _ ih =>
    apply Network.Reachable.step (next := ⟨middle.1, middle.2, store⟩)
    · refine ⟨edge.1, ?_⟩
      change (store, programs before.1 middle.1 before.2) = (store, some middle.2)
      rw [edge.2]
    · exact ih

/-- Stateless programs agree with transfer semantics and cannot change the store. -/
theorem stateless_reachable_iff (physical : Network Node) (programs : Node → Node → Header → Option Header)
    (before after : Vertex Node Store) :
    (network physical (stateless programs)).Reachable before after ↔
      after.store = before.store ∧
        (statelessTransfer physical programs).network.Reachable (before.node, before.header) (after.node, after.header) := by
  constructor
  · intro path
    exact ⟨stateless_store physical programs path,
      (statelessProjection physical programs).toRefinement.reachable path⟩
  · rintro ⟨same, path⟩
    have lifted := stateless_lift physical programs before.store path
    cases before
    cases after
    cases same
    exact lifted

end Netlib.Packet.Stateful
