import Netlib.Network.Architecture

/-!
# Failure models

A fault disables forwarding links, including links incident to failed nodes.
Availability claims state which faults and endpoint failures they cover.
Node faults disable incident links. Zero-step paths remain in the graph.
-/

namespace Netlib.Network

universe u
variable {Node : Type u}

structure Fault (Node : Type u) where
  nodes : Node → Prop
  links : Node → Node → Prop

def Fault.none : Fault Node := ⟨fun _ => False, fun _ _ => False⟩

def Fault.node (failed : Node) : Fault Node := ⟨(· = failed), fun _ _ => False⟩

def afterFault (net : Network Node) (fault : Fault Node) : Network Node :=
  net.restrict fun a b => ¬fault.nodes a ∧ ¬fault.nodes b ∧ ¬fault.links a b

abbrev FaultModel (Node : Type u) := Fault Node → Prop

def RobustAvailable (net : Network Node) (faults : FaultModel Node)
    (sources targets : Node → Prop) : Prop :=
  ∀ fault, faults fault → (net.afterFault fault).Available sources targets

def RobustIsolated (net : Network Node) (faults : FaultModel Node)
    (sources targets : Node → Prop) : Prop :=
  ∀ fault, faults fault → (net.afterFault fault).Isolated sources targets

def RobustMediated (net : Network Node) (faults : FaultModel Node)
    (sources targets gateways : Node → Prop) : Prop :=
  ∀ fault, faults fault → (net.afterFault fault).Mediated sources targets gateways

theorem robustIsolated_of_isolated {net : Network Node} {sources targets : Node → Prop}
    (secure : net.Isolated sources targets) (faults : FaultModel Node) :
    net.RobustIsolated faults sources targets :=
  fun _ _ => isolated_mono secure (fun _ _ edge => edge.1)

theorem robustMediated_of_mediated {net : Network Node}
    {sources targets gateways : Node → Prop}
    (secure : net.Mediated sources targets gateways) (faults : FaultModel Node) :
    net.RobustMediated faults sources targets gateways :=
  fun _ _ => mediated_mono secure (fun _ _ edge => edge.1)

/-- The model permits one failed internal node and no independent link failures. -/
def singleInternalNode (sources targets : Node → Prop) : FaultModel Node := fun fault =>
  (∀ a b, fault.nodes a → fault.nodes b → a = b) ∧
  (∀ a, sources a → ¬fault.nodes a) ∧
  (∀ b, targets b → ¬fault.nodes b) ∧
  (∀ a b, ¬fault.links a b)

theorem singleInternalNode_none (sources targets : Node → Prop) :
    singleInternalNode sources targets Fault.none := by
  exact ⟨fun _ _ impossible => False.elim impossible,
    fun _ _ impossible => impossible, fun _ _ impossible => impossible,
    fun _ _ impossible => impossible⟩

theorem singleInternalNode_node {sources targets : Node → Prop} (failed : Node)
    (outsideSources : ¬sources failed) (outsideTargets : ¬targets failed) :
    singleInternalNode sources targets (Fault.node failed) := by
  refine ⟨fun a b ha hb => ha.trans hb.symm, ?_, ?_, fun _ _ impossible => impossible⟩
  · intro a member same
    exact outsideSources (same ▸ member)
  · intro b member same
    exact outsideTargets (same ▸ member)

theorem Walk.afterFault {net : Network Node} {fault : Fault Node}
    {source target : Node} {trace : List Node} (walk : Walk net source target trace)
    (nodesAlive : ∀ node ∈ trace, ¬fault.nodes node)
    (linksAlive : ∀ a b, net.link a b → ¬fault.links a b) :
    Walk (net.afterFault fault) source target trace := by
  induction walk with
  | nil node => exact .nil node
  | @cons source next target trace edge tail ih =>
    have tailAlive : ∀ node ∈ trace, ¬fault.nodes node :=
      fun node member => nodesAlive node (List.mem_cons_of_mem source member)
    have nextAlive : ¬fault.nodes next := by
      apply tailAlive next
      cases tail <;> simp
    exact .cons ⟨edge, nodesAlive source (by simp), nextAlive, linksAlive source next edge⟩
      (ih tailAlive)

/-- Internally disjoint paths retain one complete path under a single node failure. -/
theorem reachable_disjoint_walks_after_fault {net : Network Node} {fault : Fault Node}
    {source target : Node} {firstTrace secondTrace : List Node}
    (first : Walk net source target firstTrace) (second : Walk net source target secondTrace)
    (sharedOnlyEndpoints : ∀ node ∈ firstTrace, node ∈ secondTrace →
      node = source ∨ node = target)
    (oneNode : ∀ a b, fault.nodes a → fault.nodes b → a = b)
    (sourceAlive : ¬fault.nodes source) (targetAlive : ¬fault.nodes target)
    (linksAlive : ∀ a b, net.link a b → ¬fault.links a b) :
    (net.afterFault fault).Reachable source target := by
  classical
  by_cases firstAlive : ∀ node ∈ firstTrace, ¬fault.nodes node
  · exact (first.afterFault firstAlive linksAlive).reachable
  · apply (second.afterFault ?_ linksAlive).reachable
    intro node member failed
    apply firstAlive
    intro other otherMember otherFailed
    have same := oneNode other node otherFailed failed
    have endpoint := sharedOnlyEndpoints other otherMember (same ▸ member)
    rcases endpoint with endpoint | endpoint
    · exact sourceAlive (endpoint ▸ otherFailed)
    · exact targetAlive (endpoint ▸ otherFailed)

theorem robustAvailable_disjoint_walks {net : Network Node} {sources targets : Node → Prop}
    (redundant : ∀ source target, sources source → targets target →
      ∃ firstTrace secondTrace,
        Walk net source target firstTrace ∧ Walk net source target secondTrace ∧
        ∀ node ∈ firstTrace, node ∈ secondTrace → node = source ∨ node = target) :
    net.RobustAvailable (singleInternalNode sources targets) sources targets := by
  intro fault ⟨oneNode, sourcesAlive, targetsAlive, linksAlive⟩ source target sourceMember targetMember
  obtain ⟨firstTrace, secondTrace, first, second, shared⟩ :=
    redundant source target sourceMember targetMember
  exact reachable_disjoint_walks_after_fault first second shared oneNode
    (sourcesAlive source sourceMember) (targetsAlive target targetMember)
    (fun a b _ => linksAlive a b)

/-- Distinct gateways provide a surviving two-hop path under one internal-node failure. -/
theorem reachable_two_gateways_after_fault {net : Network Node} {fault : Fault Node}
    {source target first second : Node}
    (oneNode : ∀ a b, fault.nodes a → fault.nodes b → a = b)
    (sourceAlive : ¬fault.nodes source) (targetAlive : ¬fault.nodes target)
    (noLinkFailure : ∀ a b, ¬fault.links a b)
    (distinct : first ≠ second)
    (sourceFirst : net.link source first) (firstTarget : net.link first target)
    (sourceSecond : net.link source second) (secondTarget : net.link second target) :
    (net.afterFault fault).Reachable source target := by
  classical
  have path (gateway : Node) (alive : ¬fault.nodes gateway)
      (enter : net.link source gateway) (leave : net.link gateway target) :
      (net.afterFault fault).Reachable source target :=
    .step ⟨enter, sourceAlive, alive, noLinkFailure source gateway⟩
      (.single ⟨leave, alive, targetAlive, noLinkFailure gateway target⟩)
  by_cases failed : fault.nodes first
  · have secondAlive : ¬fault.nodes second := fun secondFailed =>
      distinct (oneNode first second failed secondFailed)
    exact path second secondAlive sourceSecond secondTarget
  · exact path first failed sourceFirst firstTarget

theorem robustAvailable_two_gateways {net : Network Node} {sources targets : Node → Prop}
    (redundant : ∀ source target, sources source → targets target →
      ∃ first second, first ≠ second ∧
        net.link source first ∧ net.link first target ∧
        net.link source second ∧ net.link second target) :
    net.RobustAvailable (singleInternalNode sources targets) sources targets := by
  intro fault ⟨oneNode, sourcesAlive, targetsAlive, linksAlive⟩ source target sourceMember targetMember
  obtain ⟨first, second, distinct, enterFirst, leaveFirst, enterSecond, leaveSecond⟩ :=
    redundant source target sourceMember targetMember
  exact reachable_two_gateways_after_fault oneNode (sourcesAlive source sourceMember)
    (targetsAlive target targetMember) linksAlive distinct enterFirst leaveFirst enterSecond leaveSecond

end Netlib.Network
