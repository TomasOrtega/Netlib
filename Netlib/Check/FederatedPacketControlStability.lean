import Netlib.Check.FederatedPacketControl
import Netlib.Check.FederatedPacketPartition

/-!
# One control graph for each joint packet class

The joint representative preserves every native edge and control successor.
The equality applies to all keys, including their pending receiver phases.
-/

namespace Netlib.Federation.InFlight.Control

variable {input : Input}

theorem nativeEdge_representative (context : Context input) (header : Packet.Header)
    (current : Cursors input) (source target : Node) :
    nativeEdge context ((JointPartition.partition input context.first).representative header) current source target =
      nativeEdge context header current source target := by
  cases source with
  | inl source =>
    cases target with
    | inl target =>
      simp only [nativeEdge]
      rw [JointPartition.nativeEdge_representative input context.first (input.left.revisionAt current.1)
        (List.mem_append_left _ (input.left.at_mem current.1)) header context.first.request source target]
    | inr target => rfl
  | inr source =>
    cases target with
    | inl target => rfl
    | inr target =>
      simp only [nativeEdge]
      rw [JointPartition.nativeEdge_representative input context.first (input.right.revisionAt current.2)
        (List.mem_append_right _ (input.right.at_mem current.2)) header context.second.request source target]

theorem step_representative (context : Context input) (header : Packet.Header) (key : Key input) (move : Move) :
    step context ((JointPartition.partition input context.first).representative header) key move =
      step context header key move := by
  cases move <;> simp only [step, nativeEdge_representative]

theorem successors_representative (context : Context input) (header : Packet.Header) (key : Key input) :
    successors context ((JointPartition.partition input context.first).representative header) key =
      successors context header key := by
  simp only [successors, step_representative]

theorem successorRows_representative (context : Context input) (header : Packet.Header) (keys : List (Key input)) :
    keys.map (fun key => (key, successors context ((JointPartition.partition input context.first).representative header) key)) =
      keys.map (fun key => (key, successors context header key)) := by
  simp only [successors_representative]

theorem row_transport (context : Context input) (header : Packet.Header) (key : Key input)
    (property : List (Move × Key input) → Prop) :
    property (successors context ((JointPartition.partition input context.first).representative header) key) ↔
      property (successors context header key) := by
  rw [successors_representative]

theorem selected_rows (context : Context input) (header : Packet.Header)
    (accepted : context.first.selector.accepts header = true) :
    ∃ representative ∈ JointPartition.selectedHeaders input context.first,
      ∀ key, successors context representative key = successors context header key :=
  ⟨(JointPartition.partition input context.first).representative header,
    JointPartition.selected_representative_mem input context.first header accepted,
    successors_representative context header⟩

end Netlib.Federation.InFlight.Control
