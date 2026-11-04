import Netlib.Packet.Stateful
import Netlib.Packet.ProcessorTrace

namespace Netlib.Packet.Stateful

universe u v
variable {Node : Type u} {Store : Type v}

/-- Project every original hop, including its incoming packet and observed output. -/
def calls : List (Vertex Node Store) → List (Processor.Observation (Node × Node))
  | [] | [_] => []
  | before :: after :: vertices =>
    ⟨(before.node, after.node), before.header, some after.header⟩ :: calls (after :: vertices)

theorem calls_length (vertices : List (Vertex Node Store)) :
    (calls vertices).length = vertices.length - 1 := by
  induction vertices with
  | nil => rfl
  | cons before vertices ih =>
    cases vertices with
    | nil => rfl
    | cons after vertices =>
      simp only [calls, List.length_cons] at ih ⊢
      omega

private theorem calls_prepend (physical : Network Node) (programs : Node → Node → Processor Store)
    (previous : Vertex Node Store) {before after : Vertex Node Store} {vertices : List (Vertex Node Store)}
    (walk : Network.Walk (network physical programs) before after vertices) :
    calls (previous :: vertices) =
      ⟨(previous.node, before.node), previous.header, some before.header⟩ :: calls vertices := by
  cases walk <;> rfl

/-- Each successful graph hop is the corresponding exact shared-store processor call. -/
theorem walk_processor_trace (physical : Network Node) (programs : Node → Node → Processor Store)
    {before after : Vertex Node Store} {vertices : List (Vertex Node Store)}
    (walk : Network.Walk (network physical programs) before after vertices) :
    (Processor.transition (fun edge : Node × Node => programs edge.1 edge.2)).Trace
      before.store (calls vertices) after.store := by
  induction walk with
  | nil vertex => exact .nil vertex.store
  | @cons source next target vertices edge walk ih =>
    rw [calls_prepend physical programs source walk]
    exact .cons edge.2 ih

/-- Replaying projected hop inputs computes the walk's final store and every projected output. -/
theorem walk_execute (physical : Network Node) (programs : Node → Node → Processor Store)
    {before after : Vertex Node Store} {vertices : List (Vertex Node Store)}
    (walk : Network.Walk (network physical programs) before after vertices) :
    Processor.execute (fun edge : Node × Node => programs edge.1 edge.2)
      before.store ((calls vertices).map Processor.Observation.input) = (after.store, calls vertices) :=
  Processor.trace_eq_execute _ (walk_processor_trace physical programs walk)

theorem walk_calls_physical (physical : Network Node) (programs : Node → Node → Processor Store)
    {before after : Vertex Node Store} {vertices : List (Vertex Node Store)}
    (walk : Network.Walk (network physical programs) before after vertices) :
    ∀ call ∈ calls vertices, physical.link call.kind.1 call.kind.2 := by
  induction walk with
  | nil => simp [calls]
  | @cons source next target vertices edge walk ih =>
    rw [calls_prepend physical programs source walk]
    intro call member
    rcases List.mem_cons.mp member with rfl | member
    · exact edge.1
    · exact ih call member

end Netlib.Packet.Stateful
