import Netlib.Check.FederatedCohortContext
import Netlib.Theory.FiniteProduct

/-!
# Independent header choices for every packet

The class count is a product. Each tuple retains one fixed class per packet;
row transport then covers every accepted header without changing identity.
-/

namespace Netlib.Federation.Cohort

namespace Product
export Theory.FiniteProduct (tuples count Matches mem_tuples matches_of_getElem)
end Product

variable {input : Input} {profile : Profile}

def Prepared.choices (value : Prepared input profile) : List (List Packet.Header) :=
  value.locals.map fun entry => entry.certificate.cells.map Sigma.fst

@[simp] theorem Prepared.choices_length (value : Prepared input profile) :
    value.choices.length = value.size := by simp [Prepared.choices, Prepared.size]

@[simp] theorem Prepared.choice (value : Prepared input profile) (index : Fin value.size) :
    value.choices[index.val]'(by simp) = (value.locals.get index).certificate.cells.map Sigma.fst := by
  simp only [Prepared.choices, List.getElem_map]
  rfl

def Prepared.classCount (value : Prepared input profile) : Nat := Product.count value.choices

def Prepared.headerTuples (value : Prepared input profile) : List (Vector Packet.Header value.size) :=
  (Product.tuples value.choices).attach.map fun entry => Theory.FiniteProduct.vector entry.val
    (((Product.mem_tuples value.choices entry.val).mp entry.property).length.trans value.choices_length)

theorem Prepared.headerTuples_length (value : Prepared input profile) :
    value.headerTuples.length = value.classCount := by
  simp [Prepared.headerTuples, Prepared.classCount, Theory.FiniteProduct.tuples_length]

theorem Prepared.headerTuples_mem (value : Prepared input profile) (headers : Vector Packet.Header value.size) :
    headers ∈ value.headerTuples ↔ headers.toList ∈ Product.tuples value.choices := by
  constructor
  · intro member
    obtain ⟨entry, _, same⟩ := List.mem_map.mp member
    have equal := congrArg Vector.toList same
    simp only [Theory.FiniteProduct.vector_toList] at equal
    exact equal ▸ entry.property
  · intro member
    apply List.mem_map.mpr
    refine ⟨⟨headers.toList, member⟩, List.mem_attach _ _, ?_⟩
    apply Vector.toList_inj.mp
    simp

theorem Prepared.headerTuple_accepted (value : Prepared input profile) (headers : Vector Packet.Header value.size)
    (member : headers ∈ value.headerTuples) : Accepted value.context headers := by
  have matched := (Product.mem_tuples _ _).mp ((value.headerTuples_mem headers).mp member)
  intro index
  have selected := matched.getElem index.val (by simp) (by simp)
  rw [value.choice index] at selected
  have headerEq : headers.toList[index.val] = headers.get index := by simp [Vector.get, Fin.cast]
  rw [headerEq, (value.locals.get index).certificate.covered] at selected
  have accepted := InFlight.JointPartition.selectedHeaders_accepted input
    (value.locals.get index).certificate.context.first (headers.get index) selected
  change ((makeContext value.locals _).packets.get index).first.selector.accepts (headers.get index) = true
  rw [makeContext_packet]
  exact accepted

def Prepared.representatives (value : Prepared input profile) (headers : Vector Packet.Header value.size) :
    Vector Packet.Header value.size := Vector.ofFn fun index =>
  (InFlight.JointPartition.partition input (value.context.packets.get index).first).representative (headers.get index)

@[simp] theorem Prepared.representatives_get (value : Prepared input profile)
    (headers : Vector Packet.Header value.size) (index : Fin value.size) :
    (value.representatives headers).get index =
      (InFlight.JointPartition.partition input (value.context.packets.get index).first).representative (headers.get index) := by
  simp [Prepared.representatives, Vector.get, Fin.cast]

theorem Prepared.representatives_mem (value : Prepared input profile) (headers : Vector Packet.Header value.size)
    (accepted : Accepted value.context headers) : value.representatives headers ∈ value.headerTuples := by
  apply (value.headerTuples_mem _).mpr
  apply (Product.mem_tuples _ _).mpr
  apply Product.matches_of_getElem (by simp)
  intro index left right
  let position : Fin value.size := ⟨index, by simpa using left⟩
  have raw : (value.locals.get position).certificate.context.first.selector.accepts (headers.get position) = true := by
    have selected := accepted position
    change ((makeContext value.locals _).packets.get position).first.selector.accepts (headers.get position) = true at selected
    rw [makeContext_packet] at selected
    exact selected
  have selected := InFlight.JointPartition.selected_representative_mem input
    (value.locals.get position).certificate.context.first (headers.get position) raw
  rw [← (value.locals.get position).certificate.covered] at selected
  change (value.representatives headers).get position ∈ value.choices[position.val]
  rw [value.choice position, value.representatives_get]
  change (InFlight.JointPartition.partition input ((makeContext value.locals _).packets.get position).first).representative
    (headers.get position) ∈ _
  rw [makeContext_packet]
  exact selected

namespace Control

theorem localChecks_representatives (value : Prepared input profile) (headers : Vector Packet.Header value.size)
    (before after : Key input value.size) (move : Move value.size) :
    localChecks value.context (value.representatives headers) before after move =
      localChecks value.context headers before after move := by
  unfold localChecks
  apply congrArg ((List.finRange value.size).all)
  funext index
  cases move.local index with
  | none => rfl
  | some selected => simp only [value.representatives_get, InFlight.Control.step_representative]

theorem step_representatives (value : Prepared input profile) (headers : Vector Packet.Header value.size)
    (key : Key input value.size) (move : Move value.size) :
    step value.context (value.representatives headers) key move = step value.context headers key move := by
  simp only [step, localChecks_representatives]

theorem successors_representatives (value : Prepared input profile) (headers : Vector Packet.Header value.size)
    (key : Key input value.size) :
    successors value.context (value.representatives headers) key = successors value.context headers key := by
  simp only [successors, step_representatives]

end Control

end Netlib.Federation.Cohort
