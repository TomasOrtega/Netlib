import Netlib.Check.FederatedCohortClasses
import Netlib.Check.FederatedCohortGraph
import Netlib.Check.FederatedCohortSharing

/-!
# Closed certificates for every independent header tuple

All component certificates and complete joint graphs come from native input.
Sparse discovery consumes one shared aggregate budget and never returns a
partially explored class as a certificate.
-/

namespace Netlib.Federation.Cohort

variable {input : Input} {profile : Profile}
variable {prepared : Prepared input profile}

structure Cell (prepared : Prepared input profile) (headers : Vector Packet.Header prepared.size) where
  accepted : Accepted prepared.context headers
  checked : Graph.Checked prepared.family headers accepted
  statesWithin : checked.sparse.graph.size ≤ profile.limits.states
  edgesWithin : Theory.FiniteProgressRank.edgeCount checked.sparse.graph.table ≤ profile.limits.edges

def Cell.work (value : Cell prepared headers) : Nat :=
  Theory.FiniteSuccessorGraph.workEstimate (Graph.costs prepared.context) value.checked.sparse.graph.size
    (Theory.FiniteProgressRank.edgeCount value.checked.sparse.graph.table)

def cellsWork (cells : List ((headers : Vector Packet.Header prepared.size) × Cell prepared headers)) : Nat :=
  (cells.map (fun entry => entry.2.work)).sum

def signatureRows (prepared : Prepared input profile) : Nat :=
  (prepared.locals.map (fun entry => (entry.certificate.cells.map (fun cell =>
    cell.2.graph.size + Theory.FiniteProgressRank.edgeCount cell.2.graph.table)).sum)).sum

def tupleWork (prepared : Prepared input profile) : Nat :=
  (prepared.classCount + 1) * (prepared.size + 1) +
    (prepared.classCount + 1) ^ 2 * (signatureRows prepared + 1) *
      ((InFlight.Control.nodes input).length + prepared.size + 1)

def Cell.transport (value : Cell prepared representative) (headers : Vector Packet.Header prepared.size)
    (accepted : Accepted prepared.context headers)
    (same : ∀ key, Control.successors prepared.context representative key = Control.successors prepared.context headers key) :
    Cell prepared headers :=
  ⟨accepted, value.checked.transport prepared.family representative value.accepted headers accepted same,
    value.statesWithin, value.edgesWithin⟩

private def reuseCell (prepared : Prepared input profile) (headers : Vector Packet.Header prepared.size)
    (accepted : Accepted prepared.context headers)
    (previous : List ((header : Vector Packet.Header prepared.size) × Cell prepared header)) :
    Option (Cell prepared headers) :=
  let current := Cached.Cache.build prepared.family headers accepted
  let signature := Sharing.signature current
  let rec search : List ((header : Vector Packet.Header prepared.size) × Cell prepared header) →
      Option (Cell prepared headers)
    | [] => none
    | ⟨prior, cell⟩ :: rest =>
      let old := Cached.Cache.build prepared.family prior cell.accepted
      if equal : Sharing.signature old = signature then
        some (cell.transport headers accepted (Sharing.successors_eq old current equal))
      else search rest
  search previous

private def buildCell (prepared : Prepared input profile) (headers : Vector Packet.Header prepared.size)
    (accepted : Accepted prepared.context headers) (budget : Nat) : Except String (Cell prepared headers) := do
  let limits : Theory.FiniteSuccessorGraph.Limits := ⟨profile.limits.states, profile.limits.edges, budget⟩
  let checked ← Graph.check prepared.family headers accepted prepared.initialGood limits
  if statesWithin : checked.sparse.graph.size ≤ profile.limits.states then
    if edgesWithin : Theory.FiniteProgressRank.edgeCount checked.sparse.graph.table ≤ profile.limits.edges then
      return ⟨accepted, checked, statesWithin, edgesWithin⟩
    else throw "A complete joint graph exceeds the successor budget."
  else throw "A complete joint graph exceeds the state budget."

private def buildCells (prepared : Prepared input profile)
    (previous : List ((header : Vector Packet.Header prepared.size) × Cell prepared header)) :
    (headers : List (Vector Packet.Header prepared.size)) →
    (∀ header ∈ headers, Accepted prepared.context header) → (budget : Nat) →
    Except String { values : List ((header : Vector Packet.Header prepared.size) × Cell prepared header) //
      values.map Sigma.fst = headers ∧ cellsWork values ≤ budget }
  | [], _, _ => return ⟨[], rfl, by simp [cellsWork]⟩
  | header :: rest, accepted, budget => do
    let selected := accepted header (by simp)
    let cell ← match reuseCell prepared header selected previous with
      | some reused => pure reused
      | none => buildCell prepared header selected budget
    if within : cell.work ≤ budget then
      let tail ← buildCells prepared (⟨header, cell⟩ :: previous) rest
        (fun header member => accepted header (List.mem_cons_of_mem _ member)) (budget - cell.work)
      return ⟨⟨header, cell⟩ :: tail.val, by simp only [List.map_cons, tail.property.1], by
        have remaining := tail.property.2
        simp only [cellsWork, List.map_cons, List.sum_cons]
        change cell.work + cellsWork tail.val ≤ budget
        omega⟩
    else throw "A complete joint graph exceeds the remaining cohort work budget."

structure Certified (input : Input) (profile : Profile) where
  prepared : Prepared input profile
  cells : List ((headers : Vector Packet.Header prepared.size) × Cell prepared headers)
  covered : cells.map Sigma.fst = prepared.headerTuples
  classesWithin : prepared.classCount ≤ profile.limits.classes
  totalWork : Nat
  totalWorkEq : totalWork = prepared.totalWork + tupleWork prepared + cellsWork cells
  workWithin : totalWork ≤ profile.limits.work

def certify (input : Input) (profile : Profile) : Except String (Certified input profile) := do
  let prepared ← prepare input profile
  if classesWithin : prepared.classCount ≤ profile.limits.classes then
    let start := prepared.totalWork + tupleWork prepared
    if admitted : start ≤ profile.limits.work then
      let cells ← buildCells prepared [] prepared.headerTuples prepared.headerTuple_accepted (profile.limits.work - start)
      let total := start + cellsWork cells.val
      have workWithin : total ≤ profile.limits.work := by
        have remaining := cells.property.2
        omega
      return ⟨prepared, cells.val, cells.property.1, classesWithin, total, rfl, workWithin⟩
    else throw "The complete header tuple estimate exceeds the cohort work budget."
  else throw "The independent header tuple count exceeds the class budget."

private def storedCell (values : List ((headers : Vector Packet.Header prepared.size) × Cell prepared headers))
    (headers : Vector Packet.Header prepared.size) (member : headers ∈ values.map Sigma.fst) :
    { value : Cell prepared headers // ⟨headers, value⟩ ∈ values } :=
  match values with
  | [] => False.elim (by simp at member)
  | ⟨actual, cell⟩ :: rest =>
    if same : actual = headers then
      same ▸ ⟨cell, List.mem_cons_self⟩
    else
      let tail := storedCell rest headers (by
        simpa only [List.map_cons, List.mem_cons, Ne.symm same, false_or] using member)
      ⟨tail.val, List.mem_cons_of_mem _ tail.property⟩

def Certified.representativeCell (value : Certified input profile) (headers : Vector Packet.Header value.prepared.size)
    (accepted : Accepted value.prepared.context headers) : Cell value.prepared (value.prepared.representatives headers) :=
  (storedCell value.cells _ (by rw [value.covered]; exact value.prepared.representatives_mem headers accepted)).val

theorem Certified.representativeCell_stored (value : Certified input profile)
    (headers : Vector Packet.Header value.prepared.size) (accepted : Accepted value.prepared.context headers) :
    ⟨value.prepared.representatives headers, value.representativeCell headers accepted⟩ ∈ value.cells :=
  (storedCell value.cells _ (by rw [value.covered]; exact value.prepared.representatives_mem headers accepted)).property

def Certified.cellAt (value : Certified input profile) (headers : Vector Packet.Header value.prepared.size)
    (accepted : Accepted value.prepared.context headers) : Cell value.prepared headers :=
  (value.representativeCell headers accepted).transport headers accepted
    (Control.successors_representatives value.prepared headers)

theorem Certified.cellAt_table (value : Certified input profile) (headers : Vector Packet.Header value.prepared.size)
    (accepted : Accepted value.prepared.context headers) :
    (value.cellAt headers accepted).checked.sparse.graph.table =
      (value.representativeCell headers accepted).checked.sparse.graph.table := rfl

end Netlib.Federation.Cohort
