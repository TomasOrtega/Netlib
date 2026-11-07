import Netlib.Check.DomainContractValidation
import Netlib.Network.FiniteDecision

/-!
# Native local domain certificates

The checker derives both graph bounds from native forwarding decisions.
Each selected partition cell retains concrete checked must paths.
-/

namespace Netlib.Federation.Native

open Packet

structure Limits where
  cells : Nat := 100000
  work : Nat := 1000000
  deriving Repr

private def verify (condition : Prop) [Decidable condition] (message : String) :
    Except String { _value : Unit // condition } :=
  if accepted : condition then .ok ⟨(), accepted⟩ else .error message

def partition (revision : Revision) (selected : Case) : Packet.Partition :=
  revision.snapshot.compile.trafficPartition selected.selector

def headers (revision : Revision) (selected : Case) : List Header :=
  (partition revision selected).representatives.filter selected.selector.accepts

def nativeRows (revision : Revision) : Nat :=
  let intent := revision.snapshot.intent
  intent.devices.length + intent.principals.length + intent.resources.length + intent.operations.length +
    intent.permissions.length + intent.requests.length + intent.traffic.length + intent.requirements.length +
    intent.groups.foldl (fun count group => count + 1 + group.members.length) 0 +
    revision.snapshot.routers.foldl (fun count router =>
    count + 1 + router.routes.routes.length + router.bindings.length + router.nftables.rules.length) 0

def workEstimate (contract : Contract) (revision : Revision) : Nat :=
  let nodes := revision.snapshot.intent.ids.length
  let rows := nativeRows revision + revision.projection.length + revision.anchors.length + contract.nodes.length +
    contract.cases.foldl (fun count selected => count + 1 + selected.upper.length + selected.must.length) 0 + 1
  rows * rows + contract.cases.foldl (fun count selected => count +
    (partition revision selected).cellCount *
      (nodes * nodes + selected.must.length * (nodes + 1) ^ 4) * rows) 0

structure Path (revision : Revision) (selected : Case) (header : Header) (arc : Arc) where
  trace : List String
  valid : Certificate.validPath revision.snapshot.intent.ids
    (revision.snapshot.compile.edge header selected.request)
    (revision.anchor arc.source) (revision.anchor arc.target) trace = true

theorem Path.walk (value : Path revision selected header arc) :
    Network.Walk (revision.native selected header)
      (revision.anchor arc.source) (revision.anchor arc.target) value.trace := by
  have walk := Certificate.validPath_walk _ _ _ _ _ value.valid
  change Network.Walk (Certificate.finiteNetwork revision.snapshot.compile.ids
    (revision.snapshot.compile.edge header selected.request)) _ _ value.trace at walk
  rw [DataPlane.Config.finiteNetwork_eq_model] at walk
  rw [revision.snapshot.model_correct] at walk
  exact walk

structure Cell (contract : Contract) (revision : Revision) (selected : Case) (header : Header) where
  upper : StutteringRefinement (revision.native selected header) (contract.upperModel selected)
  projection : upper.project = revision.project
  paths : List ((arc : Arc) × Path revision selected header arc)
  covered : paths.map Sigma.fst = selected.must

structure CaseResult (contract : Contract) (revision : Revision) (selected : Case) where
  cells : List ((header : Header) × Cell contract revision selected header)
  covered : cells.map Sigma.fst = headers revision selected

structure Checked (contract : Contract) (revision : Revision) where
  limits : Limits
  validated : Revision.Validated contract revision
  workWithin : workEstimate contract revision ≤ limits.work
  cellBounds : ∀ selected ∈ contract.cases, (partition revision selected).cellCount ≤ limits.cells
  results : List ((selected : Case) × CaseResult contract revision selected)
  covered : results.map Sigma.fst = contract.cases

private def upperAllowed (revision : Revision) (selected : Case) (header : Header) : Bool :=
  revision.snapshot.intent.ids.all fun source => revision.snapshot.intent.ids.all fun target =>
    decide (revision.snapshot.compile.edge header selected.request source target = true →
      revision.project source = revision.project target ∨
        arcs selected.upper (revision.project source) (revision.project target) = true)

private def upper_refinement (valid : Revision.Validated contract revision)
    (checked : upperAllowed revision selected header = true) :
    StutteringRefinement (revision.native selected header) (contract.upperModel selected) where
  project := revision.project
  simulate source target edge := by
    have native : source ∈ revision.snapshot.intent.ids ∧ target ∈ revision.snapshot.intent.ids ∧
        revision.snapshot.compile.edge header selected.request source target = true := by
      rw [Revision.native, ← revision.snapshot.model_correct,
        ← DataPlane.Config.finiteNetwork_eq_model] at edge
      exact edge
    have all : ∀ source ∈ revision.snapshot.intent.ids, ∀ target ∈ revision.snapshot.intent.ids,
        revision.snapshot.compile.edge header selected.request source target = true →
          revision.project source = revision.project target ∨
            arcs selected.upper (revision.project source) (revision.project target) = true := by
      simpa only [upperAllowed, List.all_eq_true, decide_eq_true_eq] using checked
    rcases all source native.1 target native.2.1 native.2.2 with same | allowed
    · exact .inl same
    · exact .inr ⟨valid.projectMember source native.1, valid.projectMember target native.2.1, allowed⟩

private def checkPath (revision : Revision) (selected : Case) (header : Header) (arc : Arc) :
    Except String (Path revision selected header arc) := do
  let decision ← (Compliance.decideReach revision.snapshot.intent.ids
    (revision.snapshot.compile.edge header selected.request) (revision.anchor arc.source) (revision.anchor arc.target)).mapError
      (fun reason => s!"Case {selected.id}, packet {repr header}: {reason}")
  match decision with
  | .reachable trace valid => return ⟨trace, valid⟩
  | .isolated region _ =>
    throw s!"Case {selected.id}, packet {repr header}: native must path {arc.source} -> {arc.target} is blocked by cut {region}."

private def checkPaths (revision : Revision) (selected : Case) (header : Header) :
    (arcs : List Arc) → Except String { values : List ((arc : Arc) × Path revision selected header arc) //
      values.map Sigma.fst = arcs }
  | [] => return ⟨[], rfl⟩
  | arc :: rest => do
    let head ← checkPath revision selected header arc
    let tail ← checkPaths revision selected header rest
    return ⟨⟨arc, head⟩ :: tail.val, by simp only [List.map_cons, tail.property]⟩

private def checkCell (contract : Contract) (revision : Revision) (valid : Revision.Validated contract revision)
    (selected : Case) (header : Header) : Except String (Cell contract revision selected header) := do
  let upper ← verify (upperAllowed revision selected header = true)
    s!"Case {selected.id}: a native edge leaves the public upper graph at packet {repr header}."
  let paths ← checkPaths revision selected header selected.must
  return ⟨upper_refinement valid upper.property, rfl, paths.val, paths.property⟩

private def checkCells (contract : Contract) (revision : Revision) (valid : Revision.Validated contract revision)
    (selected : Case) : (headers : List Header) →
    Except String { values : List ((header : Header) × Cell contract revision selected header) //
      values.map Sigma.fst = headers }
  | [] => return ⟨[], rfl⟩
  | header :: rest => do
    let head ← checkCell contract revision valid selected header
    let tail ← checkCells contract revision valid selected rest
    return ⟨⟨header, head⟩ :: tail.val, by simp only [List.map_cons, tail.property]⟩

private def checkCases (contract : Contract) (revision : Revision) (valid : Revision.Validated contract revision) :
    (cases : List Case) → Except String { values : List ((selected : Case) × CaseResult contract revision selected) //
      values.map Sigma.fst = cases }
  | [] => return ⟨[], rfl⟩
  | selected :: rest => do
    if (headers revision selected).isEmpty then throw s!"Case {selected.id}: the selected header class is empty."
    let cells ← checkCells contract revision valid selected (headers revision selected)
    let tail ← checkCases contract revision valid rest
    return ⟨⟨selected, cells.val, cells.property⟩ :: tail.val, by simp only [List.map_cons, tail.property]⟩

def check (contract : Contract) (revision : Revision) (limits : Limits := {}) : Except String (Checked contract revision) := do
  let work ← verify (workEstimate contract revision ≤ limits.work)
    s!"Native domain work estimate {workEstimate contract revision} exceeds budget {limits.work}."
  let cells ← verify (contract.cases.all (fun selected => decide ((partition revision selected).cellCount ≤ limits.cells)) = true)
    s!"A native domain packet partition exceeds its cell budget {limits.cells}."
  let valid ← revision.check contract
  let results ← checkCases contract revision valid.property contract.cases
  return ⟨limits, valid.property, work.property,
    (by simpa only [List.all_eq_true, decide_eq_true_eq] using cells.property), results.val, results.property⟩

theorem native_representative (revision : Revision) (selected : Case) (header : Header) :
    revision.native selected ((partition revision selected).representative header) = revision.native selected header := by
  exact (revision.snapshot.model_correct _ _).symm.trans
    ((revision.snapshot.compile.model_representative selected.selector header selected.request).trans
      (revision.snapshot.model_correct header selected.request))

private theorem CaseResult.at (value : CaseResult contract revision selected) (header : Header)
    (accepted : selected.selector.accepts header = true) :
    Nonempty (Cell contract revision selected ((partition revision selected).representative header)) := by
  have selectedCell : (partition revision selected).representative header ∈ headers revision selected := by
    apply List.mem_filter.mpr
    refine ⟨(partition revision selected).representative_mem header, ?_⟩
    rw [(partition revision selected).match_stable selected.selector
      (revision.snapshot.compile.trafficPartition_selected selected.selector) header]
    exact accepted
  rw [← value.covered] at selectedCell
  obtain ⟨⟨cell, result⟩, member, same⟩ := List.mem_map.mp selectedCell
  cases same
  exact ⟨result⟩

private theorem Checked.case_at (value : Checked contract revision) (selected : Case) (member : selected ∈ contract.cases) :
    Nonempty (CaseResult contract revision selected) := by
  rw [← value.covered] at member
  obtain ⟨⟨caseValue, result⟩, present, same⟩ := List.mem_map.mp member
  cases same
  exact ⟨result⟩

def Checked.upper (value : Checked contract revision) (selected : Case) (member : selected ∈ contract.cases)
    (header : Header) (accepted : selected.selector.accepts header = true) :
    StutteringRefinement (revision.native selected header) (contract.upperModel selected) where
  project := revision.project
  simulate source target edge := by
    obtain ⟨caseResult⟩ := value.case_at selected member
    obtain ⟨cell⟩ := caseResult.at header accepted
    rw [← native_representative revision selected header] at edge
    have simulated := cell.upper.simulate source target edge
    rw [cell.projection] at simulated
    exact simulated

theorem Checked.path (value : Checked contract revision) (selected : Case) (member : selected ∈ contract.cases)
    (header : Header) (accepted : selected.selector.accepts header = true) (arc : Arc) (present : arc ∈ selected.must) :
    ∃ trace, Network.Walk (revision.native selected header) (revision.anchor arc.source) (revision.anchor arc.target) trace := by
  obtain ⟨caseResult⟩ := value.case_at selected member
  obtain ⟨cell⟩ := caseResult.at header accepted
  rw [← cell.covered] at present
  obtain ⟨⟨actualArc, result⟩, belongs, same⟩ := List.mem_map.mp present
  cases same
  have walk := result.walk
  rw [native_representative revision selected header] at walk
  exact ⟨result.trace, walk⟩

def Checked.lower (value : Checked contract revision) (selected : Case) (member : selected ∈ contract.cases)
    (header : Header) (accepted : selected.selector.accepts header = true) :
    Refinement (contract.mustModel selected) (revision.native selected header) where
  project := revision.anchor
  simulate source target edge := by
    have present : (⟨source, target⟩ : Arc) ∈ selected.must := by
      simpa only [Contract.mustModel, Certificate.finiteNetwork, arcs, List.contains_iff_mem] using edge.2.2
    obtain ⟨trace, walk⟩ := value.path selected member header accepted ⟨source, target⟩ present
    exact walk.reachable

@[simp] theorem Checked.upper_project (value : Checked contract revision) (selected : Case)
    (member : selected ∈ contract.cases) (header : Header) (accepted : selected.selector.accepts header = true) :
    (value.upper selected member header accepted).project = revision.project := rfl

@[simp] theorem Checked.lower_project (value : Checked contract revision) (selected : Case)
    (member : selected ∈ contract.cases) (header : Header) (accepted : selected.selector.accepts header = true) :
    (value.lower selected member header accepted).project = revision.anchor := rfl

structure Provenance (value : Checked contract revision) (selected : Case) (header : Header) (arc : Arc) where
  caseResult : CaseResult contract revision selected
  caseStored : ⟨selected, caseResult⟩ ∈ value.results
  cell : Cell contract revision selected ((partition revision selected).representative header)
  cellStored : ⟨(partition revision selected).representative header, cell⟩ ∈ caseResult.cells
  path : Path revision selected ((partition revision selected).representative header) arc
  pathStored : ⟨arc, path⟩ ∈ cell.paths
  walk : Network.Walk (revision.native selected header)
    (revision.anchor arc.source) (revision.anchor arc.target) path.trace

theorem Checked.provenance (value : Checked contract revision) (selected : Case) (member : selected ∈ contract.cases)
    (header : Header) (accepted : selected.selector.accepts header = true) (arc : Arc) (present : arc ∈ selected.must) :
    Nonempty (Provenance value selected header arc) := by
  rw [← value.covered] at member
  obtain ⟨⟨actualCase, caseResult⟩, caseStored, same⟩ := List.mem_map.mp member
  dsimp only at same
  subst actualCase
  have selectedCell : (partition revision selected).representative header ∈ headers revision selected := by
    apply List.mem_filter.mpr
    refine ⟨(partition revision selected).representative_mem header, ?_⟩
    rw [(partition revision selected).match_stable selected.selector
      (revision.snapshot.compile.trafficPartition_selected selected.selector) header]
    exact accepted
  rw [← caseResult.covered] at selectedCell
  obtain ⟨⟨actualHeader, cell⟩, cellStored, same⟩ := List.mem_map.mp selectedCell
  dsimp only at same
  subst actualHeader
  rw [← cell.covered] at present
  obtain ⟨⟨actualArc, path⟩, pathStored, same⟩ := List.mem_map.mp present
  dsimp only at same
  subst actualArc
  have walk := path.walk
  rw [native_representative revision selected header] at walk
  exact ⟨⟨caseResult, caseStored, cell, cellStored, path, pathStored, walk⟩⟩

end Netlib.Federation.Native
