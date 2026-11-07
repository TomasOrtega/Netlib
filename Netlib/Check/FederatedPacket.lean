import Netlib.Check.FederatedPacketContext
import Netlib.Check.FederatedPacketControlStability
import Netlib.Check.FederatedPacketGraph

/-!
# Checked progress for every selected packet class

Graph generation and rank analysis have separate aggregate guards. Header
lookup reuses a stored representative's exact table and computed ranks.
-/

namespace Netlib.Federation.InFlight

namespace Rank
export Theory.FiniteProgressRank (Checked Limits)
end Rank

private def contractRows (contract : Contract) : Nat :=
  1 + contract.nodes.length + contract.cases.foldl (fun count selected =>
    count + 1 + selected.upper.length + selected.must.length) 0

def rawRows (input : Input) (profile : Profile) : Nat :=
  let revisions := input.left.versions ++ input.right.versions
  1 + contractRows input.left.contract + contractRows input.right.contract +
    revisions.foldl (fun count revision => count + 1 + Native.nativeRows revision +
      revision.projection.length + revision.anchors.length) 0 +
    input.intent.borders.foldl (fun count border => count + 1 + border.cases.length) 0 +
    input.intent.queries.foldl (fun count query => count + 1 + query.gateways.length) 0 +
    profile.leftFences.foldl (fun count names => count + 1 + names.length) 0 +
    profile.rightFences.foldl (fun count names => count + 1 + names.length) 0

def contextWork (input : Input) (profile : Profile) : Nat := (rawRows input profile) ^ 2

def generationWork (context : Context input) : Nat :=
  Graph.generationWork context * JointPartition.selectedCount input context.first

def graphLimits (context : Context input) : Rank.Limits :=
  let states := Graph.universeSize input
  ⟨states, states * ((Control.nodes input).length + 5), context.profile.work⟩

structure RankedCell (context : Context input) (header : Packet.Header) where
  graph : Graph.Indexed context header
  ranked : Rank.Checked graph.table

def rankWork (cells : List ((header : Packet.Header) × RankedCell context header)) : Nat :=
  (cells.map (fun entry => entry.2.graph.rankWork)).sum

structure Certified (input : Input) (profile : Profile) where
  deployment : Deployment.Checked input
  context : Context input
  valid : Context.Validated deployment context
  profileEq : context.profile = profile
  cells : List ((header : Packet.Header) × RankedCell context header)
  covered : cells.map Sigma.fst = JointPartition.selectedHeaders input context.first
  selectedWithin : JointPartition.selectedCount input context.first ≤ profile.cells
  rawWithin : contextWork input profile ≤ profile.work
  generationWithin : Deployment.workEstimate input + contextWork input profile + generationWork context ≤ profile.work
  totalWork : Nat
  totalWorkEq : totalWork = Deployment.workEstimate input + contextWork input profile + generationWork context + rankWork cells
  workWithin : totalWork ≤ profile.work

private def buildGraphs (context : Context input) : (headers : List Packet.Header) →
    Except String { values : List ((header : Packet.Header) × Graph.Indexed context header) //
      values.map Sigma.fst = headers }
  | [] => return ⟨[], rfl⟩
  | header :: rest => do
    let graph ← Graph.build context header (graphLimits context)
    let tail ← buildGraphs context rest
    return ⟨⟨header, graph⟩ :: tail.val, by simp only [List.map_cons, tail.property]⟩

private def graphsRankWork (graphs : List ((header : Packet.Header) × Graph.Indexed context header)) : Nat :=
  (graphs.map (fun entry => entry.2.rankWork)).sum

private def analyzeGraphs (context : Context input) :
    (graphs : List ((header : Packet.Header) × Graph.Indexed context header)) →
    Except String { values : List ((header : Packet.Header) × RankedCell context header) //
      values.map Sigma.fst = graphs.map Sigma.fst ∧ rankWork values = graphsRankWork graphs }
  | [] => return ⟨[], by simp [rankWork, graphsRankWork]⟩
  | ⟨header, graph⟩ :: rest => do
    let ranked ← graph.analyze (graphLimits context)
    let tail ← analyzeGraphs context rest
    return ⟨⟨header, ⟨graph, ranked⟩⟩ :: tail.val, by
      constructor
      · simp only [List.map_cons, tail.property.1]
      · simpa only [rankWork, graphsRankWork, List.map_cons, List.sum_cons] using
          congrArg (graph.rankWork + ·) tail.property.2⟩

def certify (input : Input) (profile : Profile) : Except String (Certified input profile) := do
  if rawWithin : contextWork input profile ≤ profile.work then
    let base := Deployment.workEstimate input
    if base + contextWork input profile > profile.work then
      throw s!"Native deployment and packet context estimates exceed budget {profile.work}."
    let deployment ← Deployment.certify input
    let selection ← Context.select deployment profile
    let context := selection.context
    if selectedWithin : JointPartition.selectedCount input context.first ≤ profile.cells then
      if generationWithin : base + contextWork input profile + generationWork context ≤ profile.work then
        let graphs ← buildGraphs context (JointPartition.selectedHeaders input context.first)
        let total := base + contextWork input profile + generationWork context + graphsRankWork graphs.val
        if within : total ≤ profile.work then
          let cells ← analyzeGraphs context graphs.val
          return ⟨deployment, context, selection.validated, selection.profileEq, cells.val,
            cells.property.1.trans graphs.property, selectedWithin, rawWithin, generationWithin,
            total, by simp only [total, base, cells.property.2], within⟩
        else throw s!"Complete packet graph and rank estimate {total} exceeds budget {profile.work}."
      else throw s!"Complete packet successor generation estimate exceeds budget {profile.work}."
    else throw s!"Selected packet classes {JointPartition.selectedCount input context.first} exceed budget {profile.cells}."
  else throw s!"Raw packet context estimate {contextWork input profile} exceeds budget {profile.work}."

variable {input : Input} {profile : Profile} {context : Context input}

private def storedCell (values : List ((header : Packet.Header) × RankedCell context header))
    (header : Packet.Header) (member : header ∈ values.map Sigma.fst) :
    { value : RankedCell context header // ⟨header, value⟩ ∈ values } :=
  match values with
  | [] => False.elim (by simp at member)
  | ⟨actual, cell⟩ :: rest =>
    if same : actual = header then
      same ▸ ⟨cell, List.mem_cons_self⟩
    else
      let tail := storedCell rest header (by
        simpa only [List.map_cons, List.mem_cons, Ne.symm same, false_or] using member)
      ⟨tail.val, List.mem_cons_of_mem _ tail.property⟩

def Certified.representativeCell (value : Certified input profile) (header : Packet.Header)
    (accepted : value.context.first.selector.accepts header = true) :
    RankedCell value.context ((JointPartition.partition input value.context.first).representative header) :=
  (storedCell value.cells _ (by
    rw [value.covered]
    exact JointPartition.selected_representative_mem input value.context.first header accepted)).val

theorem Certified.representativeCell_stored (value : Certified input profile) (header : Packet.Header)
    (accepted : value.context.first.selector.accepts header = true) :
    ⟨(JointPartition.partition input value.context.first).representative header,
      value.representativeCell header accepted⟩ ∈ value.cells :=
  (storedCell value.cells _ (by
    rw [value.covered]
    exact JointPartition.selected_representative_mem input value.context.first header accepted)).property

def RankedCell.transport (value : RankedCell context representative) (header : Packet.Header)
    (same : ∀ key, Control.successors context representative key = Control.successors context header key) :
    RankedCell context header :=
  let graph : Graph.Indexed context header := { value.graph with
    rowsExact := fun index => (value.graph.rowsExact index).trans (same _) }
  ⟨graph, value.ranked⟩

def Certified.cellAt (value : Certified input profile) (header : Packet.Header)
    (accepted : value.context.first.selector.accepts header = true) : RankedCell value.context header :=
  (value.representativeCell header accepted).transport header
    (Control.successors_representative value.context header)

theorem Certified.cellAt_table (value : Certified input profile) (header : Packet.Header)
    (accepted : value.context.first.selector.accepts header = true) :
    (value.cellAt header accepted).graph.table = (value.representativeCell header accepted).graph.table := rfl

theorem Certified.cellAt_ranked (value : Certified input profile) (header : Packet.Header)
    (accepted : value.context.first.selector.accepts header = true) :
    (value.cellAt header accepted).ranked = (value.representativeCell header accepted).ranked := rfl

end Netlib.Federation.InFlight
