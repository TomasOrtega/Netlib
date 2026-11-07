import Netlib.Model.DomainContract

/-!
# Public names and private native anchors

Projection and anchor checks refer to the actual imported inventory.
An egress anchor is a native terminal with no outgoing bindings.
-/

namespace Netlib.Federation

variable {contract : Contract} {revision : Revision}

private def verify (condition : Prop) [Decidable condition] (message : String) :
    Except String { _value : Unit // condition } :=
  if accepted : condition then .ok ⟨(), accepted⟩ else .error message

def canonicalPrefix (block : Packet.Prefix) : Bool :=
  decide (block.address.val % block.width = 0)

def canonicalSelector (selector : Packet.Match) : Bool :=
  selector.source.all canonicalPrefix && selector.destination.all canonicalPrefix &&
    selector.sourcePorts.all (fun range => decide (range.first ≤ range.last)) &&
    selector.destinationPorts.all (fun range => decide (range.first ≤ range.last))

def Case.valid (contract : Contract) (selected : Case) : Bool :=
  !selected.id.isEmpty && canonicalSelector selected.selector &&
    decide selected.upper.Nodup && decide selected.must.Nodup &&
    selected.upper.all (fun arc => decide (arc.source ∈ contract.ids ∧ arc.target ∈ contract.ids)) &&
    selected.must.all (fun arc => decide (arc.source ∈ contract.ids ∧ arc.target ∈ contract.ids))

structure Contract.Validated (contract : Contract) : Prop where
  named : contract.id ≠ ""
  positive : 0 < contract.version
  nonempty : contract.nodes ≠ []
  unique : contract.ids.Nodup
  nodeNames : ∀ node ∈ contract.nodes, node.id ≠ ""
  casesNonempty : contract.cases ≠ []
  casesUnique : (contract.cases.map (·.id)).Nodup
  cases : ∀ selected ∈ contract.cases, selected.valid contract = true

theorem Contract.Validated.upper_nodes (valid : contract.Validated) (selected : Case)
    (member : selected ∈ contract.cases) (arc : Arc) (present : arc ∈ selected.upper) :
    arc.source ∈ contract.ids ∧ arc.target ∈ contract.ids := by
  have checks := valid.cases selected member
  simp only [Case.valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at checks
  exact checks.1.2 arc present

theorem Contract.Validated.must_nodes (valid : contract.Validated) (selected : Case)
    (member : selected ∈ contract.cases) (arc : Arc) (present : arc ∈ selected.must) :
    arc.source ∈ contract.ids ∧ arc.target ∈ contract.ids := by
  have checks := valid.cases selected member
  simp only [Case.valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at checks
  exact checks.2 arc present

def Contract.check (contract : Contract) : Except String { _value : Unit // contract.Validated } := do
  let named ← verify (contract.id ≠ "") "The contract identity is empty."
  let positive ← verify (0 < contract.version) "The contract version must be positive."
  let nonempty ← verify (contract.nodes ≠ []) "The public node inventory is empty."
  let unique ← verify contract.ids.Nodup "Public node identities must be unique."
  let nodeNames ← verify (contract.nodes.all (fun node => decide (node.id ≠ "")) = true)
    "A public node identity is empty."
  let casesNonempty ← verify (contract.cases.isEmpty = false) "The contract has no traffic case."
  let casesUnique ← verify (contract.cases.map (·.id)).Nodup "Public case identities must be unique."
  let cases ← verify (contract.cases.all (·.valid contract) = true)
    "A case has an empty identity, noncanonical selector, duplicate arc, or unknown endpoint."
  return ⟨(), named.property, positive.property, nonempty.property, unique.property,
    (by simpa only [List.all_eq_true, decide_eq_true_eq] using nodeNames.property),
    (by intro empty; have absent := casesNonempty.property; simp only [empty, List.isEmpty_nil, Bool.true_eq_false] at absent), casesUnique.property, List.all_eq_true.mp cases.property⟩

def Revision.terminal (revision : Revision) (publicNode : String) : Bool :=
  match revision.snapshot.router? (revision.anchor publicNode) with
  | none => false
  | some router => router.bindings.isEmpty

structure Revision.Validated (contract : Contract) (revision : Revision) : Prop where
  publicValid : contract.Validated
  named : revision.id ≠ ""
  sourceValid : revision.snapshot.compile.validate = .ok ()
  projectionUnique : (revision.projection.map (·.localNode)).Nodup
  projectionRows : ∀ row ∈ revision.projection,
    row.localNode ∈ revision.snapshot.intent.ids ∧ row.publicNode ∈ contract.ids
  projectionCoverage : ∀ localNode ∈ revision.snapshot.intent.ids,
    localNode ∈ revision.projection.map (·.localNode)
  projectMember : ∀ localNode ∈ revision.snapshot.intent.ids, revision.project localNode ∈ contract.ids
  anchorsUnique : (revision.anchors.map (·.publicNode)).Nodup
  anchorRows : ∀ row ∈ revision.anchors,
    row.publicNode ∈ contract.ids ∧ row.localNode ∈ revision.snapshot.intent.ids
  anchorMember : ∀ publicNode ∈ contract.ids, revision.anchor publicNode ∈ revision.snapshot.intent.ids
  anchorProject : ∀ publicNode ∈ contract.ids, revision.project (revision.anchor publicNode) = publicNode
  enforcement : ∀ localNode ∈ revision.snapshot.intent.ids, ∀ node ∈ contract.nodes,
    revision.project localNode = node.id → node.role = .enforcement →
      localNode ∈ revision.snapshot.intent.select revision.snapshot.intent.enforcement
  terminals : ∀ node ∈ contract.nodes, node.role = .egress → revision.terminal node.id = true
  requests : ∀ selected ∈ contract.cases,
    ∃ request ∈ revision.snapshot.intent.requests, request.value = selected.request

theorem Revision.Validated.terminal_router (valid : Revision.Validated contract revision) (node : PublicNode)
    (member : node ∈ contract.nodes) (role : node.role = .egress) :
    ∃ router, revision.snapshot.router? (revision.anchor node.id) = some router ∧ router.bindings = [] := by
  have checked := valid.terminals node member role
  unfold Revision.terminal at checked
  split at checked
  · cases checked
  · exact ⟨_, by assumption, List.isEmpty_iff.mp checked⟩

theorem Revision.Validated.egress_native (valid : Revision.Validated contract revision) (node : PublicNode)
    (member : node ∈ contract.nodes) (role : node.role = .egress)
    (header : Packet.Header) (request : ZeroTrust.Request String String String) (target : String) :
    revision.snapshot.nativeEdge header request (revision.anchor node.id) target = false := by
  obtain ⟨router, found, empty⟩ := valid.terminal_router node member role
  simp only [Import.LinuxDeployment.Snapshot.nativeEdge, found]
  simp only [Import.LinuxDeployment.Router.adjacent, empty,
    List.any_nil, Bool.false_and]

def Revision.check (contract : Contract) (revision : Revision) :
    Except String { _value : Unit // Revision.Validated contract revision } := do
  let contractValid ← contract.check
  let named ← verify (revision.id ≠ "") "The native revision identity is empty."
  match sourceValid : revision.snapshot.compile.validate with
  | .error reason => throw reason
  | .ok () =>
    let projectionUnique ← verify (revision.projection.map (·.localNode)).Nodup
      "Each native node needs one projection."
    let projectionRows ← verify (revision.projection.all (fun row =>
      decide (row.localNode ∈ revision.snapshot.intent.ids ∧ row.publicNode ∈ contract.ids)) = true)
      "A projection refers to an unknown native or public node."
    let projectionCoverage ← verify (revision.snapshot.intent.ids.all (fun node =>
      decide (node ∈ revision.projection.map (·.localNode))) = true) "A native node has no projection."
    let projectMember ← verify (revision.snapshot.intent.ids.all (fun node => decide (revision.project node ∈ contract.ids)) = true)
      "A native projection does not resolve to a public node."
    let anchorsUnique ← verify (revision.anchors.map (·.publicNode)).Nodup
      "Each public node needs one native anchor."
    let anchorRows ← verify (revision.anchors.all (fun row =>
      decide (row.publicNode ∈ contract.ids ∧ row.localNode ∈ revision.snapshot.intent.ids)) = true)
      "An anchor refers to an unknown public or native node."
    let anchorFacts ← verify (contract.ids.all (fun node =>
      decide (revision.anchor node ∈ revision.snapshot.intent.ids ∧ revision.project (revision.anchor node) = node)) = true)
      "A public anchor is absent or projects to another public node."
    let enforcement ← verify (revision.snapshot.intent.ids.all (fun localNode => contract.nodes.all (fun node =>
      decide (revision.project localNode = node.id → node.role = .enforcement →
        localNode ∈ revision.snapshot.intent.select revision.snapshot.intent.enforcement))) = true)
      "A public enforcement role has a native preimage outside the actual enforcement selector."
    let terminals ← verify (contract.nodes.all (fun node =>
      if node.role = .egress then revision.terminal node.id else true) = true)
      "An egress anchor is not a native terminal."
    let requests ← verify (contract.cases.all (fun selected => revision.snapshot.intent.requests.any
      (fun request => decide (request.value = selected.request))) = true)
      "A public case request triple is absent from the native revision."
    have anchors : ∀ node ∈ contract.ids, revision.anchor node ∈ revision.snapshot.intent.ids ∧
        revision.project (revision.anchor node) = node := by
      simpa only [List.all_eq_true, decide_eq_true_eq] using anchorFacts.property
    return ⟨(), contractValid.property, named.property, sourceValid, projectionUnique.property,
      (by simpa only [List.all_eq_true, decide_eq_true_eq] using projectionRows.property),
      (by simpa only [List.all_eq_true, decide_eq_true_eq] using projectionCoverage.property),
      (by simpa only [List.all_eq_true, decide_eq_true_eq] using projectMember.property),
      anchorsUnique.property,
      (by simpa only [List.all_eq_true, decide_eq_true_eq] using anchorRows.property),
      (fun node member => (anchors node member).1), (fun node member => (anchors node member).2),
      (by simpa only [List.all_eq_true, decide_eq_true_eq] using enforcement.property),
      (by
        intro node member role
        have checked := List.all_eq_true.mp terminals.property node member
        simpa only [role, ite_true] using checked),
      (by simpa only [List.all_eq_true, List.any_eq_true, decide_eq_true_eq] using requests.property)⟩

end Netlib.Federation
