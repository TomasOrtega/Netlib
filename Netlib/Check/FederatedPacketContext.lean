import Netlib.Model.FederatedPacket

namespace Netlib.Federation.InFlight

variable {input : Input}

private def verify (condition : Prop) [Decidable condition] (message : String) :
    Except String (PLift condition) :=
  if accepted : condition then .ok ⟨accepted⟩ else .error message

namespace Fences

def beforeCursor (plan : Plan) (operation : plan.Operation) : plan.Cursor :=
  ⟨operation.val, by simp only [Plan.versions, List.length_cons]; omega⟩

def before (plan : Plan) (operation : plan.Operation) : Revision :=
  plan.revisionAt (beforeCursor plan operation)

def hazardBool (before after : Revision) (node : String) : Bool :=
  decide (node ∉ after.snapshot.intent.ids ∨ before.project node ≠ after.project node)

def namesAt (fences : List (List String)) (index : Nat) : List String :=
  (fences[index]?).getD []

private def rowCheck (before after : Revision) (names : List String) : Bool :=
  decide names.Nodup && names.all (fun node => decide (node ∈ before.snapshot.intent.ids)) &&
    before.snapshot.intent.ids.all (fun node => decide (hazardBool before after node = true → node ∈ names))

private def atCheck (plan : Plan) (fences : List (List String)) (index : Nat) : Bool :=
  match plan.versions[index]?, plan.updates[index]?, fences[index]? with
  | some before, some after, some names => rowCheck before after names
  | _, _, _ => false

structure RowValidated (before after : Revision) (names : List String) : Prop where
  unique : names.Nodup
  known : ∀ node ∈ names, node ∈ before.snapshot.intent.ids
  covered : ∀ node ∈ before.snapshot.intent.ids, hazardBool before after node = true → node ∈ names

theorem RowValidated.retained {before after : Revision} {names : List String}
    (value : RowValidated before after names) (node : String)
    (known : node ∈ before.snapshot.intent.ids) (clear : node ∉ names) :
    node ∈ after.snapshot.intent.ids ∧ before.project node = after.project node := by
  have safe : hazardBool before after node = false := by
    cases checked : hazardBool before after node with
    | false => rfl
    | true => exact False.elim (clear (value.covered node known checked))
  simpa [hazardBool] using safe

structure Validated (plan : Plan) (fences : List (List String)) : Prop where
  length : fences.length = plan.updates.length
  checks : ∀ index ∈ List.range plan.updates.length, atCheck plan fences index = true

def check (plan : Plan) (fences : List (List String)) : Except String (PLift (Validated plan fences)) := do
  let length ← verify (fences.length = plan.updates.length)
    s!"Operator {plan.contract.id}: fence count does not match the update count."
  let checked ← verify ((List.range plan.updates.length).all (atCheck plan fences) = true)
    s!"Operator {plan.contract.id}: a fence is duplicated, unknown before its update, or omits a changed node."
  return ⟨length.down, List.all_eq_true.mp checked.down⟩

theorem Validated.row (value : Validated plan fences) (operation : plan.Operation) :
    RowValidated (before plan operation) (plan.update operation) (namesAt fences operation.val) := by
  have checked := value.checks operation.val (List.mem_range.mpr operation.isLt)
  have beforeFound : plan.versions[operation.val]? = some (before plan operation) :=
    List.getElem?_eq_some_iff.mpr ⟨(beforeCursor plan operation).isLt, rfl⟩
  have afterFound : plan.updates[operation.val]? = some (plan.update operation) :=
    List.getElem?_eq_some_iff.mpr ⟨operation.isLt, rfl⟩
  have available : operation.val < fences.length := by rw [value.length]; exact operation.isLt
  have namesFound : fences[operation.val]? = some fences[operation.val] :=
    List.getElem?_eq_some_iff.mpr ⟨available, rfl⟩
  simp only [atCheck, beforeFound, afterFound, namesFound, rowCheck, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true] at checked
  simpa only [namesAt, namesFound, Option.getD_some] using
    (show RowValidated (before plan operation) (plan.update operation) fences[operation.val] from
      ⟨checked.1.1, checked.1.2, checked.2⟩)

end Fences

structure FixedAnchors (plan : Plan) : Prop where
  anchors : ∀ revision ∈ plan.versions, ∀ node ∈ plan.contract.nodes,
    fixedRole node.role = true → revision.anchor node.id = plan.initial.anchor node.id

private def checkFixed (plan : Plan) : Except String (PLift (FixedAnchors plan)) := do
  let checked ← verify (plan.versions.all (fun revision => plan.contract.nodes.all (fun node =>
    decide (fixedRole node.role = true → revision.anchor node.id = plan.initial.anchor node.id))) = true)
    s!"Operator {plan.contract.id}: an endpoint, ingress, or egress anchor changes across revisions."
  return ⟨⟨by simpa only [List.all_eq_true, decide_eq_true_eq] using checked.down⟩⟩

namespace Context

structure Validated (deployment : Deployment.Checked input) (context : Context input) where
  result : Queries.Result input.left.contract input.right.contract input.intent context.query
  stored : ⟨context.query, result⟩ ∈ deployment.queries.results
  firstEq : context.first = result.first
  secondEq : context.second = result.second
  profileID : context.query.id = context.profile.queryID
  reach : context.query.kind = .reach
  packetID : context.profile.packetID ≠ ""
  leftFences : Fences.Validated input.left context.profile.leftFences
  rightFences : Fences.Validated input.right context.profile.rightFences
  leftFixed : FixedAnchors input.left
  rightFixed : FixedAnchors input.right

variable {deployment : Deployment.Checked input} {context : Context input}

structure Selection (deployment : Deployment.Checked input) (profile : Profile) where
  context : Context input
  validated : Validated deployment context
  profileEq : context.profile = profile

def select (deployment : Deployment.Checked input) (profile : Profile) :
    Except String (Selection deployment profile) := do
  let packetID ← verify (profile.packetID ≠ "") "The in-flight packet identity is empty."
  match found : deployment.queries.results.find? (fun entry => entry.1.id == profile.queryID) with
  | none => throw s!"Unknown stored in-flight query: {profile.queryID}."
  | some ⟨query, result⟩ =>
    let reach ← verify (query.kind = .reach) "An in-flight profile must select a reachability query."
    let leftFences ← Fences.check input.left profile.leftFences
    let rightFences ← Fences.check input.right profile.rightFences
    let leftFixed ← checkFixed input.left
    let rightFixed ← checkFixed input.right
    let context : Context input := ⟨profile, query, result.first, result.second⟩
    return ⟨context, ⟨result, List.mem_of_find?_eq_some found, rfl, rfl,
      (by simpa using List.find?_some found), reach.down, packetID.down,
      leftFences.down, rightFences.down, leftFixed.down, rightFixed.down⟩, rfl⟩

theorem Validated.query_member (value : Validated deployment context) : context.query ∈ input.intent.queries := by
  rw [← deployment.covered]
  exact List.mem_map.mpr ⟨⟨context.query, value.result⟩, value.stored, rfl⟩

theorem Validated.first_mem (value : Validated deployment context) : context.first ∈ input.left.contract.cases := by
  rw [value.firstEq]
  exact List.mem_of_find?_eq_some value.result.firstFound

theorem Validated.second_mem (value : Validated deployment context) : context.second ∈ input.right.contract.cases := by
  rw [value.secondEq]
  exact List.mem_of_find?_eq_some value.result.secondFound

theorem Validated.matches (value : Validated deployment context) : Compatibility.Matches context.first context.second := by
  rw [value.firstEq, value.secondEq]
  exact value.result.agreement

private theorem reference_mem (atRole : Queries.AtRole left right reference role) :
    reference ∈ references left right := by
  rcases reference with ⟨side, node⟩
  cases side with
  | left => exact (Composition.reference_left left right node).mpr atRole.known
  | right => exact (Composition.reference_right left right node).mpr atRole.known

theorem Validated.anchor_fixed (value : Validated deployment context)
    (atRole : Queries.AtRole input.left.contract input.right.contract reference role)
    (fixed : fixedRole role = true) (current : Cursors input) :
    Composition.anchor (input.left.revisionAt current.1) (input.right.revisionAt current.2) reference =
      Composition.anchor input.left.initial input.right.initial reference := by
  rcases reference with ⟨side, node⟩
  cases side with
  | left =>
    have member := List.mem_of_find?_eq_some atRole.found
    have selected : atRole.node.id = node := beq_iff_eq.mp
      (List.find?_some (p := fun candidate : PublicNode => candidate.id == node) atRole.found)
    have same := value.leftFixed.anchors _ (input.left.at_mem current.1) _ member (by rw [atRole.roleEq]; exact fixed)
    simp only [Composition.anchor, ← selected, same]
  | right =>
    have member := List.mem_of_find?_eq_some atRole.found
    have selected : atRole.node.id = node := beq_iff_eq.mp
      (List.find?_some (p := fun candidate : PublicNode => candidate.id == node) atRole.found)
    have same := value.rightFixed.anchors _ (input.right.at_mem current.2) _ member (by rw [atRole.roleEq]; exact fixed)
    simp only [Composition.anchor, ← selected, same]

theorem Validated.anchor_known_at (value : Validated deployment context)
    (atRole : Queries.AtRole input.left.contract input.right.contract reference role)
    (fixed : fixedRole role = true) (current : Cursors input) :
    Composition.Known (input.left.revisionAt current.1) (input.right.revisionAt current.2)
      (Composition.anchor input.left.initial input.right.initial reference) := by
  rw [← value.anchor_fixed atRole fixed current]
  exact Composition.anchor_known (deployment.left.nativeAt current.1) (deployment.right.nativeAt current.2)
    reference (reference_mem atRole)

theorem Validated.anchor_project_at (value : Validated deployment context)
    (atRole : Queries.AtRole input.left.contract input.right.contract reference role)
    (fixed : fixedRole role = true) (current : Cursors input) :
    Composition.project (input.left.revisionAt current.1) (input.right.revisionAt current.2)
      (Composition.anchor input.left.initial input.right.initial reference) = reference := by
  rw [← value.anchor_fixed atRole fixed current]
  exact Composition.anchor_project (deployment.left.nativeAt current.1) (deployment.right.nativeAt current.2)
    reference (reference_mem atRole)

theorem Validated.sourceNode_known (value : Validated deployment context) (current : Cursors input) :
    Composition.Known (input.left.revisionAt current.1) (input.right.revisionAt current.2) context.sourceNode :=
  value.anchor_known_at value.result.validated.source rfl current

theorem Validated.targetNode_known (value : Validated deployment context) (current : Cursors input) :
    Composition.Known (input.left.revisionAt current.1) (input.right.revisionAt current.2) context.targetNode :=
  value.anchor_known_at value.result.validated.target rfl current

theorem Validated.sourceNode_project (value : Validated deployment context) (current : Cursors input) :
    Composition.project (input.left.revisionAt current.1) (input.right.revisionAt current.2) context.sourceNode =
      context.query.source :=
  value.anchor_project_at value.result.validated.source rfl current

theorem Validated.targetNode_project (value : Validated deployment context) (current : Cursors input) :
    Composition.project (input.left.revisionAt current.1) (input.right.revisionAt current.2) context.targetNode =
      context.query.target :=
  value.anchor_project_at value.result.validated.target rfl current

end Context
end Netlib.Federation.InFlight
