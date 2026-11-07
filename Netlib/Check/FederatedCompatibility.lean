import Netlib.Model.DomainContract

/-!
# Checked public border compatibility

Directional borders name both contract versions and exact public cases.
Native routing remains private to each separately checked revision.
-/

namespace Netlib.Federation.Compatibility

def Matches (first second : Case) : Prop :=
  first.id = second.id ∧ first.selector = second.selector ∧
    first.request.principal = second.request.principal ∧
    first.request.resource = second.request.resource ∧ first.request.operation = second.request.operation

instance (first second : Case) : Decidable (Matches first second) := by
  unfold Matches
  infer_instance

theorem Matches.request_eq (value : Matches first second) : first.request = second.request := by
  have principal := value.2.2.1
  have resource := value.2.2.2.1
  have operation := value.2.2.2.2
  cases one : first.request
  cases two : second.request
  simp_all

structure CaseChecked (first : Case) (other : Contract) where
  selected : Case
  found : other.case? first.id = some selected
  agreement : Matches first selected

private def verify (property : Prop) [Decidable property] (message : String) : Except String (PLift property) :=
  if checked : property then .ok ⟨checked⟩ else .error message

private def checkCase (first : Case) (other : Contract) : Except String (CaseChecked first other) := do
  match found : other.case? first.id with
  | none => throw s!"Unknown peer case: {first.id}."
  | some selected =>
    let matched ← verify (Matches first selected) s!"Peer case differs in selector or request: {first.id}."
    return ⟨selected, found, matched.down⟩

private def checkCases (other : Contract) : (cases : List Case) →
    Except String (PLift (∀ first ∈ cases, ∃ second, other.case? first.id = some second ∧ Matches first second))
  | [] => .ok ⟨by simp⟩
  | first :: rest => do
    let checked ← checkCase first other
    let later ← checkCases other rest
    return ⟨by
      intro selected member
      rcases List.mem_cons.mp member with same | member
      · subst selected
        exact ⟨checked.selected, checked.found, checked.agreement⟩
      · exact later.down selected member⟩

private def knownCase (left right : Contract) (id : String) : Bool :=
  match left.case? id, right.case? id with
  | some first, some second => decide (Matches first second)
  | _, _ => false

private theorem knownCase_sound (left right : Contract) (id : String) (checked : knownCase left right id = true) :
    ∃ first second, left.case? id = some first ∧ right.case? id = some second ∧ Matches first second := by
  unfold knownCase at checked
  split at checked
  · rename_i first second leftFound rightFound
    exact ⟨first, second, leftFound, rightFound, of_decide_eq_true checked⟩
  · cases checked

structure BorderChecked (left right : Contract) (border : Border) where
  opposite : border.source.side ≠ border.target.side
  sourceDomain : border.sourceDomain = (contracts left right border.source.side).id
  targetDomain : border.targetDomain = (contracts left right border.target.side).id
  sourceVersion : border.sourceVersion = (contracts left right border.source.side).version
  targetVersion : border.targetVersion = (contracts left right border.target.side).version
  sourceNode : PublicNode
  sourceFound : (contracts left right border.source.side).node? border.source.node = some sourceNode
  sourceRole : sourceNode.role = .egress
  targetNode : PublicNode
  targetFound : (contracts left right border.target.side).node? border.target.node = some targetNode
  targetRole : targetNode.role = .ingress
  nonempty : border.cases ≠ []
  knownCases : ∀ id ∈ border.cases, ∃ first second,
    left.case? id = some first ∧ right.case? id = some second ∧ Matches first second

theorem nodeFound_known (contract : Contract) (id : String) (node : PublicNode)
    (found : contract.node? id = some node) : id ∈ contract.ids := by
  have member := List.mem_of_find?_eq_some found
  have selected : node.id = id := beq_iff_eq.mp
    (List.find?_some (p := fun candidate : PublicNode => candidate.id == id) found)
  exact List.mem_map.mpr ⟨node, member, selected⟩

theorem BorderChecked.source_known (value : BorderChecked left right border) :
    border.source.node ∈ (contracts left right border.source.side).ids :=
  nodeFound_known _ _ value.sourceNode value.sourceFound

theorem BorderChecked.target_known (value : BorderChecked left right border) :
    border.target.node ∈ (contracts left right border.target.side).ids :=
  nodeFound_known _ _ value.targetNode value.targetFound

private def checkBorder (left right : Contract) (border : Border) : Except String (BorderChecked left right border) := do
  let opposite ← verify (border.source.side ≠ border.target.side) "A border must cross two different operators."
  let sourceDomain ← verify (border.sourceDomain = (contracts left right border.source.side).id)
    "The border source domain differs from its selected contract."
  let targetDomain ← verify (border.targetDomain = (contracts left right border.target.side).id)
    "The border target domain differs from its selected contract."
  let sourceVersion ← verify (border.sourceVersion = (contracts left right border.source.side).version)
    "The border source contract version is stale."
  let targetVersion ← verify (border.targetVersion = (contracts left right border.target.side).version)
    "The border target contract version is stale."
  match sourceFound : (contracts left right border.source.side).node? border.source.node with
  | none => throw "The border source public node is undeclared."
  | some sourceNode =>
    let sourceRole ← verify (sourceNode.role = .egress) "The border source must be an egress port."
    match targetFound : (contracts left right border.target.side).node? border.target.node with
    | none => throw "The border target public node is undeclared."
    | some targetNode =>
      let targetRole ← verify (targetNode.role = .ingress) "The border target must be an ingress port."
      let nonempty ← verify (border.cases ≠ []) "A border must declare at least one packet case."
      let known ← verify (border.cases.all (knownCase left right) = true)
        "A border names an unknown or mismatched peer case."
      return ⟨opposite.down, sourceDomain.down, targetDomain.down, sourceVersion.down, targetVersion.down,
        sourceNode, sourceFound, sourceRole.down, targetNode, targetFound, targetRole.down, nonempty.down,
        fun id member => knownCase_sound left right id (List.all_eq_true.mp known.down id member)⟩

private def checkBorders (left right : Contract) (index : Nat) : (borders : List Border) →
    Except String (PLift (∀ border ∈ borders, Nonempty (BorderChecked left right border)))
  | [] => .ok ⟨by simp⟩
  | border :: rest => do
    let checked ← (checkBorder left right border).mapError
      (fun reason => s!"Border {index} ({repr border.source} -> {repr border.target}): {reason}")
    let later ← checkBorders left right (index + 1) rest
    return ⟨by
      intro selected member
      rcases List.mem_cons.mp member with same | member
      · subst selected
        exact ⟨checked⟩
      · exact later.down selected member⟩

structure Compatible (left right : Contract) (intent : Intent) : Type where
  leftNonempty : left.id ≠ ""
  rightNonempty : right.id ≠ ""
  distinct : left.id ≠ right.id
  forward : ∀ first ∈ left.cases, ∃ second, right.case? first.id = some second ∧ Matches first second
  backward : ∀ second ∈ right.cases, ∃ first, left.case? second.id = some first ∧ Matches second first
  borders : ∀ border ∈ intent.borders, Nonempty (BorderChecked left right border)

def check (left right : Contract) (intent : Intent) : Except String (Compatible left right intent) := do
  let leftNonempty ← verify (left.id ≠ "") "The left operator ID is empty."
  let rightNonempty ← verify (right.id ≠ "") "The right operator ID is empty."
  let distinct ← verify (left.id ≠ right.id) "The two operator IDs must differ."
  let forward ← checkCases right left.cases
  let backward ← checkCases left right.cases
  let borders ← checkBorders left right 0 intent.borders
  return ⟨leftNonempty.down, rightNonempty.down, distinct.down, forward.down, backward.down, borders.down⟩

theorem Compatible.matchingCase (value : Compatible left right intent) (id : String) (first second : Case)
    (firstFound : left.case? id = some first) (secondFound : right.case? id = some second) : Matches first second := by
  have member := List.mem_of_find?_eq_some firstFound
  have selected : first.id = id := beq_iff_eq.mp
    (List.find?_some (p := fun candidate : Case => candidate.id == id) firstFound)
  obtain ⟨matched, found, agreement⟩ := value.forward first member
  rw [selected] at found
  have same : matched = second := Option.some.inj (found.symm.trans secondFound)
  exact same ▸ agreement

theorem Compatible.border_source_known (value : Compatible left right intent) (border : Border)
    (member : border ∈ intent.borders) : border.source.node ∈ (contracts left right border.source.side).ids := by
  obtain ⟨checked⟩ := value.borders border member
  exact checked.source_known

theorem Compatible.border_target_known (value : Compatible left right intent) (border : Border)
    (member : border ∈ intent.borders) : border.target.node ∈ (contracts left right border.target.side).ids := by
  obtain ⟨checked⟩ := value.borders border member
  exact checked.target_known

theorem Compatible.border_opposite (value : Compatible left right intent) (border : Border)
    (member : border ∈ intent.borders) : border.source.side ≠ border.target.side := by
  obtain ⟨checked⟩ := value.borders border member
  exact checked.opposite

theorem Compatible.border_roles (value : Compatible left right intent) (border : Border)
    (member : border ∈ intent.borders) :
    ∃ source target,
      (contracts left right border.source.side).node? border.source.node = some source ∧
      (contracts left right border.target.side).node? border.target.node = some target ∧
      source.role = .egress ∧ target.role = .ingress := by
  obtain ⟨checked⟩ := value.borders border member
  exact ⟨checked.sourceNode, checked.targetNode, checked.sourceFound, checked.targetFound,
    checked.sourceRole, checked.targetRole⟩

end Netlib.Federation.Compatibility
