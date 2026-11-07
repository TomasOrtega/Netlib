import Netlib.Check.FederatedCompatibility
import Netlib.Check.DomainContractNative

/-!
# Native federation refinements in both directions

Native edges refine the public upper graph. Public must edges expand into
checked native paths through exact per-revision anchors.
-/

namespace Netlib.Federation.Composition

open Compatibility

def nativeForward (left right : Revision) (borders : List Border) (caseID : String) (source target : String) : Prop :=
  ∃ exit entry, borderEdge borders caseID ⟨.left, exit⟩ ⟨.right, entry⟩ = true ∧
    source = left.anchor exit ∧ target = right.anchor entry

def nativeBackward (left right : Revision) (borders : List Border) (caseID : String) (source target : String) : Prop :=
  ∃ exit entry, borderEdge borders caseID ⟨.right, exit⟩ ⟨.left, entry⟩ = true ∧
    source = right.anchor exit ∧ target = left.anchor entry

def nativeModel (left right : Revision) (first second : Case) (borders : List Border) (header : Packet.Header) :
    Network (Sum String String) :=
  Network.interconnect (left.native first header) (right.native second header)
    (nativeForward left right borders first.id) (nativeBackward left right borders first.id)

def project (left right : Revision) : Sum String String → PublicRef
  | .inl node => ⟨.left, left.project node⟩
  | .inr node => ⟨.right, right.project node⟩

def anchor (left right : Revision) (node : PublicRef) : Sum String String :=
  match node.side with
  | .left => .inl (left.anchor node.node)
  | .right => .inr (right.anchor node.node)

theorem reference_left (left right : Contract) (node : String) :
    (⟨.left, node⟩ : PublicRef) ∈ references left right ↔ node ∈ left.ids := by
  simp [references, PublicRef.mk.injEq]

theorem reference_right (left right : Contract) (node : String) :
    (⟨.right, node⟩ : PublicRef) ∈ references left right ↔ node ∈ right.ids := by
  simp [references, PublicRef.mk.injEq]

theorem border_witness (borders : List Border) (caseID : String) (source target : PublicRef)
    (edge : borderEdge borders caseID source target = true) :
    ∃ border ∈ borders, border.source = source ∧ border.target = target ∧ caseID ∈ border.cases := by
  obtain ⟨border, member, selected⟩ := List.any_eq_true.mp edge
  have flags : (border.source = source ∧ border.target = target) ∧ caseID ∈ border.cases := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq, List.contains_eq_mem] using selected
  exact ⟨border, member, flags.1.1, flags.1.2, flags.2⟩

theorem border_known (compatible : Compatible left right intent) (caseID : String) (source target : PublicRef)
    (edge : borderEdge intent.borders caseID source target = true) :
    source.node ∈ (contracts left right source.side).ids ∧ target.node ∈ (contracts left right target.side).ids := by
  obtain ⟨border, member, sameSource, sameTarget, _⟩ := border_witness intent.borders caseID source target edge
  have sourceKnown := compatible.border_source_known border member
  have targetKnown := compatible.border_target_known border member
  simpa only [sameSource, sameTarget] using And.intro sourceKnown targetKnown

private theorem upper_left (left right : Contract) (first second : Case) (borders : List Border)
    (source target : String) (edge : (left.upperModel first).link source target) :
    (publicModel left right first second borders false).link ⟨.left, source⟩ ⟨.left, target⟩ :=
  ⟨(reference_left left right source).mpr edge.1, (reference_left left right target).mpr edge.2.1, edge.2.2⟩

private theorem upper_right (left right : Contract) (first second : Case) (borders : List Border)
    (source target : String) (edge : (right.upperModel second).link source target) :
    (publicModel left right first second borders false).link ⟨.right, source⟩ ⟨.right, target⟩ :=
  ⟨(reference_right left right source).mpr edge.1, (reference_right left right target).mpr edge.2.1, edge.2.2⟩

def upper (compatible : Compatible leftContract rightContract intent)
    (leftChecked : Native.Checked leftContract left) (rightChecked : Native.Checked rightContract right)
    (first second : Case) (firstMember : first ∈ leftContract.cases) (secondMember : second ∈ rightContract.cases)
    (header : Packet.Header) (firstAccepted : first.selector.accepts header = true)
    (secondAccepted : second.selector.accepts header = true) :
    StutteringRefinement (nativeModel left right first second intent.borders header)
      (publicModel leftContract rightContract first second intent.borders false) where
  project := project left right
  simulate source target edge := by
    cases source with
    | inl source =>
      cases target with
      | inl target =>
        have inside := (leftChecked.upper first firstMember header firstAccepted).simulate source target edge
        change left.project source = left.project target ∨ (leftContract.upperModel first).link _ _ at inside
        rcases inside with same | step
        · exact .inl (congrArg (fun node => (⟨.left, node⟩ : PublicRef)) same)
        · exact .inr (upper_left leftContract rightContract first second intent.borders _ _ step)
      | inr target =>
        obtain ⟨exit, entry, border, sourceEq, targetEq⟩ := edge
        subst source target
        have known := border_known compatible first.id ⟨.left, exit⟩ ⟨.right, entry⟩ border
        have sourceProject := leftChecked.validated.anchorProject exit known.1
        have targetProject := rightChecked.validated.anchorProject entry known.2
        apply Or.inr
        change (publicModel leftContract rightContract first second intent.borders false).link
          ⟨.left, left.project (left.anchor exit)⟩ ⟨.right, right.project (right.anchor entry)⟩
        rw [sourceProject, targetProject]
        exact ⟨(reference_left _ _ exit).mpr known.1, (reference_right _ _ entry).mpr known.2, border⟩
    | inr source =>
      cases target with
      | inl target =>
        obtain ⟨exit, entry, border, sourceEq, targetEq⟩ := edge
        subst source target
        have known := border_known compatible first.id ⟨.right, exit⟩ ⟨.left, entry⟩ border
        have sourceProject := rightChecked.validated.anchorProject exit known.1
        have targetProject := leftChecked.validated.anchorProject entry known.2
        apply Or.inr
        change (publicModel leftContract rightContract first second intent.borders false).link
          ⟨.right, right.project (right.anchor exit)⟩ ⟨.left, left.project (left.anchor entry)⟩
        rw [sourceProject, targetProject]
        exact ⟨(reference_right _ _ exit).mpr known.1, (reference_left _ _ entry).mpr known.2, border⟩
      | inr target =>
        have inside := (rightChecked.upper second secondMember header secondAccepted).simulate source target edge
        change right.project source = right.project target ∨ (rightContract.upperModel second).link _ _ at inside
        rcases inside with same | step
        · exact .inl (congrArg (fun node => (⟨.right, node⟩ : PublicRef)) same)
        · exact .inr (upper_right leftContract rightContract first second intent.borders _ _ step)

def lower (leftChecked : Native.Checked leftContract left) (rightChecked : Native.Checked rightContract right)
    (first second : Case) (firstMember : first ∈ leftContract.cases) (secondMember : second ∈ rightContract.cases)
    (borders : List Border) (header : Packet.Header) (firstAccepted : first.selector.accepts header = true)
    (secondAccepted : second.selector.accepts header = true) :
    Refinement (publicModel leftContract rightContract first second borders true)
      (nativeModel left right first second borders header) where
  project := anchor left right
  simulate source target edge := by
    rcases source with ⟨sourceSide, source⟩
    rcases target with ⟨targetSide, target⟩
    cases sourceSide with
    | left =>
      cases targetSide with
      | left =>
        have inside : (leftContract.mustModel first).link source target :=
          ⟨(reference_left _ _ source).mp edge.1, (reference_left _ _ target).mp edge.2.1, edge.2.2⟩
        have path := (leftChecked.lower first firstMember header firstAccepted).simulate source target inside
        change (left.native first header).Reachable (left.anchor source) (left.anchor target) at path
        exact path.map Sum.inl (fun _ _ link => .single link)
      | right => exact .single ⟨source, target, edge.2.2, rfl, rfl⟩
    | right =>
      cases targetSide with
      | left => exact .single ⟨source, target, edge.2.2, rfl, rfl⟩
      | right =>
        have inside : (rightContract.mustModel second).link source target :=
          ⟨(reference_right _ _ source).mp edge.1, (reference_right _ _ target).mp edge.2.1, edge.2.2⟩
        have path := (rightChecked.lower second secondMember header secondAccepted).simulate source target inside
        change (right.native second header).Reachable (right.anchor source) (right.anchor target) at path
        exact path.map Sum.inr (fun _ _ link => .single link)

theorem anchor_project (leftChecked : Native.Checked leftContract left) (rightChecked : Native.Checked rightContract right)
    (node : PublicRef) (known : node ∈ references leftContract rightContract) :
    project left right (anchor left right node) = node := by
  rcases node with ⟨side, node⟩
  cases side with
  | left =>
    have equal := leftChecked.validated.anchorProject node ((reference_left _ _ node).mp known)
    change (⟨.left, left.project (left.anchor node)⟩ : PublicRef) = ⟨.left, node⟩
    rw [equal]
  | right =>
    have equal := rightChecked.validated.anchorProject node ((reference_right _ _ node).mp known)
    change (⟨.right, right.project (right.anchor node)⟩ : PublicRef) = ⟨.right, node⟩
    rw [equal]

def Known (left right : Revision) : Sum String String → Prop
  | .inl node => node ∈ left.snapshot.intent.ids
  | .inr node => node ∈ right.snapshot.intent.ids

def Enforcement (left right : Revision) : Sum String String → Prop
  | .inl node => node ∈ left.snapshot.intent.select left.snapshot.intent.enforcement
  | .inr node => node ∈ right.snapshot.intent.select right.snapshot.intent.enforcement

def EnforcementOn (side : Side) (left right : Revision) : Sum String String → Prop
  | .inl node => side = .left ∧ node ∈ left.snapshot.intent.select left.snapshot.intent.enforcement
  | .inr node => side = .right ∧ node ∈ right.snapshot.intent.select right.snapshot.intent.enforcement

def EnforcementOnly (left right : Contract) (gateways : List PublicRef) : Prop :=
  ∀ gateway ∈ gateways, ∃ node ∈ (contracts left right gateway.side).nodes,
    node.id = gateway.node ∧ node.role = .enforcement

theorem anchor_known (leftChecked : Native.Checked leftContract left) (rightChecked : Native.Checked rightContract right)
    (node : PublicRef) (member : node ∈ references leftContract rightContract) : Known left right (anchor left right node) := by
  rcases node with ⟨side, node⟩
  cases side with
  | left => exact leftChecked.validated.anchorMember node ((reference_left _ _ node).mp member)
  | right => exact rightChecked.validated.anchorMember node ((reference_right _ _ node).mp member)

theorem edge_known (compatible : Compatible leftContract rightContract intent)
    (leftChecked : Native.Checked leftContract left) (rightChecked : Native.Checked rightContract right)
    (first second : Case) (header : Packet.Header) (source target : Sum String String)
    (edge : (nativeModel left right first second intent.borders header).link source target) :
    Known left right source ∧ Known left right target := by
  cases source with
  | inl source =>
    cases target with
    | inl target => exact ⟨edge.1, edge.2.1⟩
    | inr target =>
      obtain ⟨exit, entry, border, sourceEq, targetEq⟩ := edge
      subst source target
      have known := border_known compatible first.id ⟨.left, exit⟩ ⟨.right, entry⟩ border
      exact ⟨leftChecked.validated.anchorMember exit known.1, rightChecked.validated.anchorMember entry known.2⟩
  | inr source =>
    cases target with
    | inl target =>
      obtain ⟨exit, entry, border, sourceEq, targetEq⟩ := edge
      subst source target
      have known := border_known compatible first.id ⟨.right, exit⟩ ⟨.left, entry⟩ border
      exact ⟨rightChecked.validated.anchorMember exit known.1, leftChecked.validated.anchorMember entry known.2⟩
    | inr target => exact ⟨edge.1, edge.2.1⟩

theorem walk_known (compatible : Compatible leftContract rightContract intent)
    (leftChecked : Native.Checked leftContract left) (rightChecked : Native.Checked rightContract right)
    (first second : Case) (header : Packet.Header)
    (walk : Network.Walk (nativeModel left right first second intent.borders header) source target trace)
    (initial : Known left right source) : ∀ node ∈ trace, Known left right node := by
  induction walk with
  | nil source =>
    intro node member
    exact (List.mem_singleton.mp member) ▸ initial
  | @cons source next target trace edge _ ih =>
    have endpoints := edge_known compatible leftChecked rightChecked first second header source next edge
    intro node member
    rcases List.mem_cons.mp member with same | member
    · exact same ▸ endpoints.1
    · exact ih endpoints.2 node member

theorem enforcement_reflection (leftChecked : Native.Checked leftContract left)
    (rightChecked : Native.Checked rightContract right) (gateways : List PublicRef)
    (typed : EnforcementOnly leftContract rightContract gateways) (node : Sum String String)
    (known : Known left right node) (gateway : project left right node ∈ gateways) : Enforcement left right node := by
  obtain ⟨publicNode, member, selected, role⟩ := typed _ gateway
  cases node with
  | inl node => exact leftChecked.validated.enforcement node known publicNode member selected.symm role
  | inr node => exact rightChecked.validated.enforcement node known publicNode member selected.symm role

theorem _root_.Netlib.Federation.Revision.project_known (validated : Revision.Validated contract revision)
    (node : String) (visible : revision.project node ≠ "") : node ∈ revision.snapshot.intent.ids := by
  unfold Revision.project at visible
  cases found : revision.projection.find? (fun row => row.localNode == node) with
  | none => simp only [found, Option.map_none, Option.getD_none, ne_eq, not_true_eq_false] at visible
  | some row =>
    have member := List.mem_of_find?_eq_some found
    have selected : row.localNode = node := beq_iff_eq.mp
      (List.find?_some (p := fun row : NodeMap => row.localNode == node) found)
    have known := (validated.projectionRows row member).1
    simpa only [selected] using known

theorem reflect_labels (leftChecked : Native.Checked leftContract left) (rightChecked : Native.Checked rightContract right)
    (gateways : List PublicRef) (typed : EnforcementOnly leftContract rightContract gateways)
    (node : Sum String String) (gateway : project left right node ∈ gateways) : Enforcement left right node := by
  obtain ⟨publicNode, member, selected, role⟩ := typed _ gateway
  cases node with
  | inl node =>
    have named := leftChecked.validated.publicValid.nodeNames publicNode member
    have known := left.project_known leftChecked.validated node (by
      intro empty
      exact named (selected.trans empty))
    exact leftChecked.validated.enforcement node known publicNode member selected.symm role
  | inr node =>
    have named := rightChecked.validated.publicValid.nodeNames publicNode member
    have known := right.project_known rightChecked.validated node (by
      intro empty
      exact named (selected.trans empty))
    exact rightChecked.validated.enforcement node known publicNode member selected.symm role

theorem enforcementOnly_of_found (left right : Contract) (gateways : List PublicRef)
    (typed : ∀ gateway ∈ gateways, ∃ node,
      (contracts left right gateway.side).node? gateway.node = some node ∧ node.role = .enforcement) :
    EnforcementOnly left right gateways := by
  intro gateway member
  obtain ⟨node, found, role⟩ := typed gateway member
  have known := List.mem_of_find?_eq_some found
  have selected : node.id = gateway.node := beq_iff_eq.mp
    (List.find?_some (p := fun candidate : PublicNode => candidate.id == gateway.node) found)
  exact ⟨node, known, selected, role⟩

theorem reflect_gateways (leftChecked : Native.Checked leftContract left) (rightChecked : Native.Checked rightContract right)
    (gateways : List PublicRef)
    (typed : ∀ gateway ∈ gateways, ∃ node,
      (contracts leftContract rightContract gateway.side).node? gateway.node = some node ∧ node.role = .enforcement)
    (node : Sum String String) (gateway : project left right node ∈ gateways) : Enforcement left right node :=
  reflect_labels leftChecked rightChecked gateways (enforcementOnly_of_found _ _ _ typed) node gateway

theorem reflect_gateways_side (leftChecked : Native.Checked leftContract left) (rightChecked : Native.Checked rightContract right)
    (gateways : List PublicRef)
    (typed : ∀ gateway ∈ gateways, ∃ node,
      (contracts leftContract rightContract gateway.side).node? gateway.node = some node ∧ node.role = .enforcement)
    (side : Side) (sameSide : ∀ gateway ∈ gateways, gateway.side = side)
    (node : Sum String String) (gateway : project left right node ∈ gateways) : EnforcementOn side left right node := by
  have enforced := reflect_gateways leftChecked rightChecked gateways typed node gateway
  have selected := sameSide _ gateway
  cases node with
  | inl node => exact ⟨selected.symm, enforced⟩
  | inr node => exact ⟨selected.symm, enforced⟩

theorem mediated_enforcement (compatible : Compatible leftContract rightContract intent)
    (leftChecked : Native.Checked leftContract left) (rightChecked : Native.Checked rightContract right)
    (first second : Case) (firstMember : first ∈ leftContract.cases) (secondMember : second ∈ rightContract.cases)
    (header : Packet.Header) (firstAccepted : first.selector.accepts header = true)
    (secondAccepted : second.selector.accepts header = true) (source target : PublicRef)
    (sourceKnown : source ∈ references leftContract rightContract) (targetKnown : target ∈ references leftContract rightContract)
    (gateways : List PublicRef) (typed : EnforcementOnly leftContract rightContract gateways)
    (secure : (publicModel leftContract rightContract first second intent.borders false).Mediated
      (· = source) (· = target) (· ∈ gateways)) :
    (nativeModel left right first second intent.borders header).Mediated
      (· = anchor left right source) (· = anchor left right target) (Enforcement left right) := by
  let refinement := upper compatible leftChecked rightChecked first second firstMember secondMember header firstAccepted secondAccepted
  have mediated := refinement.mediated secure
  apply Network.mediated_iff_every_walk.mpr
  intro actualSource actualTarget trace selectedSource selectedTarget walk
  subst actualSource actualTarget
  have sourceProject := anchor_project leftChecked rightChecked source sourceKnown
  have targetProject := anchor_project leftChecked rightChecked target targetKnown
  obtain ⟨gateway, member, publicRole⟩ := Network.mediated_iff_every_walk.mp mediated
    (anchor left right source) (anchor left right target) trace sourceProject targetProject walk
  have reflected : project left right gateway ∈ gateways := publicRole
  exact ⟨gateway, member, reflect_labels leftChecked rightChecked gateways typed gateway reflected⟩

theorem mediated_on (compatible : Compatible leftContract rightContract intent)
    (leftChecked : Native.Checked leftContract left) (rightChecked : Native.Checked rightContract right)
    (first second : Case) (firstMember : first ∈ leftContract.cases) (secondMember : second ∈ rightContract.cases)
    (header : Packet.Header) (firstAccepted : first.selector.accepts header = true)
    (secondAccepted : second.selector.accepts header = true) (source target : PublicRef)
    (sourceKnown : source ∈ references leftContract rightContract) (targetKnown : target ∈ references leftContract rightContract)
    (gateways : List PublicRef)
    (typed : ∀ gateway ∈ gateways, ∃ node,
      (contracts leftContract rightContract gateway.side).node? gateway.node = some node ∧ node.role = .enforcement)
    (side : Side) (sameSide : ∀ gateway ∈ gateways, gateway.side = side)
    (secure : (publicModel leftContract rightContract first second intent.borders false).Mediated
      (· = source) (· = target) (· ∈ gateways)) :
    (nativeModel left right first second intent.borders header).Mediated
      (· = anchor left right source) (· = anchor left right target)
      (fun node => EnforcementOn side left right node ∧ project left right node ∈ gateways) := by
  let refinement := upper compatible leftChecked rightChecked first second firstMember secondMember header firstAccepted secondAccepted
  have mediated := refinement.mediated secure
  apply Network.mediated_iff_every_walk.mpr
  intro actualSource actualTarget trace selectedSource selectedTarget walk
  subst actualSource actualTarget
  have sourceProject := anchor_project leftChecked rightChecked source sourceKnown
  have targetProject := anchor_project leftChecked rightChecked target targetKnown
  obtain ⟨gateway, member, publicRole⟩ := Network.mediated_iff_every_walk.mp mediated
    (anchor left right source) (anchor left right target) trace sourceProject targetProject walk
  have reflected : project left right gateway ∈ gateways := publicRole
  exact ⟨gateway, member, reflect_gateways_side leftChecked rightChecked gateways typed side sameSide gateway reflected, reflected⟩

theorem mediated_on_actual (compatible : Compatible leftContract rightContract intent)
    (leftChecked : Native.Checked leftContract left) (rightChecked : Native.Checked rightContract right)
    (first second : Case) (firstMember : first ∈ leftContract.cases) (secondMember : second ∈ rightContract.cases)
    (header : Packet.Header) (firstAccepted : first.selector.accepts header = true)
    (secondAccepted : second.selector.accepts header = true) (source target : PublicRef)
    (sourceKnown : source ∈ references leftContract rightContract) (targetKnown : target ∈ references leftContract rightContract)
    (gateways : List PublicRef)
    (typed : ∀ gateway ∈ gateways, ∃ node,
      (contracts leftContract rightContract gateway.side).node? gateway.node = some node ∧ node.role = .enforcement)
    (side : Side) (sameSide : ∀ gateway ∈ gateways, gateway.side = side)
    (secure : (publicModel leftContract rightContract first second intent.borders false).Mediated
      (· = source) (· = target) (· ∈ gateways)) :
    (nativeModel left right first second intent.borders header).Mediated
      (· = anchor left right source) (· = anchor left right target) (EnforcementOn side left right) := by
  have specific := mediated_on compatible leftChecked rightChecked first second firstMember secondMember header
    firstAccepted secondAccepted source target sourceKnown targetKnown gateways typed side sameSide secure
  apply Network.mediated_iff_every_walk.mpr
  intro actualSource actualTarget trace selectedSource selectedTarget walk
  obtain ⟨gateway, member, enforced, _⟩ := Network.mediated_iff_every_walk.mp specific
    actualSource actualTarget trace selectedSource selectedTarget walk
  exact ⟨gateway, member, enforced⟩

end Netlib.Federation.Composition
