import Netlib.Check.FederatedRefinement

/-!
# Exact native and border step origins

Each local step keeps the selected source router, route, and filter verdict.
Each crossing keeps its declared border and checked contract references.
-/

namespace Netlib.Federation.Provenance

open Import Compatibility

private theorem source_filter (rules : List Nftables.SourceRule) (policy fallback : Packet.Action)
    (header : Packet.Header) :
    Packet.ACL.evaluate fallback (rules.map Nftables.SourceRule.compile ++ [⟨{}, policy⟩]) header =
      match rules.find? (fun rule => rule.accepts header) with
      | none => policy
      | some rule => rule.action := by
  induction rules with
  | nil => simp [Packet.ACL.evaluate, Packet.ACL.lookup, Packet.Match.any_accepts]
  | cons rule rest ih =>
    cases accepted : rule.accepts header with
    | false =>
      rw [List.map_cons, List.cons_append, Packet.ACL.evaluate_cons_rejects fallback rule.compile _ header
        (by rw [Nftables.SourceRule.compile_accepts]; exact accepted)]
      simpa only [List.find?_cons, accepted, Bool.false_eq_true, ↓reduceIte] using ih
    | true =>
      rw [List.map_cons, List.cons_append, Packet.ACL.evaluate_cons_accepts fallback rule.compile _ header
        (by rw [Nftables.SourceRule.compile_accepts]; exact accepted)]
      simp only [List.find?_cons, accepted, Nftables.SourceRule.compile]

inductive Filter (snapshot : Nftables.Snapshot) (header : Packet.Header) where
  | rule (source : Nftables.SourceRule)
      (selected : snapshot.rules.find? (fun rule => rule.accepts header) = some source)
      (verdict : source.action = .permit)
  | policy (selected : snapshot.rules.find? (fun rule => rule.accepts header) = none)
      (verdict : snapshot.policy = .permit)

def Filter.sourceID : Filter snapshot header → String
  | .rule source _ _ => source.sourceID
  | .policy _ _ => snapshot.policySourceID

theorem filter_origin (snapshot : Nftables.Snapshot) (header : Packet.Header)
    (permitted : snapshot.permits header = true) : Nonempty (Filter snapshot header) := by
  have verdict : snapshot.evaluate header = .permit := of_decide_eq_true permitted
  have selected := source_filter snapshot.rules snapshot.policy .deny header
  change Packet.ACL.evaluate .deny snapshot.compile header = _ at selected
  rw [snapshot.compile_evaluate .deny header] at selected
  cases found : snapshot.rules.find? (fun rule => rule.accepts header) with
  | none =>
    rw [found] at selected
    exact ⟨.policy found (selected.symm.trans verdict)⟩
  | some source =>
    rw [found] at selected
    exact ⟨.rule source found (selected.symm.trans verdict)⟩

structure Local (revision : Revision) (selected : Case) (header : Packet.Header) (source target : String) where
  sourceKnown : source ∈ revision.snapshot.intent.ids
  targetKnown : target ∈ revision.snapshot.intent.ids
  native : revision.snapshot.nativeEdge header selected.request source target = true
  router : LinuxDeployment.Router
  routerFound : revision.snapshot.router? source = some router
  routerMember : router ∈ revision.snapshot.routers
  routerNode : router.node = source
  adjacent : router.adjacent target = true
  routeNext : router.routes.nextNode header.destination = some target
  route : LinuxRoute.Route
  routeSelected : router.routes.selected header.destination = some route
  routeTarget : route.nextNode = some target
  filter : Filter router.nftables header
  permits : router.nftables.permits header = true
  policy : (!(revision.snapshot.intent.select revision.snapshot.intent.enforcement).contains source &&
    !(revision.snapshot.intent.select revision.snapshot.intent.enforcement).contains target ||
      revision.snapshot.intent.policy.allows selected.request) = true

def Local.revisionID (_value : Local revision selected header source target) : String := revision.id

def Local.routerLocation (value : Local revision selected header source target) : String := value.router.sourceID

def Local.routeLocation (value : Local revision selected header source target) : String := value.route.location

def Local.filterLocation (value : Local revision selected header source target) : String := value.filter.sourceID

theorem local_origin (revision : Revision) (selected : Case) (header : Packet.Header) (source target : String)
    (edge : (revision.native selected header).link source target) : Nonempty (Local revision selected header source target) := by
  have native := edge.2.2
  unfold LinuxDeployment.Snapshot.nativeEdge at native
  cases found : revision.snapshot.router? source with
  | none => simp only [found, Bool.false_eq_true] at native
  | some router =>
    have flags : ((router.adjacent target = true ∧ router.routes.nextNode header.destination = some target) ∧
        router.nftables.permits header = true) ∧
        (!(revision.snapshot.intent.select revision.snapshot.intent.enforcement).contains source &&
          !(revision.snapshot.intent.select revision.snapshot.intent.enforcement).contains target ||
          revision.snapshot.intent.policy.allows selected.request) = true := by
      simpa only [found, Bool.and_eq_true, decide_eq_true_eq] using native
    have routerMember := List.mem_of_find?_eq_some found
    have routerNode : router.node = source := beq_iff_eq.mp
      (List.find?_some (p := fun candidate : LinuxDeployment.Router => candidate.node == source) found)
    obtain ⟨filter⟩ := filter_origin router.nftables header flags.1.2
    cases routeFound : router.routes.selected header.destination with
    | none =>
      simp only [LinuxRoute.Snapshot.nextNode, routeFound, Option.bind_none, reduceCtorEq] at flags
      exact False.elim flags.1.1.2
    | some route =>
      have routeTarget : route.nextNode = some target := by
        simpa only [LinuxRoute.Snapshot.nextNode, routeFound, Option.bind_some] using flags.1.1.2
      exact ⟨⟨edge.1, edge.2.1, edge.2.2, router, found, routerMember, routerNode,
        flags.1.1.1, flags.1.1.2, route, routeFound, routeTarget, filter, flags.1.2, flags.2⟩⟩

inductive Origin (leftContract rightContract : Contract) (left right : Revision) (first second : Case)
    (intent : Intent) (header : Packet.Header) : Sum String String → Sum String String → Type where
  | left (source target : String) (native : Local left first header source target) :
      Origin leftContract rightContract left right first second intent header (.inl source) (.inl target)
  | right (source target : String) (native : Local right second header source target) :
      Origin leftContract rightContract left right first second intent header (.inr source) (.inr target)
  | border (source target : Sum String String) (declared : Border) (member : declared ∈ intent.borders)
      (checked : BorderChecked leftContract rightContract declared) (selectedCase : first.id ∈ declared.cases)
      (sourceAnchor : Composition.anchor left right declared.source = source)
      (targetAnchor : Composition.anchor left right declared.target = target) :
      Origin leftContract rightContract left right first second intent header source target

theorem edge_origin (compatible : Compatible leftContract rightContract intent) (left right : Revision)
    (first second : Case) (header : Packet.Header) (source target : Sum String String)
    (edge : (Composition.nativeModel left right first second intent.borders header).link source target) :
    Nonempty (Origin leftContract rightContract left right first second intent header source target) := by
  cases source with
  | inl source =>
    cases target with
    | inl target =>
      obtain ⟨native⟩ := local_origin left first header source target edge
      exact ⟨.left source target native⟩
    | inr target =>
      obtain ⟨exit, entry, border, sourceEq, targetEq⟩ := edge
      obtain ⟨declared, member, sourceRef, targetRef, selectedCase⟩ :=
        Composition.border_witness intent.borders first.id ⟨.left, exit⟩ ⟨.right, entry⟩ border
      obtain ⟨checked⟩ := compatible.borders declared member
      refine ⟨.border (.inl source) (.inr target) declared member checked selectedCase ?_ ?_⟩
      · simpa only [sourceRef, Composition.anchor] using congrArg Sum.inl sourceEq.symm
      · simpa only [targetRef, Composition.anchor] using congrArg Sum.inr targetEq.symm
  | inr source =>
    cases target with
    | inl target =>
      obtain ⟨exit, entry, border, sourceEq, targetEq⟩ := edge
      obtain ⟨declared, member, sourceRef, targetRef, selectedCase⟩ :=
        Composition.border_witness intent.borders first.id ⟨.right, exit⟩ ⟨.left, entry⟩ border
      obtain ⟨checked⟩ := compatible.borders declared member
      refine ⟨.border (.inr source) (.inl target) declared member checked selectedCase ?_ ?_⟩
      · simpa only [sourceRef, Composition.anchor] using congrArg Sum.inr sourceEq.symm
      · simpa only [targetRef, Composition.anchor] using congrArg Sum.inl targetEq.symm
    | inr target =>
      obtain ⟨native⟩ := local_origin right second header source target edge
      exact ⟨.right source target native⟩

private theorem walk_head {Node : Type u} {net : Network Node} {source target : Node} {vertices : List Node}
    (walk : Network.Walk net source target vertices) : vertices[0]? = some source := by
  cases walk <;> rfl

private theorem walk_edge {Node : Type u} {net : Network Node} {source target : Node} {vertices : List Node}
    (walk : Network.Walk net source target vertices) (index : Nat) (first second : Node)
    (firstFound : vertices[index]? = some first) (secondFound : vertices[index + 1]? = some second) : net.link first second := by
  induction walk generalizing index with
  | nil source =>
    cases index <;> simp at secondFound
  | @cons source next target trace edge rest ih =>
    cases index with
    | zero =>
      have sourceEq : source = first := Option.some.inj firstFound
      have targetEq : next = second := Option.some.inj ((walk_head rest).symm.trans secondFound)
      exact sourceEq ▸ targetEq ▸ edge
    | succ index => exact ih index firstFound secondFound

theorem walk_origins (compatible : Compatible leftContract rightContract intent) (left right : Revision)
    (first second : Case) (header : Packet.Header)
    {source target : Sum String String} {vertices : List (Sum String String)}
    (walk : Network.Walk (Composition.nativeModel left right first second intent.borders header) source target vertices)
    (index : Nat) (before after : Sum String String)
    (beforeFound : vertices[index]? = some before) (afterFound : vertices[index + 1]? = some after) :
    Nonempty (Origin leftContract rightContract left right first second intent header before after) :=
  edge_origin compatible left right first second header before after (walk_edge walk index before after beforeFound afterFound)

end Netlib.Federation.Provenance
