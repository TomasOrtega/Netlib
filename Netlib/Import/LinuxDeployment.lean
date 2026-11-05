import Netlib.Import.LinuxRoute
import Netlib.Import.Nftables
import Netlib.Model.DataPlane

/-!
# Linux transit deployment bundles

The model receives valid, unfragmented IPv4 transit headers after main-table selection.
Bindings supply trusted topology and next-node identity.
Identity enforcement remains a supplied external policy.
Kernel execution and the snapshot capture process require separate evidence.
-/

namespace Netlib.Import.LinuxDeployment

open Packet

structure Router where
  index : Nat
  node : String
  routeVersion : String
  routes : LinuxRoute.Snapshot
  nftables : Nftables.Snapshot

namespace Router

def bindings (router : Router) : List LinuxRoute.Binding := router.routes.bindings

def links (router : Router) : List DataPlane.PhysicalLink :=
  router.bindings.map fun binding => ⟨router.node, binding.nextNode, true, router.nftables.compile⟩

def routeTable (router : Router) : DataPlane.RouteTable := ⟨router.node, router.routes.compile⟩

def adjacent (router : Router) (target : String) : Bool :=
  router.bindings.any (·.nextNode == target)

def sourceID (router : Router) : String := s!"/routers/{router.index}"

end Router

structure Snapshot where
  intent : DataPlane.Config
  routers : List Router
  uniqueNodes : (routers.map Router.node).Nodup

namespace Snapshot

def compile (snapshot : Snapshot) : DataPlane.Config :=
  { snapshot.intent with
    links := snapshot.routers.flatMap Router.links
    routes := snapshot.routers.map Router.routeTable }

def router? (snapshot : Snapshot) (node : String) : Option Router :=
  snapshot.routers.find? (·.node == node)

def adjacent (snapshot : Snapshot) (source target : String) : Bool :=
  ((snapshot.router? source).map (·.adjacent target)).getD false

/-- This uses source-chain and source-route decisions before compilation. -/
def nativeEdge (snapshot : Snapshot) (header : Header)
    (request : ZeroTrust.Request String String String) (source target : String) : Bool :=
  match snapshot.router? source with
  | none => false
  | some router =>
    router.adjacent target && decide (router.routes.nextNode header.destination = some target) &&
    router.nftables.permits header &&
    (!(snapshot.intent.select snapshot.intent.enforcement).contains source &&
      !(snapshot.intent.select snapshot.intent.enforcement).contains target ||
      snapshot.intent.policy.allows request)

private theorem same_router {routers : List Router} (unique : (routers.map Router.node).Nodup)
    {left right : Router} (leftMember : left ∈ routers) (rightMember : right ∈ routers)
    (same : left.node = right.node) : left = right := by
  induction routers generalizing left right with
  | nil => simp at leftMember
  | cons head tail ih =>
    have distinct := List.nodup_cons.mp unique
    rcases List.mem_cons.mp leftMember with rfl | leftTail
    · rcases List.mem_cons.mp rightMember with rfl | rightTail
      · rfl
      · exact False.elim (distinct.1 (List.mem_map.mpr ⟨right, rightTail, same.symm⟩))
    · rcases List.mem_cons.mp rightMember with rfl | rightTail
      · exact False.elim (distinct.1 (List.mem_map.mpr ⟨left, leftTail, same⟩))
      · exact ih distinct.2 leftTail rightTail same

private theorem physical_as_any (snapshot : Snapshot) (source target : String) :
    snapshot.compile.physicalEdge source target =
      snapshot.routers.any (fun router => router.node == source && router.adjacent target) := by
  simp only [DataPlane.Config.physicalEdge, compile, List.any_flatMap]
  apply congrArg (fun predicate => snapshot.routers.any predicate)
  funext router
  cases same : router.node == source <;>
    simp [Router.links, Router.adjacent, List.any_map, Function.comp_def, same]

theorem physicalEdge_correct (snapshot : Snapshot) (source target : String) :
    snapshot.compile.physicalEdge source target = snapshot.adjacent source target := by
  rw [physical_as_any]
  apply Bool.eq_iff_iff.mpr
  cases found : snapshot.router? source with
  | none =>
    have noRouter := List.find?_eq_none.mp found
    simp only [adjacent, found, Option.map_none, Option.getD_none, Bool.false_eq_true, iff_false]
    intro possible
    obtain ⟨router, member, accepted⟩ := List.any_eq_true.mp possible
    exact noRouter router member ((Bool.and_eq_true _ _).mp accepted).1
  | some router =>
    have member := List.mem_of_find?_eq_some found
    have node : router.node = source := by simpa using List.find?_some found
    simp only [adjacent, found, Option.map_some, Option.getD_some]
    constructor
    · intro possible
      obtain ⟨other, belongs, accepted⟩ := List.any_eq_true.mp possible
      have otherNode : other.node = source := by simpa using ((Bool.and_eq_true _ _).mp accepted).1
      have same := same_router snapshot.uniqueNodes belongs member (otherNode.trans node.symm)
      subst other
      exact ((Bool.and_eq_true _ _).mp accepted).2
    · intro accepted
      exact List.any_eq_true.mpr ⟨router, member, by simp [node, accepted]⟩

private theorem find_routeTable (routers : List Router) (source : String) :
    (routers.map Router.routeTable).find? (·.node == source) =
      (routers.find? (·.node == source)).map Router.routeTable := by
  induction routers with
  | nil => rfl
  | cons router routers ih =>
    cases same : router.node == source <;>
      simp [Router.routeTable, same, ih]

theorem tables_correct (snapshot : Snapshot) (source : String) (router : Router)
    (found : snapshot.router? source = some router) :
    snapshot.compile.tables source = router.routes.compile := by
  simp only [DataPlane.Config.tables, compile, find_routeTable]
  rw [show snapshot.routers.find? (·.node == source) = some router from found]
  rfl

private theorem link_source (snapshot : Snapshot) (link : DataPlane.PhysicalLink)
    (member : link ∈ snapshot.compile.links) :
    ∃ router ∈ snapshot.routers, link.source = router.node ∧ link.rules = router.nftables.compile := by
  obtain ⟨router, belongs, member⟩ := List.mem_flatMap.mp member
  obtain ⟨binding, _, rfl⟩ := List.mem_map.mp member
  exact ⟨router, belongs, rfl, rfl⟩

theorem policies_correct (snapshot : Snapshot) (source target : String) (router : Router)
    (found : snapshot.router? source = some router)
    (physical : snapshot.compile.physicalEdge source target = true) :
    snapshot.compile.policies source target = router.nftables.compile := by
  unfold DataPlane.Config.policies
  cases selected : snapshot.compile.links.find? (fun link => link.source == source && link.target == target) with
  | none =>
    have noLink := List.find?_eq_none.mp selected
    obtain ⟨link, member, enabled⟩ := List.any_eq_true.mp physical
    have conditions := (Bool.and_eq_true _ _).mp enabled
    have sourceMatch := ((Bool.and_eq_true _ _).mp conditions.1).2
    exact False.elim (noLink link member (by simp [sourceMatch, conditions.2]))
  | some link =>
    have member := List.mem_of_find?_eq_some selected
    have selectedMatches : (link.source == source && link.target == target) = true :=
      List.find?_some (p := fun item : DataPlane.PhysicalLink => item.source == source && item.target == target)
        (a := link) selected
    have accepted := (Bool.and_eq_true _ _).mp selectedMatches
    have sourceNode : link.source = source := by simpa using accepted.1
    obtain ⟨owner, ownerMember, ownerSource, ownerRules⟩ := link_source snapshot link member
    have routerMember := List.mem_of_find?_eq_some found
    have routerNode : router.node = source := by simpa using List.find?_some found
    have same := same_router snapshot.uniqueNodes ownerMember routerMember
      (ownerSource.symm.trans (sourceNode.trans routerNode.symm))
    subst owner
    simpa only [Option.map_some, Option.getD_some] using ownerRules

theorem edge_correct (snapshot : Snapshot) (header : Header)
    (request : ZeroTrust.Request String String String) (source target : String) :
    snapshot.compile.edge header request source target = snapshot.nativeEdge header request source target := by
  cases found : snapshot.router? source with
  | none =>
    have absent : snapshot.compile.physicalEdge source target = false := by
      rw [physicalEdge_correct]
      simp [adjacent, found]
    simp [DataPlane.Config.edge, absent, nativeEdge, found]
  | some router =>
    cases connection : router.adjacent target with
    | false =>
      have absent : snapshot.compile.physicalEdge source target = false := by
        rw [physicalEdge_correct]
        simp [adjacent, found, connection]
      simp [DataPlane.Config.edge, absent, nativeEdge, found, connection]
    | true =>
      have present : snapshot.compile.physicalEdge source target = true := by
        rw [physicalEdge_correct]
        simp [adjacent, found, connection]
      rw [DataPlane.Config.edge, present, tables_correct snapshot source router found,
        policies_correct snapshot source target router found present,
        LinuxRoute.Snapshot.nextHop_correct, Nftables.Snapshot.compile_allows]
      simp only [nativeEdge, found, connection, Bool.true_and]
      rfl

def nativeModel (snapshot : Snapshot) (header : Header)
    (request : ZeroTrust.Request String String String) : Network String :=
  Certificate.finiteNetwork snapshot.intent.ids (snapshot.nativeEdge header request)

theorem model_correct (snapshot : Snapshot) (header : Header)
    (request : ZeroTrust.Request String String String) :
    snapshot.compile.model header request = snapshot.nativeModel header request := by
  rw [← DataPlane.Config.finiteNetwork_eq_model]
  change Certificate.finiteNetwork snapshot.intent.ids (snapshot.compile.edge header request) = _
  unfold nativeModel
  congr 1
  funext source target
  exact edge_correct snapshot header request source target

end Snapshot

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def fields (json : Lean.Json) (required : List String) : Except String Unit := do
  let object ← json.getObj?
  for (key, _) in object.toList do
    require (required.contains key) s!"Unsupported bundle field: {key}."
  for key in required do
    let _ ← json.getObjVal? key

private def str (json : Lean.Json) (key : String) : Except String String :=
  json.getObjVal? key >>= Lean.Json.getStr?

private def binding (json : Lean.Json) : Except String LinuxRoute.Binding := do
  fields json ["device", "nextNode", "gateway"]
  let gateway ← match ← json.getObjVal? "gateway" with
    | .null => pure none
    | value => some <$> IPv4.parseAddress (← value.getStr?)
  return ⟨← str json "device", ← str json "nextNode", gateway⟩

private def parseRouter (json : Lean.Json) (index : Nat) : Except String Router := do
  fields json ["node", "routeVersion", "bindings", "routes", "nftables"]
  let node ← str json "node"
  let routeVersion ← str json "routeVersion"
  require (routeVersion == "6.19.0") "Use iproute2 6.19.0 route snapshots."
  let bindings ← (← (← json.getObjVal? "bindings").getArr?).toList.mapM binding
  let routes ← LinuxRoute.Snapshot.fromJson (← json.getObjVal? "routes") bindings
  let nftables ← Nftables.Snapshot.fromJson (← json.getObjVal? "nftables")
  return ⟨index, node, routeVersion, routes, nftables⟩

namespace Snapshot

def fromJson (json : Lean.Json) : Except String Snapshot := do
  fields json ["schema", "scope", "intent", "routers"]
  require ((← (← json.getObjVal? "schema").getNat?) == 1) "Use Linux deployment schema 1."
  require ((← str json "scope") == "main-table-ipv4-transit") "Unsupported Linux forwarding scope."
  let intentJson ← json.getObjVal? "intent"
  fields intentJson ["schema", "devices", "groups", "principals", "resources", "operations",
    "permissions", "requests", "traffic", "enforcement", "requirements"]
  let intentFields ← intentJson.getObj?
  let intent ← DataPlane.Config.fromJson (Lean.Json.mkObj (intentFields.toList ++
    [("links", Lean.toJson ([] : List Lean.Json)), ("routes", Lean.toJson ([] : List Lean.Json))]))
  let inputs ← (← json.getObjVal? "routers").getArr?
  let mut routers := []
  for index in [:inputs.size] do
    let router ← (parseRouter inputs[index]! index).mapError (s!"/routers/{index}: " ++ ·)
    require (intent.ids.contains router.node) s!"/routers/{index}: Unknown router node: {router.node}."
    routers := routers ++ [router]
  if unique : (routers.map Router.node).Nodup then
    for node in intent.ids do
      require (routers.any (·.node == node)) s!"Missing router snapshot for node: {node}."
    let snapshot : Snapshot := ⟨intent, routers, unique⟩
    snapshot.compile.validate
    return snapshot
  else throw "Router nodes must have exactly one snapshot."

def parse (text : String) : Except String Snapshot := do
  fromJson (← Netlib.Import.Json.parse text)

end Snapshot
end Netlib.Import.LinuxDeployment
