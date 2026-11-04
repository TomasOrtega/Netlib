import Lean
import Netlib.Model.Config
import Netlib.Routing.Basic
import Netlib.Security.ZeroTrust
import Netlib.Network.Certificate

/-!
# Packet and request input

This input format combines physical links, routes, packet rules, and request policies.
All numeric fields have explicit bounds.
The model keeps each packet header fixed along its path.
-/

namespace Netlib.DataPlane

open Packet

structure PhysicalLink where
  source : String
  target : String
  enabled : Bool
  rules : ACL
  deriving Repr, BEq

structure RouteTable where
  node : String
  entries : List (Routing.Entry String)
  deriving Repr, BEq

structure Principal where
  id : String
  authenticated : Bool
  deriving Repr, BEq

structure Permission where
  principal : String
  resource : String
  operation : String
  deriving Repr, BEq, DecidableEq

structure NamedRequest where
  id : String
  value : ZeroTrust.Request String String String
  deriving Repr, BEq

structure Traffic where
  id : String
  header : Header
  deriving Repr, BEq

inductive Kind where
  | reach
  | isolate
  | mediated
  deriving Repr, BEq, DecidableEq

structure Query where
  id : String
  kind : Kind
  source : Selector
  target : Selector
  traffic : String
  request : String
  gateways : Option Selector
  deriving Repr, BEq, DecidableEq

structure Config where
  devices : List Device
  groups : List Group
  links : List PhysicalLink
  routes : List RouteTable
  principals : List Principal
  resources : List String
  operations : List String
  permissions : List Permission
  requests : List NamedRequest
  traffic : List Traffic
  enforcement : Selector
  requirements : List Query
  deriving Repr

namespace Config

def inventory (c : Config) : Netlib.Config := ⟨c.devices, [], c.groups⟩
def ids (c : Config) : List String := c.devices.map (·.id)
def select (c : Config) (selector : Selector) : List String := c.inventory.select selector

def physicalEdge (c : Config) (source target : String) : Bool :=
  c.links.any (fun link => link.enabled && link.source == source && link.target == target)

def tables (c : Config) (node : String) : List (Routing.Entry String) :=
  ((c.routes.find? (·.node == node)).map (·.entries)).getD []

def policies (c : Config) (source target : String) : ACL :=
  ((c.links.find? (fun link => link.source == source && link.target == target)).map (·.rules)).getD []

def policy (c : Config) : ZeroTrust.Policy String String String where
  authenticated principal :=
    ((c.principals.find? (·.id == principal)).map (·.authenticated)).getD false
  authorized request :=
    c.permissions.contains ⟨request.principal, request.resource, request.operation⟩

def trafficFor (c : Config) (id : String) : Header :=
  ((c.traffic.find? (·.id == id)).map (·.header)).getD ⟨0, 0, 0, 0, 0⟩

def requestFor (c : Config) (id : String) : ZeroTrust.Request String String String :=
  ((c.requests.find? (·.id == id)).map (·.value)).getD ⟨"", "", ""⟩

/-- Physical adjacency also limits the route and packet decisions. -/
def packetModel (c : Config) (header : Header) : Network String :=
  (Routing.packetNetwork c.tables c.policies header).restrict
    (Certificate.finiteNetwork c.ids c.physicalEdge).link

/-- A request policy applies to links incident to the enforcement group. -/
def model (c : Config) (header : Header) (request : ZeroTrust.Request String String String) :
    Network String :=
  ZeroTrust.enforce (c.packetModel header) (fun node => node ∈ c.select c.enforcement) c.policy request

/-- The certificate search uses the same decisions as the composed model. -/
def edge (c : Config) (header : Header) (request : ZeroTrust.Request String String String)
    (source target : String) : Bool :=
  c.physicalEdge source target &&
  decide (Routing.nextHop (c.tables source) header.destination = some target) &&
  (c.policies source target).allows header &&
  (!(c.select c.enforcement).contains source && !(c.select c.enforcement).contains target ||
    c.policy.allows request)

theorem finiteNetwork_eq_model (c : Config) (header : Header)
    (request : ZeroTrust.Request String String String) :
    Certificate.finiteNetwork c.ids (c.edge header request) = c.model header request := by
  unfold Certificate.finiteNetwork model ZeroTrust.enforce packetModel
    Routing.packetNetwork Packet.Forwarding.filter Routing.network Network.restrict
  congr 1
  funext source target
  apply propext
  simp only [edge, Bool.and_eq_true, Bool.or_eq_true,
    List.contains_eq_mem, decide_eq_true_eq, Certificate.finiteNetwork]
  grind

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def unique [BEq α] (items : List α) : Bool := items.length == items.eraseDups.length

private def nameOK (name : String) : Bool :=
  !name.isEmpty && name.toList.all (fun ch => ch.isAlphanum || ch == '_' || ch == '-' || ch == '.')

private def namedList (label : String) (names : List String) : Except String Unit := do
  require (unique names) s!"Duplicate {label}."
  require (names.all nameOK) s!"Invalid {label}."

/-- Invalid references and empty selectors cannot produce a query result. -/
def validate (c : Config) : Except String Unit := do
  let _ ← c.inventory.validate
  namedList "route table" (c.routes.map (·.node))
  namedList "principal" (c.principals.map (·.id))
  namedList "resource" c.resources
  namedList "operation" c.operations
  namedList "request" (c.requests.map (·.id))
  namedList "traffic class" (c.traffic.map (·.id))
  namedList "requirement" (c.requirements.map (·.id))
  require (unique (c.links.map (fun link => (link.source, link.target)))) "Duplicate physical link."
  require (unique c.permissions) "Duplicate permission."
  require (!c.requirements.isEmpty) "Supply at least one requirement."
  require (!(c.select c.enforcement).isEmpty) "The enforcement selector has no devices."
  for link in c.links do
    require (c.ids.contains link.source && c.ids.contains link.target) "Unknown physical link endpoint."
  for table in c.routes do
    require (c.ids.contains table.node) "Unknown route table node."
    for entry in table.entries do
      match entry.nextHop with
      | none => pure ()
      | some next => require (c.ids.contains next) "Unknown route next hop."
  for permission in c.permissions do
    require ((c.principals.map (·.id)).contains permission.principal &&
      c.resources.contains permission.resource && c.operations.contains permission.operation)
      "Unknown permission reference."
  for request in c.requests do
    require ((c.principals.map (·.id)).contains request.value.principal &&
      c.resources.contains request.value.resource && c.operations.contains request.value.operation)
      "Unknown request reference."
  for query in c.requirements do
    require (!(c.select query.source).isEmpty && !(c.select query.target).isEmpty)
      s!"Empty endpoint selector in {query.id}."
    require ((c.traffic.map (·.id)).contains query.traffic) s!"Unknown traffic in {query.id}."
    require ((c.requests.map (·.id)).contains query.request) s!"Unknown request in {query.id}."
    match query.kind, query.gateways with
    | .mediated, some gateways =>
      require (!(c.select gateways).isEmpty) s!"Empty gateway selector in {query.id}."
    | .mediated, none => throw s!"Supply gateways in {query.id}."
    | _, none => pure ()
    | _, some _ => throw s!"Only a mediated requirement accepts gateways: {query.id}."

private def fields (json : Lean.Json) (required : List String) : Except String Unit := do
  let object ← json.getObj?
  for (key, _) in object.toList do
    require (required.contains key) s!"Unknown JSON field: {key}."
  for key in required do
    let _ ← json.getObjVal? key

private def str (json : Lean.Json) (key : String) : Except String String :=
  json.getObjVal? key >>= Lean.Json.getStr?

private def array (json : Lean.Json) (key : String) : Except String (List Lean.Json) := do
  return (← (← json.getObjVal? key).getArr?).toList

private def number (json : Lean.Json) : Except String Nat := json.getNat?

private def bounded (limit : Nat) (json : Lean.Json) : Except String (Fin limit) := do
  let value ← number json
  if within : value < limit then return ⟨value, within⟩
  else throw s!"Number {value} exceeds its field range."

private def optional (parse : Lean.Json → Except String α) (json : Lean.Json) : Except String (Option α) :=
  match json with
  | .null => .ok none
  | _ => some <$> parse json

private def parsePrefix (json : Lean.Json) : Except String Prefix := do
  fields json ["address", "length"]
  return ⟨← bounded 4294967296 (← json.getObjVal? "address"),
    ← bounded 33 (← json.getObjVal? "length")⟩

private def portRange (json : Lean.Json) : Except String PortRange := do
  fields json ["first", "last"]
  let first ← bounded 65536 (← json.getObjVal? "first")
  let last ← bounded 65536 (← json.getObjVal? "last")
  require (first ≤ last) "Port range bounds are reversed."
  return ⟨first, last⟩

private def packetMatch (json : Lean.Json) : Except String Match := do
  fields json ["source", "destination", "protocol", "sourcePorts", "destinationPorts"]
  return ⟨← optional parsePrefix (← json.getObjVal? "source"),
    ← optional parsePrefix (← json.getObjVal? "destination"),
    ← optional (bounded 256) (← json.getObjVal? "protocol"),
    ← optional portRange (← json.getObjVal? "sourcePorts"),
    ← optional portRange (← json.getObjVal? "destinationPorts")⟩

private def rule (json : Lean.Json) : Except String Rule := do
  fields json ["match", "action"]
  let action ← match ← str json "action" with
    | "permit" => pure Action.permit
    | "deny" => pure Action.deny
    | _ => throw "Use permit or deny for a rule action."
  return ⟨← packetMatch (← json.getObjVal? "match"), action⟩

private def link (json : Lean.Json) : Except String PhysicalLink := do
  fields json ["from", "to", "enabled", "acl"]
  return ⟨← str json "from", ← str json "to", ← (← json.getObjVal? "enabled").getBool?,
    ← (← array json "acl").mapM rule⟩

private def route (json : Lean.Json) : Except String (Routing.Entry String) := do
  fields json ["destination", "nextHop"]
  return ⟨← parsePrefix (← json.getObjVal? "destination"),
    ← optional Lean.Json.getStr? (← json.getObjVal? "nextHop")⟩

private def table (json : Lean.Json) : Except String RouteTable := do
  fields json ["node", "entries"]
  return ⟨← str json "node", ← (← array json "entries").mapM route⟩

private def principal (json : Lean.Json) : Except String Principal := do
  fields json ["id", "authenticated"]
  return ⟨← str json "id", ← (← json.getObjVal? "authenticated").getBool?⟩

private def permission (json : Lean.Json) : Except String Permission := do
  fields json ["principal", "resource", "operation"]
  return ⟨← str json "principal", ← str json "resource", ← str json "operation"⟩

private def request (json : Lean.Json) : Except String NamedRequest := do
  fields json ["id", "principal", "resource", "operation"]
  return ⟨← str json "id", ⟨← str json "principal", ← str json "resource", ← str json "operation"⟩⟩

private def trafficClass (json : Lean.Json) : Except String Traffic := do
  fields json ["id", "source", "destination", "protocol", "sourcePort", "destinationPort"]
  return ⟨← str json "id", ⟨← bounded 4294967296 (← json.getObjVal? "source"),
    ← bounded 4294967296 (← json.getObjVal? "destination"),
    ← bounded 256 (← json.getObjVal? "protocol"),
    ← bounded 65536 (← json.getObjVal? "sourcePort"),
    ← bounded 65536 (← json.getObjVal? "destinationPort")⟩⟩

private def query (json : Lean.Json) : Except String Query := do
  fields json ["id", "kind", "source", "target", "traffic", "request", "gateways"]
  let kind ← match ← str json "kind" with
    | "reach" => pure Kind.reach
    | "isolate" => pure Kind.isolate
    | "mediated" => pure Kind.mediated
    | _ => throw "Use reach, isolate, or mediated for a requirement kind."
  return ⟨← str json "id", kind, ← Selector.parse (← str json "source"),
    ← Selector.parse (← str json "target"), ← str json "traffic", ← str json "request",
    ← optional (fun value => value.getStr? >>= Selector.parse) (← json.getObjVal? "gateways")⟩

/-- Schema 1 requires every listed field and rejects unknown fields. -/
def fromJson (json : Lean.Json) : Except String Config := do
  fields json ["schema", "devices", "groups", "links", "routes", "principals", "resources",
    "operations", "permissions", "requests", "traffic", "enforcement", "requirements"]
  require ((← number (← json.getObjVal? "schema")) == 1) "Use data-plane schema 1."
  let inventory ← Netlib.Config.fromJson (Lean.Json.mkObj [
    ("devices", ← json.getObjVal? "devices"), ("groups", ← json.getObjVal? "groups"),
    ("links", Lean.toJson ([] : List Lean.Json))])
  let config : Config := ⟨inventory.devices, inventory.groups,
    ← (← array json "links").mapM link, ← (← array json "routes").mapM table,
    ← (← array json "principals").mapM principal,
    ← (← array json "resources").mapM Lean.Json.getStr?,
    ← (← array json "operations").mapM Lean.Json.getStr?,
    ← (← array json "permissions").mapM permission,
    ← (← array json "requests").mapM request,
    ← (← array json "traffic").mapM trafficClass,
    ← Selector.parse (← str json "enforcement"), ← (← array json "requirements").mapM query⟩
  config.validate
  return config

def parse (text : String) : Except String Config := Lean.Json.parse text >>= fromJson

end Config
end Netlib.DataPlane
