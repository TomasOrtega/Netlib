import Lean

namespace Netlib

structure Device where
  id : String
  zone : String
  role : String
  deriving Repr, BEq, DecidableEq

structure Link where
  source : String
  target : String
  service : String
  enabled : Bool
  deriving Repr, BEq, DecidableEq

structure Group where
  name : String
  members : List String
  deriving Repr, BEq, DecidableEq

structure Config where
  devices : List Device
  links : List Link
  groups : List Group
  deriving Repr, BEq

inductive Selector where
  | node (name : String)
  | zone (name : String)
  | role (name : String)
  | group (name : String)
  deriving Repr, BEq, DecidableEq

private def validIdentifier (s : String) : Bool :=
  !s.isEmpty && s.toList.all (fun ch => ch.isAlphanum || ch == '_' || ch == '-' || ch == '.')

namespace Selector

def render : Selector → String
  | .node n => "node:" ++ n
  | .zone n => "zone:" ++ n
  | .role n => "role:" ++ n
  | .group n => "group:" ++ n

def parse (text : String) : Except String Selector :=
  match text.splitOn ":" with
  | [kind, name] =>
    if !validIdentifier name then .error "invalid or empty selector name"
    else match kind with
      | "node" => .ok (.node name)
      | "zone" => .ok (.zone name)
      | "role" => .ok (.role name)
      | "group" => .ok (.group name)
      | _ => .error s!"unknown selector kind: {kind}"
  | _ => .error s!"expected kind:name selector: {text}"

end Selector

namespace Config

def ids (c : Config) : List String := c.devices.map (·.id)

def select (c : Config) : Selector → List String
  | .node n => c.ids.filter (· == n)
  | .zone z => (c.devices.filter (·.zone == z)).map (·.id)
  | .role r => (c.devices.filter (·.role == r)).map (·.id)
  | .group g => ((c.groups.find? (·.name == g)).map (·.members)).getD []

def edge (c : Config) (service source target : String) : Bool :=
  c.links.any fun link => link.enabled && link.source == source && link.target == target &&
    (link.service == "*" || link.service == service)

private def unique (xs : List String) : Bool := xs.length == xs.eraseDups.length

private def validName := validIdentifier

private def require (ok : Bool) (message : String) : Except String Unit :=
  if ok then .ok () else .error message

def validate (c : Config) : Except String Config := do
  require (!c.devices.isEmpty) "configuration must contain devices"
  require (unique c.ids) "duplicate device ID"
  require (unique (c.groups.map (·.name))) "duplicate group name"
  for d in c.devices do
    require (validName d.id && validName d.zone && validName d.role)
      s!"invalid device identifier, zone or role: {d.id}"
  for link in c.links do
    require (c.ids.contains link.source && c.ids.contains link.target)
      s!"dangling link: {link.source} -> {link.target}"
    require (validName link.service || link.service == "*") "invalid link service"
  for group in c.groups do
    require (validName group.name) "invalid group name"
    require (!group.members.isEmpty) s!"empty group: {group.name}"
    require (unique group.members) s!"duplicate group member: {group.name}"
    require (group.members.all c.ids.contains) s!"unknown group member: {group.name}"
  return c

private def fields (j : Lean.Json) (expected : List String) : Except String Unit := do
  let obj ← j.getObj?
  for (key, _) in obj.toList do
    require (expected.contains key) s!"unknown JSON field: {key}"
  for key in expected do
    let _ ← j.getObjVal? key

private def str (j : Lean.Json) (key : String) : Except String String := do
  (← j.getObjVal? key).getStr?

private def deviceFromJson (j : Lean.Json) : Except String Device := do
  fields j ["id", "zone", "role"]
  return ⟨← str j "id", ← str j "zone", ← str j "role"⟩

private def linkFromJson (j : Lean.Json) : Except String Link := do
  fields j ["from", "to", "service", "enabled"]
  return ⟨← str j "from", ← str j "to", ← str j "service",
    ← (← j.getObjVal? "enabled").getBool?⟩

private def groupFromJson (j : Lean.Json) : Except String Group := do
  fields j ["name", "members"]
  let members ← (← j.getObjVal? "members").getArr?
  return ⟨← str j "name", ← members.toList.mapM Lean.Json.getStr?⟩

def fromJson (j : Lean.Json) : Except String Config := do
  fields j ["devices", "links", "groups"]
  let devices ← (← j.getObjVal? "devices").getArr?
  let links ← (← j.getObjVal? "links").getArr?
  let groups ← (← j.getObjVal? "groups").getArr?
  validate ⟨← devices.toList.mapM deviceFromJson, ← links.toList.mapM linkFromJson,
    ← groups.toList.mapM groupFromJson⟩

def parse (text : String) : Except String Config := do
  fromJson (← Lean.Json.parse text)

end Config
end Netlib
