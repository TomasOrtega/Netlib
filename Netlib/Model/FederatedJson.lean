import Netlib.Model.DomainContract

/-!
# Native federation input

Each operator supplies its own native snapshots and public node bindings.
The two supplied limits bound finite packet and graph checking work.
-/

namespace Netlib.Federation

structure Input where
  left : Plan
  right : Plan
  intent : Intent
  cells : Nat
  work : Nat

namespace Json

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def fields (json : Lean.Json) (required : List String) : Except String Unit := do
  let object ← json.getObj?
  for (key, _) in object.toList do
    require (required.contains key) s!"Unknown federation field: {key}."
  for key in required do
    let _ ← json.getObjVal? key

private def str (json : Lean.Json) (key : String) : Except String String :=
  json.getObjVal? key >>= Lean.Json.getStr?

private def nat (json : Lean.Json) (key : String) : Except String Nat :=
  json.getObjVal? key >>= Lean.Json.getNat?

private def array (json : Lean.Json) (key : String) : Except String (List Lean.Json) := do
  return (← (← json.getObjVal? key).getArr?).toList

private def role : String → Except String Role
  | "endpoint" => .ok .endpoint
  | "enforcement" => .ok .enforcement
  | "ingress" => .ok .ingress
  | "egress" => .ok .egress
  | "internal" => .ok .internal
  | value => .error s!"Unknown public node role: {value}."

private def publicNode (json : Lean.Json) : Except String PublicNode := do
  fields json ["id", "role"]
  return ⟨← str json "id", ← role (← str json "role")⟩

private def arc (json : Lean.Json) : Except String Arc := do
  fields json ["source", "target"]
  return ⟨← str json "source", ← str json "target"⟩

private def request (json : Lean.Json) : Except String (ZeroTrust.Request String String String) := do
  fields json ["principal", "resource", "operation"]
  return ⟨← str json "principal", ← str json "resource", ← str json "operation"⟩

private def packetCase (json : Lean.Json) : Except String Case := do
  fields json ["id", "selector", "request", "upper", "must"]
  let selection ← DataPlane.Config.parseTrafficSelection (← json.getObjVal? "selector").compress
  return ⟨← str json "id", selection, ← request (← json.getObjVal? "request"),
    ← (← array json "upper").mapM arc, ← (← array json "must").mapM arc⟩

def contract (json : Lean.Json) : Except String Contract := do
  fields json ["id", "version", "nodes", "cases"]
  return ⟨← str json "id", ← nat json "version", ← (← array json "nodes").mapM publicNode,
    ← (← array json "cases").mapM packetCase⟩

private def nodeMap (json : Lean.Json) : Except String NodeMap := do
  fields json ["localNode", "publicNode"]
  return ⟨← str json "localNode", ← str json "publicNode"⟩

private def anchor (json : Lean.Json) : Except String Anchor := do
  fields json ["publicNode", "localNode"]
  return ⟨← str json "publicNode", ← str json "localNode"⟩

def revision (json : Lean.Json) : Except String Revision := do
  fields json ["id", "snapshot", "projection", "anchors"]
  let snapshot ← Import.LinuxDeployment.Snapshot.fromJson (← json.getObjVal? "snapshot")
  return ⟨← str json "id", snapshot, ← (← array json "projection").mapM nodeMap,
    ← (← array json "anchors").mapM anchor⟩

def plan (json : Lean.Json) : Except String Plan := do
  fields json ["contract", "initial", "updates"]
  return ⟨← contract (← json.getObjVal? "contract"), ← revision (← json.getObjVal? "initial"),
    ← (← array json "updates").mapM revision⟩

private def side : String → Except String Side
  | "left" => .ok .left
  | "right" => .ok .right
  | value => .error s!"Unknown operator side: {value}."

private def reference (json : Lean.Json) : Except String PublicRef := do
  fields json ["side", "node"]
  return ⟨← side (← str json "side"), ← str json "node"⟩

private def border (json : Lean.Json) : Except String Border := do
  fields json ["source", "target", "sourceDomain", "targetDomain", "sourceVersion", "targetVersion", "cases"]
  return ⟨← reference (← json.getObjVal? "source"), ← reference (← json.getObjVal? "target"),
    ← str json "sourceDomain", ← str json "targetDomain", ← nat json "sourceVersion", ← nat json "targetVersion",
    ← (← array json "cases").mapM Lean.Json.getStr?⟩

private def kind : String → Except String DataPlane.Kind
  | "reach" => .ok .reach
  | "isolate" => .ok .isolate
  | "mediated" => .ok .mediated
  | value => .error s!"Unknown federation query kind: {value}."

private def query (json : Lean.Json) : Except String Query := do
  fields json ["id", "kind", "case", "source", "target", "gateways"]
  return ⟨← str json "id", ← kind (← str json "kind"), ← str json "case",
    ← reference (← json.getObjVal? "source"), ← reference (← json.getObjVal? "target"),
    ← (← array json "gateways").mapM reference⟩

def intent (json : Lean.Json) : Except String Intent := do
  fields json ["borders", "queries"]
  return ⟨← (← array json "borders").mapM border, ← (← array json "queries").mapM query⟩

def fromJson (json : Lean.Json) : Except String Input := do
  fields json ["schema", "scope", "left", "right", "intent", "limits"]
  require ((← nat json "schema") == 1) "Use federation schema 1."
  require ((← str json "scope") == "two-domain-ipv4-transit") "Unsupported federation scope."
  let limits ← json.getObjVal? "limits"
  fields limits ["cells", "work"]
  return ⟨← plan (← json.getObjVal? "left"), ← plan (← json.getObjVal? "right"),
    ← intent (← json.getObjVal? "intent"), ← nat limits "cells", ← nat limits "work"⟩

def parse (text : String) : Except String Input := do
  fromJson (← Netlib.Import.Json.parse text)

end Json
end Netlib.Federation
