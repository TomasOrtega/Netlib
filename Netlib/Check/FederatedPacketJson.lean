import Netlib.Model.FederatedPacketExecution
import Netlib.Import.PacketFields

/-!
# Raw packet operations and native deployment inputs

The parser preserves supplied observations and send indices. Replay derives
sender epochs, effects, and endpoint receipt from the actual stored actions.
-/

namespace Netlib.Federation.InFlight

structure Bundle where
  deployment : Input
  profile : Profile
  header : Packet.Header
  actions : List Action
  serviceBound : Nat

namespace Json

private def fields := Import.PacketFields.fields

private def str (json : Lean.Json) (key : String) : Except String String :=
  json.getObjVal? key >>= Lean.Json.getStr?

private def nat (json : Lean.Json) (key : String) : Except String Nat :=
  json.getObjVal? key >>= Lean.Json.getNat?

private def array (json : Lean.Json) (key : String) : Except String (List Lean.Json) := do
  return (← (← json.getObjVal? key).getArr?).toList

def node (json : Lean.Json) : Except String Node := do
  fields json ["side", "node"]
  let name ← str json "node"
  match ← str json "side" with
  | "left" => return .inl name
  | "right" => return .inr name
  | value => throw s!"Unknown packet operator side: {value}."

def nodeJson : Node → Lean.Json
  | .inl name => Lean.Json.mkObj [("side", Lean.toJson "left"), ("node", Lean.toJson name)]
  | .inr name => Lean.Json.mkObj [("side", Lean.toJson "right"), ("node", Lean.toJson name)]

def observation (json : Lean.Json) : Except String Observation := do
  fields json ["packetID", "header", "node"]
  return ⟨← str json "packetID", ← Import.PacketFields.header (← json.getObjVal? "header"),
    ← node (← json.getObjVal? "node")⟩

def observationJson (value : Observation) : Lean.Json :=
  Lean.Json.mkObj [("packetID", Lean.toJson value.packetID),
    ("header", Import.PacketFields.headerJson value.header), ("node", nodeJson value.node)]

def action (json : Lean.Json) : Except String Action := do
  match ← str json "kind" with
  | "idle" =>
    fields json ["kind"]
    return .idle
  | "send" =>
    fields json ["kind", "observation", "target"]
    return .send (← observation (← json.getObjVal? "observation")) (← node (← json.getObjVal? "target"))
  | "arrive" =>
    fields json ["kind", "observation", "sendIndex"]
    return .arrive (← observation (← json.getObjVal? "observation")) (← nat json "sendIndex")
  | "receive" =>
    fields json ["kind", "observation"]
    return .receive (← observation (← json.getObjVal? "observation"))
  | "updateLeft" =>
    fields json ["kind", "index"]
    return .updateLeft (← nat json "index")
  | "updateRight" =>
    fields json ["kind", "index"]
    return .updateRight (← nat json "index")
  | "updateBoth" =>
    fields json ["kind", "leftIndex", "rightIndex"]
    return .updateBoth (← nat json "leftIndex") (← nat json "rightIndex")
  | value => throw s!"Unknown packet action: {value}."

def actionJson : Action → Lean.Json
  | .idle => Lean.Json.mkObj [("kind", Lean.toJson "idle")]
  | .send observed target => Lean.Json.mkObj [("kind", Lean.toJson "send"),
      ("observation", observationJson observed), ("target", nodeJson target)]
  | .arrive observed index => Lean.Json.mkObj [("kind", Lean.toJson "arrive"),
      ("observation", observationJson observed), ("sendIndex", Lean.toJson index)]
  | .receive observed => Lean.Json.mkObj [("kind", Lean.toJson "receive"),
      ("observation", observationJson observed)]
  | .updateLeft index => Lean.Json.mkObj [("kind", Lean.toJson "updateLeft"), ("index", Lean.toJson index)]
  | .updateRight index => Lean.Json.mkObj [("kind", Lean.toJson "updateRight"), ("index", Lean.toJson index)]
  | .updateBoth first second => Lean.Json.mkObj [("kind", Lean.toJson "updateBoth"),
      ("leftIndex", Lean.toJson first), ("rightIndex", Lean.toJson second)]

private def fenceRows (json : Lean.Json) : Except String (List (List String)) := do
  let rows ← json.getArr?
  rows.toList.mapM fun row => do
    (← row.getArr?).toList.mapM Lean.Json.getStr?

def profile (json : Lean.Json) : Except String Profile := do
  fields json ["query", "packetID", "fences", "limits"]
  let fences ← json.getObjVal? "fences"
  fields fences ["left", "right"]
  let limits ← json.getObjVal? "limits"
  fields limits ["cells", "work"]
  return ⟨← str json "query", ← str json "packetID",
    ← fenceRows (← fences.getObjVal? "left"), ← fenceRows (← fences.getObjVal? "right"),
    ← nat limits "cells", ← nat limits "work"⟩

def profileJson (value : Profile) : Lean.Json :=
  Lean.Json.mkObj [("query", Lean.toJson value.queryID), ("packetID", Lean.toJson value.packetID),
    ("fences", Lean.Json.mkObj [("left", Lean.toJson value.leftFences), ("right", Lean.toJson value.rightFences)]),
    ("limits", Lean.Json.mkObj [("cells", Lean.toJson value.cells), ("work", Lean.toJson value.work)])]

def fromJson (json : Lean.Json) : Except String Bundle := do
  fields json ["schema", "scope", "deployment", "profile", "header", "actions", "serviceBound"]
  unless (← nat json "schema") == 1 do throw "Use packet update schema 1."
  unless (← str json "scope") == "two-domain-packet-updates" do throw "Unsupported packet update scope."
  return ⟨← Federation.Json.fromJson (← json.getObjVal? "deployment"),
    ← profile (← json.getObjVal? "profile"), ← Import.PacketFields.header (← json.getObjVal? "header"),
    ← (← array json "actions").mapM action, ← nat json "serviceBound"⟩

def parse (text : String) : Except String Bundle := do
  fromJson (← Import.Json.parse text)

end Json
end Netlib.Federation.InFlight
