import Netlib.Check.Transfer
import Netlib.Import.PacketFields
import Netlib.Model.DataPlane

namespace Netlib.Import.TransferConfig

open Netlib.Check.Transfer

structure Input where
  config : Check.Transfer.Config
  query : Check.Transfer.Query

private def str (json : Lean.Json) (key : String) : Except String String :=
  json.getObjVal? key >>= Lean.Json.getStr?

private def link (json : Lean.Json) : Except String Check.Transfer.Link := do
  PacketFields.fields json ["from", "to", "match", "rewrite"]
  let guard ← DataPlane.Config.parseTrafficSelection (← json.getObjVal? "match").compress
  return ⟨← str json "from", ← str json "to", guard,
    ← PacketFields.rewrite (← json.getObjVal? "rewrite")⟩

def Input.fromJson (json : Lean.Json) : Except String Input := do
  PacketFields.fields json ["schema", "nodes", "links", "query"]
  if (← (← json.getObjVal? "schema").getNat?) != 1 then throw "Use transfer schema 1."
  let nodes ← (← (← json.getObjVal? "nodes").getArr?).toList.mapM Lean.Json.getStr?
  let values ← (← json.getObjVal? "links").getArr?
  let mut links := []
  for index in [:values.size] do
    let value ← (link values[index]!).mapError (s!"/links/{index}: " ++ ·)
    links := links ++ [value]
  let config : Check.Transfer.Config := ⟨nodes, links⟩
  config.validate
  let q ← json.getObjVal? "query"
  PacketFields.fields q ["kind", "source", "target", "header", "gateways"]
  let kind ← match ← str q "kind" with
    | "reach" => pure Kind.reach
    | "isolate" => pure Kind.isolate
    | "mediated" => pure Kind.mediated
    | _ => throw "Use reach, isolate, or mediated for the transfer query."
  let gateways ← (← (← q.getObjVal? "gateways").getArr?).toList.mapM Lean.Json.getStr?
  if kind == .mediated && gateways.isEmpty then throw "Supply transfer gateways for mediation."
  if kind != .mediated && !gateways.isEmpty then throw "Only mediation accepts transfer gateways."
  let source ← str q "source"
  let target ← str q "target"
  let initial ← PacketFields.header (← q.getObjVal? "header")
  let query : Check.Transfer.Query := ⟨kind, source, target, initial, gateways⟩
  query.validate config
  return ⟨config, query⟩

def Input.parse (text : String) : Except String Input := do
  Input.fromJson (← Json.parse text)

def stateJson (state : State) : Lean.Json :=
  Lean.Json.mkObj [("node", Lean.toJson state.1), ("packet", PacketFields.headerJson state.2)]

private def evidenceJson (states : Option (List State)) : Lean.Json :=
  (states.map (fun values => Lean.toJson (values.map stateJson))).getD .null

def resultJson (input : Input) (result : Check.Transfer.Result input.config input.query) : Lean.Json :=
  Lean.Json.mkObj [
    ("compliant", Lean.toJson result.value),
    ("kind", Lean.toJson (match input.query.kind with
      | .reach => "reach" | .isolate => "isolate" | .mediated => "mediated")),
    ("scope", Lean.toJson "fixed-input-header-changing-forwarding"),
    ("stateCount", Lean.toJson (input.config.stateCount input.query.initial)),
    ("source", Lean.toJson input.query.source), ("target", Lean.toJson input.query.target),
    ("initial", PacketFields.headerJson input.query.initial),
    ("gateways", Lean.toJson input.query.gateways),
    ("endpointGateway", Lean.toJson (input.query.kind == .mediated &&
      (input.query.gateways.contains input.query.source || input.query.gateways.contains input.query.target))),
    ("path", evidenceJson result.path?), ("cut", evidenceJson result.cut?)]

def render (input : Input) (result : Check.Transfer.Result input.config input.query) : String :=
  let verdict := if result.value then "COMPLIANT" else "NONCOMPLIANT"
  let path := match result.path? with
    | some states => states.map fun state => s!"{state.1}: {(PacketFields.headerJson state.2).compress}"
    | none => []
  let cut := match result.cut? with
    | some states => [s!"Closed cut contains {states.length} packet states."]
    | none => []
  String.intercalate "\n" (verdict :: "Scope: one input packet with explicit header transformations." :: path ++ cut)

end Netlib.Import.TransferConfig
