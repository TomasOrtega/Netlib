import Netlib.Check.FederatedCohortContext
import Netlib.Check.FederatedPacketJson

namespace Netlib.Federation.Cohort

structure Bundle where
  input : Input
  profile : Profile
  headers : List Packet.Header
  actions : List InFlight.Action
  serviceBound : Nat

namespace Json

private def fields := Import.PacketFields.fields

private def nat (json : Lean.Json) (key : String) : Except String Nat :=
  json.getObjVal? key >>= Lean.Json.getNat?

private def array (json : Lean.Json) (key : String) : Except String (List Lean.Json) := do
  return (← (← json.getObjVal? key).getArr?).toList

def capacity (json : Lean.Json) : Except String Capacity := do
  fields json ["node", "slots"]
  return ⟨← InFlight.Json.node (← json.getObjVal? "node"), ← nat json "slots"⟩

def capacityJson (value : Capacity) : Lean.Json :=
  Lean.Json.mkObj [("node", InFlight.Json.nodeJson value.node), ("slots", Lean.toJson value.slots)]

def profile (json : Lean.Json) : Except String Profile := do
  fields json ["packets", "capacities", "limits"]
  let limits ← json.getObjVal? "limits"
  fields limits ["classes", "states", "edges", "work"]
  let capacities ← (← array json "capacities").mapM capacity
  unless decide (capacities.map (·.node)).Nodup do throw "The raw cohort repeats a capacity row."
  return ⟨← (← array json "packets").mapM InFlight.Json.profile, capacities,
    ⟨← nat limits "classes", ← nat limits "states", ← nat limits "edges", ← nat limits "work"⟩⟩

def profileJson (value : Profile) : Lean.Json :=
  Lean.Json.mkObj [
    ("packets", .arr (value.packets.map InFlight.Json.profileJson).toArray),
    ("capacities", .arr (value.capacities.map capacityJson).toArray),
    ("limits", Lean.Json.mkObj [
      ("classes", Lean.toJson value.limits.classes), ("states", Lean.toJson value.limits.states),
      ("edges", Lean.toJson value.limits.edges), ("work", Lean.toJson value.limits.work)])]

def fromJson (json : Lean.Json) : Except String Bundle := do
  fields json ["schema", "scope", "deployment", "profile", "headers", "actions", "serviceBound"]
  unless (← nat json "schema") == 1 do throw "Use packet cohort schema 1."
  unless (← (← json.getObjVal? "scope").getStr?) == "two-domain-packet-cohorts" do
    throw "Unsupported packet cohort scope."
  return ⟨← Federation.Json.fromJson (← json.getObjVal? "deployment"),
    ← profile (← json.getObjVal? "profile"),
    ← (← array json "headers").mapM Import.PacketFields.header,
    ← (← array json "actions").mapM InFlight.Json.action, ← nat json "serviceBound"⟩

def parse (text : String) : Except String Bundle := do
  fromJson (← Import.Json.parse text)

end Json
end Netlib.Federation.Cohort
