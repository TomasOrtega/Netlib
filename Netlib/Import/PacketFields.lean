import Netlib.Import.IPv4
import Netlib.Import.Json
import Netlib.Packet.Rewrite

namespace Netlib.Import.PacketFields

def fields (json : Lean.Json) (names : List String) : Except String Unit := do
  let object ← json.getObj?
  for (key, _) in object.toList do
    if !names.contains key then throw s!"Unknown packet or event field: {key}."
  for key in names do
    let _ ← json.getObjVal? key

private def bounded (size : Nat) (json : Lean.Json) : Except String (Fin size) := do
  let value ← json.getNat?
  if fits : value < size then return ⟨value, fits⟩
  else throw s!"Packet value {value} exceeds its {size}-value field."

def addressText (address : Packet.Address) : String :=
  s!"{address.val / 16777216}.{address.val / 65536 % 256}.{address.val / 256 % 256}.{address.val % 256}"

def endpoint (json : Lean.Json) : Except String Packet.Endpoint := do
  fields json ["address", "port"]
  return ⟨← IPv4.parseAddress (← (← json.getObjVal? "address").getStr?),
    ← bounded 65536 (← json.getObjVal? "port")⟩

def endpointJson (value : Packet.Endpoint) : Lean.Json :=
  Lean.Json.mkObj [("address", Lean.toJson (addressText value.address)), ("port", Lean.toJson value.port.val)]

def header (json : Lean.Json) : Except String Packet.Header := do
  fields json ["source", "destination", "protocol", "sourcePort", "destinationPort"]
  return ⟨← IPv4.parseAddress (← (← json.getObjVal? "source").getStr?),
    ← IPv4.parseAddress (← (← json.getObjVal? "destination").getStr?),
    ← bounded 256 (← json.getObjVal? "protocol"),
    ← bounded 65536 (← json.getObjVal? "sourcePort"),
    ← bounded 65536 (← json.getObjVal? "destinationPort")⟩

def headerJson (value : Packet.Header) : Lean.Json :=
  Lean.Json.mkObj [
    ("source", Lean.toJson (addressText value.source)),
    ("destination", Lean.toJson (addressText value.destination)),
    ("protocol", Lean.toJson value.protocol.val),
    ("sourcePort", Lean.toJson value.sourcePort.val),
    ("destinationPort", Lean.toJson value.destinationPort.val)]

def optionalHeader (json : Lean.Json) : Except String (Option Packet.Header) := do
  match json with
  | .null => return none
  | _ => some <$> header json

def optionalHeaderJson (value : Option Packet.Header) : Lean.Json :=
  (value.map headerJson).getD .null

private def optional (parser : Lean.Json → Except String α) (json : Lean.Json) : Except String (Option α) :=
  match json with
  | .null => .ok none
  | _ => some <$> parser json

def rewrite (json : Lean.Json) : Except String Packet.Rewrite := do
  fields json ["source", "destination", "protocol", "sourcePort", "destinationPort"]
  return ⟨← optional (fun value => do IPv4.parseAddress (← value.getStr?)) (← json.getObjVal? "source"),
    ← optional (fun value => do IPv4.parseAddress (← value.getStr?)) (← json.getObjVal? "destination"),
    ← optional (bounded 256) (← json.getObjVal? "protocol"),
    ← optional (bounded 65536) (← json.getObjVal? "sourcePort"),
    ← optional (bounded 65536) (← json.getObjVal? "destinationPort")⟩

end Netlib.Import.PacketFields
