import Netlib.Compile.ACL
import Netlib.Import.Json
import Netlib.Model.DataPlane

namespace Netlib.Compile.Policy

private def fields (json : Lean.Json) (names : List String) : Except String Unit := do
  let object ← json.getObj?
  for (key, _) in object.toList do
    if !names.contains key then throw s!"Unknown intent field: {key}."
  for key in names do
    let _ ← json.getObjVal? key

/-- The input gives unordered permit and hard-deny requirements over packet classes. -/
def fromJson (json : Lean.Json) : Except String (List ACL.Intent) := do
  fields json ["schema", "requirements"]
  if (← (← json.getObjVal? "schema").getNat?) != 1 then throw "Use intent schema 1."
  let requirements ← (← json.getObjVal? "requirements").getArr?
  requirements.toList.mapM fun requirement => do
    fields requirement ["id", "action", "match"]
    let id ← (← requirement.getObjVal? "id").getStr?
    let action ← match ← (← requirement.getObjVal? "action").getStr? with
      | "permit" => pure Packet.Action.permit
      | "deny" => pure Packet.Action.deny
      | _ => throw "Use permit or deny for an intent action."
    let test ← DataPlane.Config.parseTrafficSelection (← requirement.getObjVal? "match").compress
    return ⟨id, test, action⟩

def parse (text : String) : Except String (List ACL.Intent) := do
  fromJson (← Netlib.Import.Json.parse text)

end Netlib.Compile.Policy
