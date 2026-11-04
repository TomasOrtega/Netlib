import Netlib.Import.LinuxDeployment
import Netlib.Check.DataPlane

namespace NetlibTest.LinuxDeployment

open Netlib
open Netlib.Import.LinuxDeployment

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def field (json : Lean.Json) (key : String) : IO Lean.Json := unwrap (json.getObjVal? key)

private def update (json : Lean.Json) (key : String) (value : Lean.Json) : IO Lean.Json := do
  let fields ← unwrap json.getObj?
  return Lean.Json.mkObj ((fields.toList.filter (·.1 != key)) ++ [(key, value)])

private def modifyRouter (json : Lean.Json) (change : Lean.Json → IO Lean.Json) : IO Lean.Json := do
  let routers ← unwrap ((← field json "routers").getArr?)
  match routers.toList with
  | [] => throw (IO.userError "The fixture needs a router.")
  | first :: rest => update json "routers" (.arr ((← change first) :: rest).toArray)

private def rejected (json : Lean.Json) : IO Unit := do
  match Snapshot.fromJson json with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "The invalid Linux bundle passed.")

private def scenarioTests : IO Unit := do
  let parsed ← unwrap (Snapshot.parse (← IO.FS.readFile "examples/linux/deployment.json"))
  let report ← unwrap (DataPlane.Check.check parsed.compile)
  ensure report.compliant "The source-derived deployment must satisfy its intent."
  ensure (parsed.routers.length == parsed.intent.devices.length) "Every modeled device needs one router snapshot."
  ensure (parsed.compile.routes.length == parsed.routers.length) "Each router must supply one compiled route table."
  for router in parsed.routers do
    ensure (router.routeVersion == "6.19.0" && router.nftables.version == "1.1.3")
      "The bundle must preserve both native producer versions."
    ensure (router.sourceID == s!"/routers/{router.index}") "Router provenance must preserve the array index."
    for (route, index) in router.routes.routes.zipIdx do
      ensure (route.index == index) "Native route indices must survive bundle import."
    for rule in router.nftables.rules do
      ensure (!rule.sourceID.isEmpty && !rule.expressionIndices.isEmpty)
        "Native rule provenance must survive bundle import."
  let nodes := parsed.intent.ids ++ ["unknown"]
  for traffic in parsed.intent.traffic do
    for request in parsed.intent.requests do
      for source in nodes do
        for target in nodes do
          ensure (parsed.compile.edge traffic.header request.value source target ==
            parsed.nativeEdge traffic.header request.value source target)
            "Compiled forwarding must agree with the source snapshots for every tested endpoint."
  for name in ["deny-first", "route-drop", "bypass", "management-leak"] do
    let changed ← unwrap (Snapshot.parse (← IO.FS.readFile s!"examples/linux/{name}.json"))
    let changedReport ← unwrap (DataPlane.Check.check changed.compile)
    ensure (!changedReport.compliant) s!"The {name} mutation must violate the intent."

private def captureTests : IO Unit := do
  let parsed ← unwrap (Netlib.Import.Nftables.Snapshot.parse
    (← IO.FS.readFile "examples/linux/captured-nftables.json"))
  ensure (parsed.version == "1.1.3" && parsed.table == "netlib_capture")
    "The genuine capture must preserve its producer and table identity."
  let packet : Packet.Header := ⟨3221225985, 3325256705, Packet.Protocol.tcp, 12000, 443⟩
  ensure (parsed.compile.allows packet) "The native captured rule must permit the selected HTTPS header."
  ensure (!(parsed.compile.allows { packet with protocol := Packet.Protocol.udp }))
    "A native TCP payload match must exclude UDP headers."
  ensure (!(parsed.compile.allows { packet with destinationPort := 22 }))
    "The native captured drop policy must exclude unmatched ports."

private def rejectionTests : IO Unit := do
  let json ← unwrap (Netlib.Import.Json.parse (← IO.FS.readFile "examples/linux/deployment.json"))
  rejected (← update json "schema" (Lean.toJson (2 : Nat)))
  rejected (← update json "scope" (.str "all-linux-forwarding"))
  rejected (← update json "unexpected" .null)
  let intent ← field json "intent"
  rejected (← update json "intent" (← update intent "links" (.arr #[])))
  rejected (← update json "intent" (← update intent "routes" (.arr #[])))
  let routers ← unwrap ((← field json "routers").getArr?)
  rejected (← update json "routers" (.arr #[]))
  rejected (← update json "routers" (.arr (routers ++ routers)))
  rejected (← modifyRouter json (fun router => update router "node" (.str "unknown")))
  rejected (← modifyRouter json (fun router => update router "routeVersion" (.str "6.18.0")))
  rejected (← modifyRouter json (fun router => update router "acl" (.arr #[])))
  rejected (← modifyRouter json (fun router => do
    let bindings ← unwrap ((← field router "bindings").getArr?)
    update router "bindings" (.arr (bindings ++ bindings))))
  rejected (← modifyRouter json (fun router => do
    let bindings ← unwrap ((← field router "bindings").getArr?)
    match bindings.toList with
    | first :: rest =>
      update router "bindings" (.arr ((← update first "nextNode" (.str "unknown")) :: rest).toArray)
    | [] => throw (IO.userError "The fixture needs an output binding.")))
  rejected (← modifyRouter json (fun router => do
    let bindings ← unwrap ((← field router "bindings").getArr?)
    match bindings.toList with
    | first :: rest =>
      update router "bindings" (.arr ((← update first "gateway" (.str "2001:db8::1")) :: rest).toArray)
    | [] => throw (IO.userError "The fixture needs an output binding.")))
  rejected (← modifyRouter json (fun router => do
    let bindings ← unwrap ((← field router "bindings").getArr?)
    match bindings.toList with
    | first :: rest =>
      let duplicate ← update first "device" (.str "other0")
      update router "bindings" (.arr (first :: duplicate :: rest).toArray)
    | [] => throw (IO.userError "The fixture needs an output binding.")))
  let missing := (routers.toList.drop 1).toArray
  rejected (← update json "routers" (.arr missing))

example (snapshot : Snapshot) (header : Packet.Header)
    (request : ZeroTrust.Request String String String) :
    snapshot.compile.model header request = snapshot.nativeModel header request :=
  snapshot.model_correct header request

def run : IO Unit := do
  scenarioTests
  captureTests
  rejectionTests
  IO.println "Linux deployment tests passed."

end NetlibTest.LinuxDeployment
