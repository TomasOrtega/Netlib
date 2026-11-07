import Netlib.Model.FederatedJson
import NetlibTest.FederatedNativeFixture

namespace NetlibTest.FederatedDeploymentInputs

open Netlib Federation

def mapVersions (plan : Plan) (change : Revision → Revision) : Plan :=
  { plan with initial := change plan.initial, updates := plan.updates.map change }

def writeRequest (input : Input) : Input :=
  let contract := { input.right.contract with cases := input.right.contract.cases.map fun selected =>
    { selected with request := { selected.request with operation := "write" } } }
  let right := mapVersions { input.right with contract } fun revision =>
    let intent := revision.snapshot.intent
    let intent := { intent with
      operations := intent.operations ++ ["write"]
      permissions := intent.permissions ++ [⟨"alice", "documents", "write"⟩]
      requests := intent.requests ++ [⟨"alice-write", ⟨"alice", "documents", "write"⟩⟩] }
    { revision with snapshot := { revision.snapshot with intent } }
  { input with right }

def selectorMismatch (input : Input) : Input :=
  let contract := { input.right.contract with cases := input.right.contract.cases.map fun selected =>
    { selected with selector := { selected.selector with sourcePorts := some ⟨4096, 50000⟩ } } }
  { input with right := { input.right with contract } }

def missingMust (input : Input) : Input :=
  let contract := { input.left.contract with cases := input.left.contract.cases.map fun selected =>
    { selected with must := [] } }
  { input with left := { input.left with contract } }

def unsafeIntermediate (input : Input) (denied : Revision) : Except String Input := do
  let some current := input.left.updates[0]? | throw "The intermediate native revision is absent."
  let updates := { denied with id := current.id } :: input.left.updates.drop 1
  return { input with left := { input.left with updates } }

def badNativeScope (json : Lean.Json) : Except String Lean.Json := do
  let left ← json.getObjVal? "left"
  let initial ← left.getObjVal? "initial"
  let snapshot ← initial.getObjVal? "snapshot"
  return json.setObjVal! "left" (left.setObjVal! "initial"
    (initial.setObjVal! "snapshot" (snapshot.setObjVal! "scope" (.str "unsupported-native-scope"))))

private def bypassRevision (revision : Lean.Json) : Except String Lean.Json := do
  let snapshot ← revision.getObjVal? "snapshot"
  let routers ← (← snapshot.getObjVal? "routers").getArr?
  let some ingress := routers[0]? | throw "The native ingress router is absent."
  let binding := Lean.Json.mkObj [
    ("device", .str "edge0"), ("nextNode", .str "egress"), ("gateway", .null)]
  let route := Lean.Json.mkObj [
    ("dst", .str "198.51.100.0/24"), ("dev", .str "edge0"),
    ("protocol", .str "static"), ("scope", .str "link"), ("flags", .arr #[])]
  let changed := (ingress.setObjVal! "bindings" (.arr #[binding])).setObjVal! "routes" (.arr #[route])
  return revision.setObjVal! "snapshot" (snapshot.setObjVal! "routers" (.arr (routers.set! 0 changed)))

def nativeBypass (json : Lean.Json) : Except String Input := do
  let left ← json.getObjVal? "left"
  let contract ← left.getObjVal? "contract"
  let cases ← (← contract.getObjVal? "cases").getArr?
  let direct := Lean.Json.mkObj [("source", .str "client"), ("target", .str "east")]
  let mut changedCases := #[]
  for selected in cases do
    let upper ← (← selected.getObjVal? "upper").getArr?
    let mut retained := #[]
    for arc in upper do
      if (← (← arc.getObjVal? "source").getStr?) != "client" then retained := retained.push arc
    let changed := selected.setObjVal! "upper" (.arr (retained.push direct))
    changedCases := changedCases.push (changed.setObjVal! "must" (.arr #[direct]))
  let initial ← bypassRevision (← left.getObjVal? "initial")
  let updates ← (← left.getObjVal? "updates").getArr?
  let mut changedUpdates := #[]
  for revision in updates do changedUpdates := changedUpdates.push (← bypassRevision revision)
  let left := left.setObjVal! "contract" (contract.setObjVal! "cases" (.arr changedCases))
  let left := (left.setObjVal! "initial" initial).setObjVal! "updates" (.arr changedUpdates)
  Json.fromJson (json.setObjVal! "left" left)

end NetlibTest.FederatedDeploymentInputs
