import Netlib.Check.FederatedPacketContext
import Netlib.Check.FederatedPacketJson
import Netlib.Check.FederatedPacketPartition
import NetlibTest.FederatedNativeFixture

namespace NetlibTest.FederatedPacketFixture

open Netlib Federation InFlight

def file : String := "examples/federation/packet-updates.json"

private def loadValue : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def raw : IO Lean.Json := do loadValue (Import.Json.parse (← IO.FS.readFile file))

def profileFromJson : Lean.Json → Except String Profile := InFlight.Json.profile

structure Base where
  input : Input
  profile : Profile
  header : Packet.Header
  actions : List Action
  serviceBound : Nat

def fromJson (json : Lean.Json) : Except String Base := do
  let bundle ← InFlight.Json.fromJson json
  return ⟨bundle.deployment, bundle.profile, bundle.header, bundle.actions, bundle.serviceBound⟩

def load : IO Base := do loadValue (fromJson (← raw))

structure Fixture where
  base : Base
  left : FederatedNativeFixture.Versions base.input.left
  right : FederatedNativeFixture.Versions base.input.right
  deployment : Deployment.Checked base.input
  context : Context base.input
  valid : Context.Validated deployment context
  profileEq : context.profile = base.profile

theorem Fixture.coverage (fixture : Fixture) (header : Packet.Header)
    (accepted : fixture.context.first.selector.accepts header = true) :
    (JointPartition.partition fixture.base.input fixture.context.first).representative header ∈
      JointPartition.selectedHeaders fixture.base.input fixture.context.first :=
  JointPartition.selected_representative_mem _ _ header accepted

private def checkLocal (plan : Plan) (checked : FederatedNativeFixture.Versions plan) : IO Unit := do
  ensure (checked.values.length == 3) "The packet fixture must check all three local revisions."
  for ⟨revision, native⟩ in checked.values do
    ensure (native.results.length == 1 && !native.results.isEmpty)
      "Every native revision must retain its complete application case."
    let expected := if revision.id.endsWith "r0" then 1 else 2
    for selected in native.results do
      ensure (selected.2.cells.length == expected)
        "Native partitions should have one initial selected cell and two after the local split."

def build : IO Fixture := do
  let base ← load
  let limits : Native.Limits := ⟨base.input.cells, base.input.work⟩
  let left ← loadValue (FederatedNativeFixture.checkVersions base.input.left limits)
  let right ← loadValue (FederatedNativeFixture.checkVersions base.input.right limits)
  checkLocal base.input.left left
  checkLocal base.input.right right
  let deployment ← loadValue (Deployment.certify base.input)
  let selection ← loadValue (Context.select deployment base.profile)
  let context := selection.context
  let headers := JointPartition.selectedHeaders base.input context.first
  let ports := (JointPartition.sourcePortPoints base.input context.first).map Fin.val
  ensure (JointPartition.selectedCount base.input context.first == 3 && headers.length == 3 &&
      JointPartition.fullCount base.input context.first == 324 &&
      ports.length == 3 && ports.contains 4096 && ports.contains 50001 && ports.contains 53001)
    "The joint partition must combine both operators' distinct native source-port boundaries."
  ensure (base.actions.length == 19 && base.serviceBound == 12 &&
      base.profile.work == 1000000000 && base.input.work == 1000000000)
    "The packet replay must retain its actual actions, service bound, and original work limits."
  ensure (base.input.left.initial.snapshot.intent.ids.contains "old-relay" &&
      !base.input.left.initial.snapshot.intent.ids.contains "new-relay" &&
      base.input.right.initial.snapshot.intent.ids.contains "old-relay")
    "Both operators must initially use overlapping private old-relay names."
  for plan in [base.input.left, base.input.right] do
    let some drain := plan.updates[0]? | throw (IO.userError "The drain revision is absent.")
    let some retired := plan.updates[1]? | throw (IO.userError "The retirement revision is absent.")
    let some selected := plan.contract.cases.head? | throw (IO.userError "The application case is absent.")
    ensure (drain.snapshot.intent.ids.contains "old-relay" && drain.snapshot.intent.ids.contains "new-relay" &&
        !retired.snapshot.intent.ids.contains "old-relay" && retired.snapshot.intent.ids.contains "new-relay" &&
        plan.initial.anchor "inside" == "old-relay" && drain.anchor "inside" == "new-relay")
      "The internal anchor must move while the old relay remains available for drain before retirement."
    ensure (plan.initial.snapshot.nativeEdge base.header selected.request "gateway" "old-relay" &&
        drain.snapshot.nativeEdge base.header selected.request "gateway" "new-relay" &&
        !drain.snapshot.nativeEdge base.header selected.request "gateway" "old-relay" &&
        drain.snapshot.nativeEdge base.header selected.request "old-relay" "egress" &&
        !retired.snapshot.nativeEdge base.header selected.request "old-relay" "egress")
      "The native route must reroute new sends, retain the old drain, then remove that old sender."
  match accepted : context.first.selector.accepts base.header with
  | false => throw (IO.userError "The concrete packet lies outside the checked traffic class.")
  | true =>
    let _ := JointPartition.selected_representative_mem base.input context.first base.header accepted
    pure ()
  return ⟨base, left, right, deployment, context, selection.validated, selection.profileEq⟩

private def changeFirstLeft (json : Lean.Json) (change : Lean.Json → Except String Lean.Json) :
    Except String Lean.Json := do
  let deployment ← json.getObjVal? "deployment"
  let left ← deployment.getObjVal? "left"
  let updates ← (← left.getObjVal? "updates").getArr?
  let some first := updates[0]? | throw "The first campus update is absent."
  let changed ← change first
  return json.setObjVal! "deployment" (deployment.setObjVal! "left"
    (left.setObjVal! "updates" (.arr (updates.set! 0 changed))))

private def changeRouter (revision : Lean.Json) (name : String)
    (change : Lean.Json → Except String Lean.Json) : Except String Lean.Json := do
  let snapshot ← revision.getObjVal? "snapshot"
  let routers ← (← snapshot.getObjVal? "routers").getArr?
  let mut found := false
  let mut changed := #[]
  for router in routers do
    if (← (← router.getObjVal? "node").getStr?) == name then
      changed := changed.push (← change router)
      found := true
    else changed := changed.push router
  if !found then throw s!"Native router {name} is absent."
  return revision.setObjVal! "snapshot" (snapshot.setObjVal! "routers" (.arr changed))

private def withoutName (values : Lean.Json) (field name : String) : Except String Lean.Json := do
  let mut changed := #[]
  for value in ← values.getArr? do
    if (← (← value.getObjVal? field).getStr?) != name then changed := changed.push value
  return .arr changed

private def removeOld (revision : Lean.Json) : Except String Lean.Json := do
  let snapshot ← revision.getObjVal? "snapshot"
  let intent ← snapshot.getObjVal? "intent"
  let devices ← withoutName (← intent.getObjVal? "devices") "id" "old-relay"
  let routers ← withoutName (← snapshot.getObjVal? "routers") "node" "old-relay"
  let projection ← withoutName (← revision.getObjVal? "projection") "localNode" "old-relay"
  let snapshot := (snapshot.setObjVal! "intent" (intent.setObjVal! "devices" devices)).setObjVal! "routers" routers
  return (revision.setObjVal! "snapshot" snapshot).setObjVal! "projection" projection

private def fence (json : Lean.Json) (index : Nat) (names : List String) : Except String Lean.Json := do
  let profile ← json.getObjVal? "profile"
  let fences ← profile.getObjVal? "fences"
  let rows ← (← fences.getObjVal? "left").getArr?
  if index ≥ rows.size then throw "The requested campus fence row is absent."
  return json.setObjVal! "profile" (profile.setObjVal! "fences"
    (fences.setObjVal! "left" (.arr (rows.set! index (Lean.toJson names)))))

/-- Static snapshots pass; the recorded update must wait for its pending receiver. -/
def removedReceiver (json : Lean.Json) : Except String Lean.Json := do
  fence (← fence (← changeFirstLeft json removeOld) 0 ["old-relay"]) 1 []

private def reprojectOld (revision : Lean.Json) : Except String Lean.Json := do
  let revision ← changeRouter revision "old-relay" fun router =>
    return (router.setObjVal! "bindings" (.arr #[])).setObjVal! "routes" (.arr #[])
  let rows ← (← revision.getObjVal? "projection").getArr?
  let mut changed := #[]
  for row in rows do
    changed := changed.push (if (← (← row.getObjVal? "localNode").getStr?) == "old-relay"
      then row.setObjVal! "publicNode" (.str "management") else row)
  return revision.setObjVal! "projection" (.arr changed)

def projectionJump (json : Lean.Json) : Except String Lean.Json := do
  fence (← changeFirstLeft json reprojectOld) 0 ["old-relay"]

private def denyOldPort (revision : Lean.Json) : Except String Lean.Json :=
  changeRouter revision "old-relay" fun router => do
    let ruleset ← router.getObjVal? "nftables"
    let entries ← (← ruleset.getObjVal? "nftables").getArr?
    let some permit := entries[3]? | throw "The old relay's application rule is absent."
    let rule ← permit.getObjVal? "rule"
    let condition := Lean.Json.mkObj [("match", Lean.Json.mkObj [
      ("op", .str "=="), ("left", Lean.Json.mkObj [("payload", Lean.Json.mkObj [
        ("protocol", .str "tcp"), ("field", .str "sport")])]), ("right", Lean.toJson (52000 : Nat))])]
    let denied := (rule.setObjVal! "handle" (Lean.toJson (99 : Nat))).setObjVal! "expr"
      (.arr #[condition, Lean.Json.mkObj [("drop", .null)]])
    let entries := entries.extract 0 3 ++ #[Lean.Json.mkObj [("rule", denied)]] ++ entries.extract 3 entries.size
    return router.setObjVal! "nftables" (ruleset.setObjVal! "nftables" (.arr entries))

def strandedHeader (json : Lean.Json) : Except String Lean.Json := changeFirstLeft json denyOldPort

private def routedTo (router : Lean.Json) (target : String) : Lean.Json :=
  (router.setObjVal! "bindings" (.arr #[Lean.Json.mkObj [
    ("device", .str "service0"), ("nextNode", .str target), ("gateway", .null)]])).setObjVal! "routes"
    (.arr #[Lean.Json.mkObj [("dst", .str "198.51.100.0/24"), ("dev", .str "service0"),
      ("protocol", .str "static"), ("scope", .str "link"), ("flags", .arr #[])]])

private def cycleOld (revision : Lean.Json) : Except String Lean.Json := do
  let revision ← changeRouter revision "old-relay" fun router => return routedTo router "drain-loop"
  let snapshot ← revision.getObjVal? "snapshot"
  let intent ← snapshot.getObjVal? "intent"
  let devices ← (← intent.getObjVal? "devices").getArr?
  let routers ← (← snapshot.getObjVal? "routers").getArr?
  let mut old := none
  for router in routers do
    if (← (← router.getObjVal? "node").getStr?) == "old-relay" then old := some router
  let some oldRouter := old | throw "The draining old relay is absent."
  let loop := (routedTo oldRouter "old-relay").setObjVal! "node" (.str "drain-loop")
  let device := Lean.Json.mkObj [("id", .str "drain-loop"), ("zone", .str "private"), ("role", .str "router")]
  let projection ← (← revision.getObjVal? "projection").getArr?
  let row := Lean.Json.mkObj [("localNode", .str "drain-loop"), ("publicNode", .str "inside")]
  let snapshot := snapshot.setObjVal! "intent" (intent.setObjVal! "devices" (.arr (devices.push device)))
  let snapshot := snapshot.setObjVal! "routers" (.arr (routers.push loop))
  return (revision.setObjVal! "snapshot" snapshot).setObjVal! "projection" (.arr (projection.push row))

def drainingCycle (json : Lean.Json) : Except String Lean.Json := do
  fence (← changeFirstLeft json cycleOld) 1 ["old-relay", "drain-loop"]

private def verifyNegative (json : Lean.Json) : IO Unit := do
  let base ← loadValue (fromJson json)
  let deployment ← loadValue (Deployment.certify base.input)
  let _ ← loadValue (Context.select deployment base.profile)
  pure ()

def run : IO Unit := do
  let _ ← build
  let json ← raw
  verifyNegative (← loadValue (removedReceiver json))
  verifyNegative (← loadValue (projectionJump json))
  let stranded ← loadValue (strandedHeader json)
  verifyNegative stranded
  let strandedBase ← loadValue (fromJson stranded)
  let deployment ← loadValue (Deployment.certify strandedBase.input)
  let selection ← loadValue (Context.select deployment strandedBase.profile)
  let context := selection.context
  let ports := (JointPartition.sourcePortPoints strandedBase.input context.first).map Fin.val
  ensure (JointPartition.selectedCount strandedBase.input context.first == 5 && ports.contains 52000 && ports.contains 52001)
    "The joint partition must include the otherwise unused old-relay deny interval."
  verifyNegative (← loadValue (drainingCycle json))
  IO.println "Packet fixtures: six native snapshots, three joint cells, and four static-valid dynamic negatives."

end NetlibTest.FederatedPacketFixture
