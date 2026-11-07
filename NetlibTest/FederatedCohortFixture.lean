import Netlib.Check.FederatedPacketCompletion
import Netlib.Check.FederatedCohortJson
import NetlibTest.FederatedPacketFixture

namespace NetlibTest.FederatedCohortFixture

open Netlib Federation InFlight

structure Specification where
  profile : Profile
  header : Packet.Header

structure Capacity where
  node : Node
  slots : Nat

structure Data where
  input : Input
  packets : List Specification
  capacities : List Capacity
  actions : List Action
  serviceBound : Nat

private def loadValue : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def Specification.observation (packet : Specification) (node : Node) : InFlight.Observation :=
  ⟨packet.profile.packetID, packet.header, node⟩

private def send (packet : Specification) (source target : Node) : Action :=
  .send (packet.observation source) target

private def arrive (packet : Specification) (target : Node) (index : Nat) : Action :=
  .arrive (packet.observation target) index

private def positiveActions (a b : Specification) : List Action := [
  send a (.inl "ingress") (.inl "gateway"),
  send b (.inl "ingress") (.inl "gateway"),
  arrive a (.inl "gateway") 0,
  arrive b (.inl "gateway") 1,
  send a (.inl "gateway") (.inl "old-relay"),
  .updateLeft 0,
  arrive a (.inl "old-relay") 4,
  send b (.inl "gateway") (.inl "new-relay"),
  arrive b (.inl "new-relay") 7,
  send b (.inl "new-relay") (.inl "egress"),
  arrive b (.inl "egress") 9,
  send b (.inl "egress") (.inr "ingress"),
  arrive b (.inr "ingress") 11,
  send b (.inr "ingress") (.inr "gateway"),
  arrive b (.inr "gateway") 13,
  send b (.inr "gateway") (.inr "old-relay"),
  .updateRight 0,
  arrive b (.inr "old-relay") 15,
  send b (.inr "old-relay") (.inr "egress"),
  .updateRight 1,
  arrive b (.inr "egress") 18,
  .receive (b.observation (.inr "egress")),
  send a (.inl "old-relay") (.inl "egress"),
  .updateLeft 1,
  arrive a (.inl "egress") 22,
  send a (.inl "egress") (.inr "ingress"),
  arrive a (.inr "ingress") 25,
  send a (.inr "ingress") (.inr "gateway"),
  arrive a (.inr "gateway") 27,
  send a (.inr "gateway") (.inr "new-relay"),
  arrive a (.inr "new-relay") 29,
  send a (.inr "new-relay") (.inr "egress"),
  arrive a (.inr "egress") 31,
  .receive (a.observation (.inr "egress"))]

private def capacities (input : Input) : List Capacity :=
  (Control.nodes input).map fun node =>
    ⟨node, if node = .inl "ingress" ∨ node = .inl "gateway" ∨ node = .inr "gateway" then 2 else 1⟩

private def positiveFrom (base : FederatedPacketFixture.Base) (secondHeader : Packet.Header) : Data :=
  let a : Specification := ⟨{ base.profile with packetID := "packet-a" }, base.header⟩
  let b : Specification := ⟨{ base.profile with packetID := "packet-b" }, secondHeader⟩
  ⟨base.input, [a, b], capacities base.input, positiveActions a b, base.serviceBound⟩

def positive : IO Data := do
  let base ← FederatedPacketFixture.load
  return positiveFrom base { base.header with sourcePort := 54000 }

def sameHeader : IO Data := do
  let base ← FederatedPacketFixture.load
  return positiveFrom base base.header

private partial def rename (json : Lean.Json) (old replacement : String) : Lean.Json :=
  match json with
  | .str value => .str (if value == old then replacement else value)
  | .arr values => .arr (values.map (rename · old replacement))
  | .obj values => Lean.Json.mkObj (values.toList.map fun (key, value) => (key, rename value old replacement))
  | other => other

private def routesFor (router : Lean.Json) (first second : String) : Lean.Json :=
  let binding := fun device target => Lean.Json.mkObj [
    ("device", .str device), ("nextNode", .str target), ("gateway", .null)]
  let route := fun destination device => Lean.Json.mkObj [
    ("dst", .str destination), ("dev", .str device), ("protocol", .str "static"),
    ("scope", .str "link"), ("flags", .arr #[])]
  let bindings := if first == second then #[binding "class-a" first]
    else #[binding "class-a" first, binding "class-b" second]
  let secondDevice := if first == second then "class-a" else "class-b"
  (router.setObjVal! "bindings" (.arr bindings)).setObjVal! "routes"
    (.arr #[route "198.51.100.0/24" "class-a", route "203.0.113.0/24" secondDevice])

private def bothDestinations (router : Lean.Json) : Except String Lean.Json := do
  let nftables ← router.getObjVal? "nftables"
  let entries ← (← nftables.getObjVal? "nftables").getArr?
  let some permitted := entries[3]? | throw "The native application permit is absent."
  let other := rename permitted "198.51.100.0" "203.0.113.0"
  let rule ← other.getObjVal? "rule"
  let other := other.setObjVal! "rule" (rule.setObjVal! "handle" (Lean.toJson (4 : Nat)))
  return router.setObjVal! "nftables" (nftables.setObjVal! "nftables" (.arr (entries.push other)))

private def casePair (contract : Lean.Json) : Except String Lean.Json := do
  let cases ← (← contract.getObjVal? "cases").getArr?
  let some first := cases[0]? | throw "The application case is absent."
  let selector ← first.getObjVal? "selector"
  let destination := Lean.Json.mkObj [("address", Lean.toJson (3405803776 : Nat)), ("length", Lean.toJson (24 : Nat))]
  let second := (first.setObjVal! "id" (.str "app-b")).setObjVal! "selector"
    (selector.setObjVal! "destination" destination)
  return contract.setObjVal! "cases" (.arr #[first, second])

private def leftDeadlockRevision (revision : Lean.Json) : Except String Lean.Json := do
  let revision := rename revision "old-relay" "x"
  let snapshot ← revision.getObjVal? "snapshot"
  let intent ← snapshot.getObjVal? "intent"
  let devices ← (← intent.getObjVal? "devices").getArr?
  let routers ← (← snapshot.getObjVal? "routers").getArr?
  let mut changed := #[]
  let mut extra := none
  for router in routers do
    match ← (← router.getObjVal? "node").getStr? with
    | "gateway" => changed := changed.push (← bothDestinations (routesFor router "x" "y"))
    | "x" =>
      let current ← bothDestinations (routesFor router "y" "egress")
      changed := changed.push current
      extra := some ((routesFor current "egress" "x").setObjVal! "node" (.str "y"))
    | _ => changed := changed.push router
  let some extraRouter := extra | throw "The x native router is absent."
  let device := Lean.Json.mkObj [("id", .str "y"), ("zone", .str "private"), ("role", .str "router")]
  let intent := intent.setObjVal! "devices" (.arr (devices.push device))
  let snapshot := (snapshot.setObjVal! "intent" intent).setObjVal! "routers" (.arr (changed.push extraRouter))
  let projection ← (← revision.getObjVal? "projection").getArr?
  let row := Lean.Json.mkObj [("localNode", .str "y"), ("publicNode", .str "inside")]
  return (revision.setObjVal! "snapshot" snapshot).setObjVal! "projection" (.arr (projection.push row))

private def rightDeadlockRevision (revision : Lean.Json) : Except String Lean.Json := do
  let snapshot ← revision.getObjVal? "snapshot"
  let routers ← (← snapshot.getObjVal? "routers").getArr?
  let mut changed := #[]
  for router in routers do
    match ← (← router.getObjVal? "node").getStr? with
    | "gateway" => changed := changed.push (← bothDestinations (routesFor router "old-relay" "old-relay"))
    | "old-relay" => changed := changed.push (← bothDestinations (routesFor router "egress" "egress"))
    | _ => changed := changed.push router
  return revision.setObjVal! "snapshot" (snapshot.setObjVal! "routers" (.arr changed))

def deadlockDeployment (json : Lean.Json) : Except String Lean.Json := do
  let deployment ← json.getObjVal? "deployment"
  let mut changed := deployment
  for side in ["left", "right"] do
    let plan ← deployment.getObjVal? side
    let contract ← casePair (← plan.getObjVal? "contract")
    let initial ← if side == "left" then leftDeadlockRevision (← plan.getObjVal? "initial")
      else rightDeadlockRevision (← plan.getObjVal? "initial")
    let plan := (plan.setObjVal! "contract" contract).setObjVal! "initial" initial
    changed := changed.setObjVal! side (plan.setObjVal! "updates" (.arr #[]))
  let intent ← deployment.getObjVal? "intent"
  let queries ← (← intent.getObjVal? "queries").getArr?
  let mut otherQueries := #[]
  for query in queries do
    let id ← (← query.getObjVal? "id").getStr?
    otherQueries := otherQueries.push ((query.setObjVal! "id" (.str (id ++ "_B"))).setObjVal! "case" (.str "app-b"))
  let borders ← (← intent.getObjVal? "borders").getArr?
  let mut otherBorders := #[]
  for border in borders do
    let cases ← (← border.getObjVal? "cases").getArr?
    otherBorders := otherBorders.push (border.setObjVal! "cases" (.arr (cases.push (.str "app-b"))))
  let intent := (intent.setObjVal! "queries" (.arr (queries ++ otherQueries))).setObjVal! "borders" (.arr otherBorders)
  return changed.setObjVal! "intent" intent

def deadlockInput (json : Lean.Json) : Except String Input := do
  Federation.Json.fromJson (← deadlockDeployment json)

private def deadlockFrom (input : Input) (base : FederatedPacketFixture.Base) (destination : Packet.Address) : Data :=
  let profile := { base.profile with leftFences := [], rightFences := [] }
  let a : Specification := ⟨{ profile with packetID := "packet-a" }, base.header⟩
  let b : Specification := ⟨{ profile with packetID := "packet-b", queryID := "APP_B" },
    { base.header with destination, sourcePort := 54000 }⟩
  ⟨input, [a, b], capacities input, [
    send a (.inl "ingress") (.inl "gateway"), arrive a (.inl "gateway") 0,
    send b (.inl "ingress") (.inl "gateway"), arrive b (.inl "gateway") 2,
    send a (.inl "gateway") (.inl "x"), arrive a (.inl "x") 4,
    send b (.inl "gateway") (.inl "y"), arrive b (.inl "y") 6], base.serviceBound⟩

def deadlock : IO Data := do
  let json ← FederatedPacketFixture.raw
  let input ← loadValue (deadlockInput json)
  let base ← FederatedPacketFixture.load
  return deadlockFrom input base 3405803786

def hiddenTupleDeployment (json : Lean.Json) : Except String Lean.Json := do
  let deployment ← deadlockDeployment json
  let mut changed := rename (rename deployment "203.0.113.0" "198.51.101.0")
    "203.0.113.0/24" "198.51.101.0/24"
  for side in ["left", "right"] do
    let plan ← changed.getObjVal? side
    let contract ← plan.getObjVal? "contract"
    let cases ← (← contract.getObjVal? "cases").getArr?
    let mut broad := #[]
    for selected in cases do
      let selector ← selected.getObjVal? "selector"
      let destination := Lean.Json.mkObj [("address", Lean.toJson (3325256704 : Nat)), ("length", Lean.toJson (23 : Nat))]
      broad := broad.push (selected.setObjVal! "selector" (selector.setObjVal! "destination" destination))
    changed := changed.setObjVal! side (plan.setObjVal! "contract" (contract.setObjVal! "cases" (.arr broad)))
  return changed

def hiddenTuple : IO Data := do
  let input ← loadValue (Federation.Json.fromJson (← loadValue (hiddenTupleDeployment (← FederatedPacketFixture.raw))))
  return deadlockFrom input (← FederatedPacketFixture.load) 3325256970

private def chainActions (packet : Specification) : List Node → Nat → List Action
  | source :: target :: rest, index =>
    [send packet source target, arrive packet target index] ++ chainActions packet (target :: rest) (index + 2)
  | [target], _ => [.receive (packet.observation target)]
  | [], _ => []

def hiddenDiagonal (second : Bool) : IO Data := do
  let data ← hiddenTuple
  let [a, b] := data.packets | throw (IO.userError "The mixed-header fixture must contain both packet identities.")
  let destination : Packet.Address := if second then 3325256970 else 3325256714
  let a := { a with header := { a.header with destination } }
  let b := { b with header := { b.header with destination } }
  let inside := if second then [.inl "y", .inl "x"] else [.inl "x", .inl "y"]
  let path := [.inl "ingress", .inl "gateway"] ++ inside ++
    [.inl "egress", .inr "ingress", .inr "gateway", .inr "old-relay", .inr "egress"]
  let first := chainActions a path 0
  return { data with packets := [a, b], actions := first ++ chainActions b path first.length }

def Data.profile (data : Data) (limits : Cohort.Limits) : Cohort.Profile :=
  ⟨data.packets.map (·.profile), data.capacities.map (fun row => ⟨row.node, row.slots⟩), limits⟩

def Data.toJson (data : Data) (deployment : Lean.Json) (limits : Cohort.Limits) : Lean.Json :=
  Lean.Json.mkObj [
    ("schema", Lean.toJson (1 : Nat)), ("scope", .str "two-domain-packet-cohorts"),
    ("deployment", deployment), ("profile", Cohort.Json.profileJson (data.profile limits)),
    ("headers", .arr (data.packets.map (fun packet => Import.PacketFields.headerJson packet.header)).toArray),
    ("actions", .arr (data.actions.map InFlight.Json.actionJson).toArray),
    ("serviceBound", Lean.toJson data.serviceBound)]

def positiveJson (limits : Cohort.Limits) : IO Lean.Json := do
  let data ← positive
  return data.toJson (← loadValue ((← FederatedPacketFixture.raw).getObjVal? "deployment")) limits

def sameHeaderJson (limits : Cohort.Limits) : IO Lean.Json := do
  return (← sameHeader).toJson (← loadValue ((← FederatedPacketFixture.raw).getObjVal? "deployment")) limits

def emptyJson (limits : Cohort.Limits) : IO Lean.Json := do
  let data ← positive
  let data := { data with packets := [], actions := [.updateBoth 0 0, .updateBoth 1 1] }
  return data.toJson (← loadValue ((← FederatedPacketFixture.raw).getObjVal? "deployment")) limits

def deadlockJson (limits : Cohort.Limits) : IO Lean.Json := do
  return (← deadlock).toJson (← loadValue (deadlockDeployment (← FederatedPacketFixture.raw))) limits

def hiddenTupleJson (limits : Cohort.Limits) : IO Lean.Json := do
  return (← hiddenTuple).toJson (← loadValue (hiddenTupleDeployment (← FederatedPacketFixture.raw))) limits

def hiddenDiagonalJson (second : Bool) (limits : Cohort.Limits) : IO Lean.Json := do
  return (← hiddenDiagonal second).toJson (← loadValue (hiddenTupleDeployment (← FederatedPacketFixture.raw))) limits

def zeroHopDeployment (json : Lean.Json) : Except String Lean.Json := do
  let deployment ← json.getObjVal? "deployment"
  let mut changed := deployment
  for side in ["left", "right"] do
    let plan ← deployment.getObjVal? side
    let contract ← plan.getObjVal? "contract"
    let cases ← (← contract.getObjVal? "cases").getArr?
    let some selected := cases[0]? | throw "The singleton packet case is absent."
    let selector := Lean.Json.mkObj [
      ("source", Lean.Json.mkObj [("address", Lean.toJson (3221225994 : Nat)), ("length", Lean.toJson (32 : Nat))]),
      ("destination", Lean.Json.mkObj [("address", Lean.toJson (3325256714 : Nat)), ("length", Lean.toJson (32 : Nat))]),
      ("protocol", Lean.toJson (17 : Nat)),
      ("sourcePorts", Lean.Json.mkObj [("first", Lean.toJson (52000 : Nat)), ("last", Lean.toJson (52000 : Nat))]),
      ("destinationPorts", Lean.Json.mkObj [("first", Lean.toJson (443 : Nat)), ("last", Lean.toJson (443 : Nat))])]
    let selected := ((selected.setObjVal! "selector" selector).setObjVal! "upper" (.arr #[])).setObjVal! "must" (.arr #[])
    let initial ← plan.getObjVal? "initial"
    let snapshot ← initial.getObjVal? "snapshot"
    let routers ← (← snapshot.getObjVal? "routers").getArr?
    let mut terminals := #[]
    for router in routers do
      let nftables ← router.getObjVal? "nftables"
      let entries ← (← nftables.getObjVal? "nftables").getArr?
      let router := (router.setObjVal! "bindings" (.arr #[])).setObjVal! "routes" (.arr #[])
      let router := router.setObjVal! "nftables" (nftables.setObjVal! "nftables" (.arr (entries.extract 0 3)))
      terminals := terminals.push router
    let initial := initial.setObjVal! "snapshot" (snapshot.setObjVal! "routers" (.arr terminals))
    let plan := plan.setObjVal! "contract" (contract.setObjVal! "cases" (.arr #[selected]))
    let plan := (plan.setObjVal! "initial" initial).setObjVal! "updates" (.arr #[])
    changed := changed.setObjVal! side plan
  let source := Lean.Json.mkObj [("side", .str "left"), ("node", .str "client")]
  let query := Lean.Json.mkObj [("id", .str "SELF"), ("kind", .str "reach"), ("case", .str "app"),
    ("source", source), ("target", source), ("gateways", .arr #[])]
  return changed.setObjVal! "intent" (Lean.Json.mkObj [("borders", .arr #[]), ("queries", .arr #[query])])

def zeroHop (count : Nat) : IO Data := do
  let input ← loadValue (Federation.Json.fromJson (← loadValue (zeroHopDeployment (← FederatedPacketFixture.raw))))
  let base ← FederatedPacketFixture.load
  let profile := { base.profile with queryID := "SELF", leftFences := [], rightFences := [] }
  let header := { base.header with protocol := Packet.Protocol.udp }
  let packets := (List.range count).map fun index =>
    (⟨{ profile with packetID := s!"packet-{index}" }, header⟩ : Specification)
  let capacities := (Control.nodes input).map fun node =>
    (⟨node, if node = .inl "ingress" then count else 1⟩ : Capacity)
  return ⟨input, packets, capacities,
    packets.map (fun packet => .receive (packet.observation (.inl "ingress"))), base.serviceBound⟩

def zeroHopJson (count : Nat) (limits : Cohort.Limits) : IO Lean.Json := do
  return (← zeroHop count).toJson (← loadValue (zeroHopDeployment (← FederatedPacketFixture.raw))) limits

private def mapRouters (revision : Lean.Json) (change : String → Lean.Json → Except String Lean.Json) :
    Except String Lean.Json := do
  let snapshot ← revision.getObjVal? "snapshot"
  let routers ← (← snapshot.getObjVal? "routers").getArr?
  let changed ← routers.toList.mapM fun router => do change (← (← router.getObjVal? "node").getStr?) router
  return revision.setObjVal! "snapshot" (snapshot.setObjVal! "routers" (.arr changed.toArray))

private def without (rows : Lean.Json) (field name : String) : Except String Lean.Json := do
  let mut changed := #[]
  for row in ← rows.getArr? do
    if (← (← row.getObjVal? field).getStr?) != name then changed := changed.push row
  return .arr changed

private def denyFirstDestination (router : Lean.Json) : Except String Lean.Json := do
  let nftables ← router.getObjVal? "nftables"
  let entries ← (← nftables.getObjVal? "nftables").getArr?
  let some permitted := entries[3]? | throw "The native first-case rule is absent."
  let rule ← permitted.getObjVal? "rule"
  let test := Lean.Json.mkObj [("match", Lean.Json.mkObj [
    ("op", .str "=="), ("left", Lean.Json.mkObj [("payload", Lean.Json.mkObj [
      ("protocol", .str "ip"), ("field", .str "daddr")])]),
    ("right", Lean.Json.mkObj [("prefix", Lean.Json.mkObj [("addr", .str "198.51.100.0"), ("len", Lean.toJson (24 : Nat))])])])]
  let denied := (rule.setObjVal! "handle" (Lean.toJson (99 : Nat))).setObjVal! "expr"
    (.arr #[test, Lean.Json.mkObj [("drop", .null)]])
  let entries := entries.extract 0 3 ++ #[Lean.Json.mkObj [("rule", denied)]] ++ entries.extract 3 entries.size
  return router.setObjVal! "nftables" (nftables.setObjVal! "nftables" (.arr entries))

def resourceDeployment (json : Lean.Json) : Except String Lean.Json := do
  let deployment ← deadlockDeployment json
  let left ← deployment.getObjVal? "left"
  let initial := rename (rename (← left.getObjVal? "initial") "x" "a") "y" "b"
  let initial ← mapRouters initial fun name router => return if name == "a" then routesFor router "egress" "egress" else router
  let snapshot ← initial.getObjVal? "snapshot"
  let routers ← (← snapshot.getObjVal? "routers").getArr?
  let mut old := none
  for router in routers do
    if (← (← router.getObjVal? "node").getStr?) == "a" then old := some router
  let some oldRouter := old | throw "The persistent a router is absent."
  let drain ← mapRouters initial fun name router =>
    if name == "gateway" then return routesFor router "new-relay" "b"
    else if name == "a" then denyFirstDestination router else return router
  let snapshot ← drain.getObjVal? "snapshot"
  let intent ← snapshot.getObjVal? "intent"
  let devices ← (← intent.getObjVal? "devices").getArr?
  let routers ← (← snapshot.getObjVal? "routers").getArr?
  let device := Lean.Json.mkObj [("id", .str "new-relay"), ("zone", .str "private"), ("role", .str "router")]
  let intent := intent.setObjVal! "devices" (.arr (devices.push device))
  let snapshot := (snapshot.setObjVal! "intent" intent).setObjVal! "routers"
    (.arr (routers.push (oldRouter.setObjVal! "node" (.str "new-relay"))))
  let projection ← (← drain.getObjVal? "projection").getArr?
  let anchors ← (← drain.getObjVal? "anchors").getArr?
  let mut changedAnchors := #[]
  for anchor in anchors do
    changedAnchors := changedAnchors.push (if (← (← anchor.getObjVal? "publicNode").getStr?) == "inside"
      then anchor.setObjVal! "localNode" (.str "new-relay") else anchor)
  let row := Lean.Json.mkObj [("localNode", .str "new-relay"), ("publicNode", .str "inside")]
  let drain := (drain.setObjVal! "snapshot" snapshot).setObjVal! "projection" (.arr (projection.push row))
  let drain := (drain.setObjVal! "anchors" (.arr changedAnchors)).setObjVal! "id" (.str "campus-resource-r1")
  let restored ← mapRouters drain fun name router =>
    if name == "gateway" then return routesFor router "new-relay" "a"
    else return if name == "a" then oldRouter else router
  let snapshot ← restored.getObjVal? "snapshot"
  let intent ← snapshot.getObjVal? "intent"
  let intent := intent.setObjVal! "devices" (← without (← intent.getObjVal? "devices") "id" "b")
  let snapshot := (snapshot.setObjVal! "intent" intent).setObjVal! "routers"
    (← without (← snapshot.getObjVal? "routers") "node" "b")
  let restored := ((restored.setObjVal! "snapshot" snapshot).setObjVal! "projection"
    (← without (← restored.getObjVal? "projection") "localNode" "b")).setObjVal! "id" (.str "campus-resource-r2")
  return deployment.setObjVal! "left" ((left.setObjVal! "initial" initial).setObjVal! "updates" (.arr #[drain, restored]))

def resourceDeadlock : IO Data := do
  let input ← loadValue (Federation.Json.fromJson (← loadValue (resourceDeployment (← FederatedPacketFixture.raw))))
  let base ← FederatedPacketFixture.load
  let profile := { base.profile with leftFences := [[], ["b"]], rightFences := [] }
  let a : Specification := ⟨{ profile with packetID := "packet-a" }, base.header⟩
  let b : Specification := ⟨{ profile with packetID := "packet-b", queryID := "APP_B" },
    { base.header with destination := 3405803786, sourcePort := 54000 }⟩
  return ⟨input, [a, b], capacities input, [
    send a (.inl "ingress") (.inl "gateway"), arrive a (.inl "gateway") 0,
    send b (.inl "ingress") (.inl "gateway"), arrive b (.inl "gateway") 2,
    send a (.inl "gateway") (.inl "a"), arrive a (.inl "a") 4,
    send b (.inl "gateway") (.inl "b"), arrive b (.inl "b") 6, .updateLeft 0], base.serviceBound⟩

def resourceDeadlockJson (limits : Cohort.Limits) : IO Lean.Json := do
  return (← resourceDeadlock).toJson (← loadValue (resourceDeployment (← FederatedPacketFixture.raw))) limits

structure Component (input : Input) (packet : Specification) where
  certificate : Certified input packet.profile
  accepted : certificate.context.first.selector.accepts packet.header = true

def checkComponents (input : Input) : (packets : List Specification) →
    Except String { values : List ((packet : Specification) × Component input packet) //
      values.map Sigma.fst = packets }
  | [] => return ⟨[], rfl⟩
  | packet :: rest => do
    let certificate ← certify input packet.profile
    if accepted : certificate.context.first.selector.accepts packet.header = true then
      let later ← checkComponents input rest
      return ⟨⟨packet, ⟨certificate, accepted⟩⟩ :: later.val, by simp only [List.map_cons, later.property]⟩
    else throw s!"Packet {packet.profile.packetID} is outside its checked class."

def projectActions (packetID : String) (actions : List Action) : List Action :=
  actions.map fun action => match action with
    | .send observed _ | .arrive observed _ | .receive observed =>
      if observed.packetID == packetID then action else .idle
    | other => other

def componentWork (values : List ((packet : Specification) × Component input packet)) : Nat :=
  (values.map (fun entry => entry.2.certificate.totalWork)).sum

def classCount (values : List ((packet : Specification) × Component input packet)) : Nat :=
  (values.map (fun entry => JointPartition.selectedCount input entry.2.certificate.context.first)).prod

private def verify (data : Data) (finishedExpected : Bool) : IO Unit := do
  let checked ← loadValue (checkComponents data.input data.packets)
  ensure (data.input.work == 1000000000 && data.packets.all (fun packet => packet.profile.work == 1000000000))
    "The inherited native and individual profile limits must remain unchanged."
  for ⟨packet, component⟩ in checked.val do
    let report ← loadValue (Replay.run component.certificate.context packet.header (projectActions packet.profile.packetID data.actions))
    ensure (report.steps.length == data.actions.length && finished report.final.key == finishedExpected)
      "Each literal component projection must retain global slots and the expected final phase."
    if !finishedExpected then
      let node := if packet.profile.queryID == "APP" then "x" else "y"
      let target := if node == "x" then "y" else "x"
      ensure (report.final.phase == .held (.inl node) &&
          (Control.step component.certificate.context packet.header report.final.key (.send (.inl target))).isSome)
        "Each standalone packet must remain enabled toward the receiver occupied by the other packet."
  IO.println s!"Cohort native fixture: packets={data.packets.length}, tuples={classCount checked.val}, componentWork={componentWork checked.val}, actions={data.actions.length}"

private def rejects (value : Except String α) (word : String) : IO Unit :=
  match value with
  | .error reason => ensure (reason.contains word) s!"Unexpected cohort parse rejection: {reason}"
  | .ok _ => throw (IO.userError "An invalid raw cohort unexpectedly parsed.")

private def verifyParser : IO Unit := do
  let limits : Cohort.Limits := ⟨0, 0, 0, 0⟩
  let json ← positiveJson limits
  let bundle ← loadValue (Cohort.Json.parse json.compress)
  ensure (bundle.profile.packets.length == 2 && bundle.headers.length == 2 && bundle.actions.length == 34 &&
      bundle.profile.limits.work == 0 && bundle.input.work == 1000000000)
    "Parsing must preserve all literal packet data and insufficient limits for the closed admission checks."
  rejects (Cohort.Json.parse ((json.setObjVal! "unknown" (.bool true)).compress)) "Unknown"
  rejects (Cohort.Json.parse ((json.setObjVal! "scope" (.str "unsupported-cohort")).compress)) "Unsupported"
  rejects (Cohort.Json.parse ("{\"schema\":1," ++ (json.compress.drop 1).toString)) "Duplicate"
  let object ← loadValue json.getObj?
  rejects (Cohort.Json.fromJson (Lean.Json.mkObj (object.toList.filter (fun entry => entry.1 != "headers")))) "headers"
  let profile ← loadValue (json.getObjVal? "profile")
  rejects (Cohort.Json.fromJson (json.setObjVal! "profile" (profile.setObjVal! "futureReady" (.bool true)))) "Unknown"
  let rows ← loadValue ((← loadValue (profile.getObjVal? "capacities")).getArr?)
  let some row := rows[0]? | throw (IO.userError "The first capacity row is absent.")
  let duplicate := json.setObjVal! "profile" (profile.setObjVal! "capacities" (.arr (rows.push row)))
  rejects (Cohort.Json.fromJson duplicate) "capacity"
  let deployment ← loadValue (json.getObjVal? "deployment")
  let left ← loadValue (deployment.getObjVal? "left")
  let initial ← loadValue (left.getObjVal? "initial")
  let snapshot ← loadValue (initial.getObjVal? "snapshot")
  let unsupported := json.setObjVal! "deployment" (deployment.setObjVal! "left" (left.setObjVal! "initial"
    (initial.setObjVal! "snapshot" (snapshot.setObjVal! "scope" (.str "unsupported-native-scope")))))
  rejects (Cohort.Json.fromJson unsupported) "scope"
  let mismatch ← loadValue (Cohort.Json.fromJson (json.setObjVal! "headers" (.arr #[])))
  ensure (mismatch.headers.isEmpty && mismatch.profile.packets.length == 2)
    "Header count belongs to closed cohort admission rather than a parser-side fixed-size assumption."
  let empty ← loadValue (Cohort.Json.fromJson (← emptyJson limits))
  ensure (empty.profile.packets.isEmpty && empty.headers.isEmpty && empty.actions.length == 2)
    "The raw empty cohort must retain the real shared update actions."
  let packets ← loadValue ((← loadValue (profile.getObjVal? "packets")).getArr?)
  let some packet := packets[0]? | throw (IO.userError "The first raw packet is absent.")
  let headers ← loadValue ((← loadValue (json.getObjVal? "headers")).getArr?)
  let some header := headers[0]? | throw (IO.userError "The first raw header is absent.")
  let three := (json.setObjVal! "profile" (profile.setObjVal! "packets"
    (.arr (packets.push (packet.setObjVal! "packetID" (.str "packet-c")))))).setObjVal! "headers" (.arr (headers.push header))
  let parsed ← loadValue (Cohort.Json.fromJson three)
  ensure (parsed.profile.packets.length == 3 && parsed.headers.length == 3)
    "The raw schema must not impose a two-packet limit."

def run : IO Unit := do
  let data ← positive
  verify data true
  let data ← sameHeader
  verify data true
  let data ← deadlock
  verify data false
  let data ← hiddenTuple
  verify data false
  verify (← hiddenDiagonal false) true
  verify (← hiddenDiagonal true) true
  verifyParser

end NetlibTest.FederatedCohortFixture
