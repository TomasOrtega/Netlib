import Netlib.Check.DomainContractNative
import Netlib.Model.FederatedJson

namespace NetlibTest.FederatedNativeFixture

open Netlib Federation

def file : String := "examples/federation/deployment.json"

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def loadValue : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

def raw : IO Lean.Json := do
  loadValue (Import.Json.parse (← IO.FS.readFile file))

def load : IO Input := do
  loadValue (Json.fromJson (← raw))

structure Versions (plan : Plan) where
  values : List ((revision : Revision) × Native.Checked plan.contract revision)
  covered : values.map Sigma.fst = plan.versions

private def checkList (contract : Contract) (limits : Native.Limits) : (versions : List Revision) →
    Except String { values : List ((revision : Revision) × Native.Checked contract revision) //
      values.map Sigma.fst = versions }
  | [] => return ⟨[], rfl⟩
  | revision :: rest => do
    let checked ← (Native.check contract revision limits).mapError (s!"Revision {revision.id}: " ++ ·)
    let later ← checkList contract limits rest
    return ⟨⟨revision, checked⟩ :: later.val, by simp only [List.map_cons, later.property]⟩

def checkVersions (plan : Plan) (limits : Native.Limits) : Except String (Versions plan) := do
  let checked ← checkList plan.contract limits plan.versions
  return ⟨checked.val, checked.property⟩

theorem Versions.each (value : Versions plan) (revision : Revision) (member : revision ∈ plan.versions) :
    Nonempty (Native.Checked plan.contract revision) := by
  rw [← value.covered] at member
  obtain ⟨⟨actual, checked⟩, present, same⟩ := List.mem_map.mp member
  cases same
  exact ⟨checked⟩

structure Fixture where
  input : Input
  left : Versions input.left
  right : Versions input.right

def packet : Packet.Header := ⟨3221225994, 3325256714, Packet.Protocol.tcp, 50000, 443⟩

private def verifyVersions (plan : Plan) (value : Versions plan) : IO Unit := do
  for ⟨revision, checked⟩ in value.values do
    ensure (revision.snapshot.intent.ids.contains "gateway" && checked.results.length == plan.contract.cases.length)
      "Each local certificate must retain the private gateway and exact case coverage."
    for stored : packed in checked.results do
      let selected := packed.1
      let cells := packed.2
      ensure (!cells.cells.isEmpty && selected.selector.accepts packet)
        "The selected native class must retain concrete cells and the arbitrary application header."
      have member : selected ∈ plan.contract.cases := by
        rw [← checked.covered]
        exact List.mem_map.mpr ⟨packed, stored, rfl⟩
      match accepted : selected.selector.accepts packet with
      | false => throw (IO.userError "The application test header is outside its native case.")
      | true =>
        let _ := checked.upper selected member packet accepted
        let _ := checked.lower selected member packet accepted
        for present : arc in selected.must do
          let _ := checked.provenance selected member packet accepted arc present
          pure ()

def build : IO Fixture := do
  let json ← raw
  let input ← loadValue (Json.fromJson json)
  let limits : Native.Limits := ⟨input.cells, input.work⟩
  let left ← loadValue (checkVersions input.left limits)
  let right ← loadValue (checkVersions input.right limits)
  ensure (input.left.versions.length == 3 && input.right.versions.length == 3 &&
      input.intent.queries.length == 4 && input.intent.borders.length == 1)
    "The native federation fixture must retain both three-revision plans and four public queries."
  let leftJson ← loadValue (json.getObjVal? "left")
  let updates ← loadValue ((← loadValue (leftJson.getObjVal? "updates")).getArr?)
  let some first := updates[0]? | throw (IO.userError "The first local update is absent.")
  let some second := updates[1]? | throw (IO.userError "The second local update is absent.")
  ensure ((← loadValue (first.getObjVal? "snapshot")).compress ==
      (← loadValue (second.getObjVal? "snapshot")).compress &&
      (← loadValue (first.getObjVal? "projection")).compress ==
        (← loadValue (second.getObjVal? "projection")).compress &&
      (← loadValue (first.getObjVal? "anchors")).compress ==
        (← loadValue (second.getObjVal? "anchors")).compress)
    "The last campus update must change only its local revision identity."
  let some initialGateway := input.left.initial.snapshot.router? "gateway"
    | throw (IO.userError "The initial native gateway is absent.")
  let some changed := input.left.updates[0]? | throw (IO.userError "The native path update is absent.")
  let some changedGateway := changed.snapshot.router? "gateway"
    | throw (IO.userError "The updated native gateway is absent.")
  ensure (initialGateway.bindings.any (·.nextNode == "egress") &&
      changedGateway.bindings.any (·.nextNode == "relay") &&
      !input.left.initial.snapshot.intent.ids.contains "relay" && changed.snapshot.intent.ids.contains "relay")
    "The private native path must change while the public contract remains fixed."
  verifyVersions input.left left
  verifyVersions input.right right
  return ⟨input, left, right⟩

def partialPortDenied (json : Lean.Json) : Except String Revision := do
  let left ← json.getObjVal? "left"
  let initial ← left.getObjVal? "initial"
  let snapshot ← initial.getObjVal? "snapshot"
  let routers ← (← snapshot.getObjVal? "routers").getArr?
  let some gateway := routers[1]? | throw "The native gateway JSON is absent."
  let ruleset ← gateway.getObjVal? "nftables"
  let rules ← (← ruleset.getObjVal? "nftables").getArr?
  let some permitted := rules[3]? | throw "The native application rule is absent."
  let rule ← permitted.getObjVal? "rule"
  let expression := Lean.Json.mkObj [("match", Lean.Json.mkObj [
    ("op", .str "=="), ("left", Lean.Json.mkObj [("payload", Lean.Json.mkObj [
      ("protocol", .str "tcp"), ("field", .str "sport")])]), ("right", Lean.toJson (50001 : Nat))])]
  let denied := (rule.setObjVal! "handle" (Lean.toJson (99 : Nat))).setObjVal! "expr"
    (.arr #[expression, Lean.Json.mkObj [("drop", .null)]])
  let entries := rules.extract 0 3 ++ #[Lean.Json.mkObj [("rule", denied)]] ++ rules.extract 3 rules.size
  let changed := gateway.setObjVal! "nftables" (ruleset.setObjVal! "nftables" (.arr entries))
  let snapshot := snapshot.setObjVal! "routers" (.arr (routers.set! 1 changed))
  Json.revision (initial.setObjVal! "snapshot" snapshot)

private def rejects (value : Except String α) (message : String) : IO Unit :=
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

def Fixture.verifyLocalRejections (fixture : Fixture) : IO Unit := do
  let input := fixture.input
  let contract := input.left.contract
  let initial := input.left.initial
  let limits : Native.Limits := ⟨input.cells, input.work⟩
  rejects (Native.check contract { initial with projection := initial.projection.tail } limits)
    "A native node without its exact projection must reject."
  let falseRole := { contract with nodes := contract.nodes.map fun node =>
    if node.id == "inside" then { node with role := .enforcement } else node }
  rejects (Native.check falseRole initial limits) "An invented native enforcement role must reject."
  let falseTerminal := { contract with nodes := contract.nodes.map fun node =>
    if node.id == "pep" then { node with role := .egress } else node }
  rejects (Native.check falseTerminal initial limits) "A forwarding gateway cannot be a terminal egress anchor."
  let wrongAnchor := { initial with anchors := initial.anchors.map fun row =>
    if row.publicNode == "client" then { row with localNode := "management" } else row }
  rejects (Native.check contract wrongAnchor limits) "A public anchor projecting to another node must reject."
  let unauthorized := { contract with cases := contract.cases.map fun selected =>
    { selected with request := ⟨"bob", "documents", "read"⟩ } }
  rejects (Native.check unauthorized initial limits) "A native request without identity permission cannot supply a must path."
  let missingEdge := { contract with cases := contract.cases.map fun selected =>
    { selected with upper := selected.upper.filter (fun arc => arc.source != "client") } }
  rejects (Native.check missingEdge initial limits) "An unadvertised real native edge must reject."
  rejects (Native.check contract initial { limits with cells := 0 }) "An exhausted cell budget must reject."
  rejects (Native.check contract initial { limits with work := 0 }) "An exhausted native work budget must reject."
  let rejectedRevision ← loadValue (partialPortDenied (← raw))
  match Native.check contract rejectedRevision limits with
  | .ok _ => throw (IO.userError "A native deny within one selected source-port interval must reject.")
  | .error reason =>
    ensure (reason.contains "50001" && reason.contains "packet")
      "The class rejection must identify the actual representative header blocked at source port 50001."

def run : IO Unit := do
  let fixture ← build
  fixture.verifyLocalRejections
  IO.println "Native federation: six checked revisions, overlapping private names, concrete paths, and local negatives."

end NetlibTest.FederatedNativeFixture
