import Netlib.Check.DataPlane

namespace NetlibTest.DataPlane

open Netlib
open Netlib.DataPlane

private def ensure (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def reject (result : Except String α) (label : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"Expected an input error: {label}")

private def read (name : String) : IO Netlib.DataPlane.Config := do
  unwrap (Netlib.DataPlane.Config.parse (← IO.FS.readFile s!"examples/dataplane/{name}.json"))

private def hasStatus (report : Check.Report c) (id : String) (value : Bool) : Bool :=
  report.results.any (fun result => result.1.id == id && result.2.value == value)

private def fixtureTests : IO Unit := do
  let secure ← read "secure"
  let report ← unwrap (Check.check secure)
  ensure report.compliant "The secure packet and request model must pass."
  ensure (report.results.length == 4) "The report must keep every requirement."
  ensure (report.results.all (fun result => result.2.evidence.length == 1))
    "Each pair must have evidence."
  let bypass ← read "bypass"
  let report ← unwrap (Check.check bypass)
  ensure (!report.compliant) "A route around the gateway must fail."
  ensure (hasStatus report "AVAILABLE" true) "The bypass must still carry admitted traffic."
  ensure (hasStatus report "IDENTITY" false) "A denied request must survive on the bypass."
  ensure (hasStatus report "GATEWAY" false) "The direct route must violate mediation."
  for name in ["acl-deny", "route-drop", "disabled", "unauthorized"] do
    let config ← read name
    let report ← unwrap (Check.check config)
    ensure (!report.compliant) s!"The violating model must fail: {name}"
    ensure (hasStatus report "AVAILABLE" false) s!"The route must be blocked: {name}"

private def validationTests : IO Unit := do
  let text ← IO.FS.readFile "examples/dataplane/secure.json"
  for (label, invalid) in [
    ("schema", text.replace "\"schema\": 1" "\"schema\": 2"),
    ("unknown field", text.replace "\"schema\": 1," "\"schema\": 1, \"extra\": true,"),
    ("protocol bound", text.replace "\"protocol\": 6" "\"protocol\": 256"),
    ("address bound", text.replace "\"source\": 167772161" "\"source\": 4294967296"),
    ("port bound", text.replace "\"sourcePort\": 50000" "\"sourcePort\": 65536"),
    ("fractional port", text.replace "\"sourcePort\": 50000" "\"sourcePort\": 50000.5"),
    ("negative port", text.replace "\"destinationPort\": 443" "\"destinationPort\": -1"),
    ("prefix length", text.replace "\"length\": 0" "\"length\": 33"),
    ("reversed range", text.replace "\"first\": 443" "\"first\": 444"),
    ("missing match field", text.replace "\"sourcePorts\": null," ""),
    ("authentication type", text.replace "\"authenticated\": true" "\"authenticated\": \"true\""),
    ("unknown next hop", text.replace "\"nextHop\": \"gateway\"" "\"nextHop\": \"unknown\""),
    ("unknown request", text.replace "\"request\": \"alice-read\"" "\"request\": \"unknown\""),
    ("empty target", text.replace "\"target\": \"node:server\"" "\"target\": \"zone:missing\""),
    ("extra gateways", text.replace "\"gateways\": null" "\"gateways\": \"group:peps\"") ] do
    reject (Netlib.DataPlane.Config.parse invalid) label
  let config ← read "secure"
  reject ({ config with links := config.links ++ config.links }.validate) "Duplicate physical links."
  reject ({ config with routes := config.routes ++ config.routes }.validate) "Duplicate route tables."
  reject ({ config with permissions := config.permissions ++ config.permissions }.validate) "Duplicate permissions."
  reject ({ config with enforcement := .group "missing" }.validate) "An empty enforcement set."

private def query (kind : Kind) (source target : Selector) : Query :=
  ⟨"TEST", kind, source, target, "https", "alice-read", none⟩

private def edgeCaseTests : IO Unit := do
  let config ← read "secure"
  let querySelf := query .reach (.node "client") (.node "client")
  let self := { config with requirements := [querySelf] }
  let report ← unwrap (Check.check self)
  ensure report.compliant "A node must reach itself with zero steps."
  let selfIsolation := { self with requirements := [{ querySelf with kind := .isolate }] }
  let report ← unwrap (Check.check selfIsolation)
  ensure (!report.compliant) "Zero steps must refute self isolation."
  let endpoint := { config with requirements :=
    [⟨"ENDPOINT", .mediated, .node "gateway", .node "server", "https", "alice-read", some (.group "peps")⟩] }
  let report ← unwrap (Check.check endpoint)
  ensure report.compliant "A gateway endpoint must satisfy mediation."
  let outside := { config with requirements :=
    [⟨"ZERO", .mediated, .node "client", .node "client", "https", "bob-read", some (.group "peps")⟩] }
  let report ← unwrap (Check.check outside)
  ensure (!report.compliant) "Zero steps outside the gateway must be a bypass."
  let allDevices := { config with requirements := [query .reach (.role "client") (.zone "services")] }
  let report ← unwrap (Check.check allDevices)
  ensure report.compliant "Role and zone selectors must select their devices."
  let many := { config with
    devices := config.devices ++ [⟨"other-server", "services", "server"⟩]
    requirements := allDevices.requirements }
  let report ← unwrap (Check.check many)
  ensure (!report.compliant) "A universal query must include the disconnected second target."
  ensure (report.results.all (fun result => result.2.evidence.length == 2))
    "The universal report must preserve both pair certificates."
  let noRules := { config with links := config.links.map (fun link => { link with rules := [] }) }
  let report ← unwrap (Check.check noRules)
  ensure (hasStatus report "AVAILABLE" false) "Empty ACLs must deny by default."
  let noAdjacency := { config with links := [] }
  let report ← unwrap (Check.check noAdjacency)
  ensure (hasStatus report "AVAILABLE" false) "Route entries must not create physical links."
  let tieDrop : Routing.Entry String := ⟨⟨0, 0⟩, none⟩
  let tie := { config with routes := config.routes.map (fun table => if table.node == "client" then { table with entries := tieDrop :: table.entries } else table) }
  let report ← unwrap (Check.check tie)
  ensure (hasStatus report "AVAILABLE" false) "The first equal-length route must win."
  let denyIdentity := { config with principals := config.principals.map (fun p => { p with authenticated := false }) }
  let report ← unwrap (Check.check denyIdentity)
  ensure (hasStatus report "AVAILABLE" false) "Authentication denial must block the mediated route."
  let empty := { config with requirements := [] }
  reject (Check.check empty) "An empty requirement list."

def run : IO Unit := do
  fixtureTests
  validationTests
  edgeCaseTests
  IO.println "Data-plane tests passed."

end NetlibTest.DataPlane
