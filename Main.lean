import Netlib.Check.Render
import Netlib.Policy.Analysis
import Netlib.Check.VerifiedCompliance
import Netlib.Check.DataPlane
import Netlib.Check.Traffic
import Netlib.Import.LinuxDeployment
import Netlib.Compile.Policy
import Netlib.Compile.Nftables
import Netlib.Import.TransferConfig
import Netlib.Check.NATTrace
import Netlib.Standards.ThreeGPP.ServiceAccess
import Netlib.Standards.IEEE80211.Deployment

open Netlib

private def usage : String := "Netlib: checked network requirements\n\n\
  netlib check CONFIG.json REQUIREMENTS.netlib [--json]\n\
  netlib analyze REQUIREMENTS.netlib [GOALS.netlib] [--budget N]\n\
  netlib formalize REQUIREMENTS.netlib\n\
  netlib dataplane CONFIG.json [--json]\n\
  netlib traffic CONFIG.json QUERY MATCH.json [--budget N] [--json]\n\
  netlib linux BUNDLE.json [--json]\n\
  netlib linux-traffic BUNDLE.json QUERY MATCH.json [--budget N] [--json]\n\
  netlib compile-acl INTENT.json [--budget N]\n\
  netlib transfer CONFIG.json [--budget N] [--json]\n\
  netlib nat-trace TRACE.json [--budget N] [--json]\n\
  netlib fiveg TRACE.json [--json]\n\
  netlib fiveg-coverage [--json]\n\
  netlib wifi AP.conf [DEPLOYMENT.json] [--json]\n\
  netlib wifi-coverage [--json]\n\
  netlib demo\n\n\
Exit codes: 0 = compliant / sufficient consistent policy; 1 = violation / policy gaps; 2 = input, resource, or internal error."

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def readRequirements (path : String) : IO (List Requirement) := do
  unwrap (Language.parse (← IO.FS.readFile path))

private def check (configPath policyPath : String) (json : Bool) : IO UInt32 := do
  let config ← unwrap (Config.parse (← IO.FS.readFile configPath))
  let requirements ← readRequirements policyPath
  let report ← unwrap (VerifiedCompliance.check config requirements)
  IO.println (if json then (Render.reportJson report).pretty else Render.report report)
  return if report.compliant then 0 else 1

private def dataPlane (path : String) (json : Bool) : IO UInt32 := do
  let config ← unwrap (DataPlane.Config.parse (← IO.FS.readFile path))
  let report ← unwrap (DataPlane.Check.check config)
  IO.println (if json then (DataPlane.Check.renderJson report).pretty else DataPlane.Check.render report)
  return if report.compliant then 0 else 1

private def standardsReport (report : Standards.Report) (json : Bool) : IO UInt32 := do
  IO.println (if json then report.renderJson.pretty else report.render)
  return if report.compliant then 0 else 1

private def traffic (path queryId selectionPath : String) (budget : Nat) (json : Bool) : IO UInt32 := do
  let config ← unwrap (DataPlane.Config.parse (← IO.FS.readFile path))
  let query ← match config.requirements.find? (·.id == queryId) with
    | none => throw (IO.userError s!"Unknown traffic query: {queryId}.")
    | some query => pure query
  let selection ← unwrap (DataPlane.Config.parseTrafficSelection (← IO.FS.readFile selectionPath))
  let checked ← unwrap (DataPlane.Check.checkTraffic config query selection budget)
  if json then
    IO.println (Lean.Json.mkObj [
      ("compliant", Lean.toJson checked.value), ("requirement", Lean.toJson query.id),
      ("scope", Lean.toJson "all-selected-packets"),
      ("partitionCells", Lean.toJson (config.trafficPartition selection).cellCount),
      ("evidence", Lean.toJson checked.evidence)]).pretty
  else
    IO.println (if checked.value then "COMPLIANT" else "NONCOMPLIANT")
    IO.println s!"Requirement {query.id}: all selected packets and endpoint pairs."
    for line in checked.evidence do IO.println line
  return if checked.value then 0 else 1

private def linuxAssumptions : List String := [
  "Headers describe valid unfragmented IPv4 transit packets after main-table selection.",
  "Interface and gateway bindings describe the intended physical adjacency.",
  "No additional hooks or packet transformations alter the modeled decisions.",
  "Declared identity facts and request enforcement describe the actual external controls.",
  "Snapshots describe the same stable deployment state."]

private def linuxEnvelope (snapshot : Import.LinuxDeployment.Snapshot) (report : Lean.Json) : Lean.Json :=
  Lean.Json.mkObj [
    ("scope", Lean.toJson "main-table-ipv4-transit"),
    ("assumptions", Lean.toJson linuxAssumptions),
    ("routers", Lean.toJson (snapshot.routers.map fun router => Lean.Json.mkObj [
      ("node", Lean.toJson router.node), ("source", Lean.toJson router.sourceID),
      ("routeVersion", Lean.toJson router.routeVersion),
      ("routes", Lean.toJson (router.routes.routes.map fun route => Lean.Json.mkObj [
        ("source", Lean.toJson s!"{router.sourceID}/routes{route.location}"), ("record", route.original)])),
      ("firewallVersion", Lean.toJson router.nftables.version),
      ("firewallPolicySource", Lean.toJson
        s!"{router.sourceID}/nftables/nftables/{router.nftables.chainIndex}/chain/policy"),
      ("firewallRules", Lean.toJson (router.nftables.rules.map fun rule => Lean.Json.mkObj [
        ("source", Lean.toJson s!"{router.sourceID}/nftables/nftables/{rule.objectIndex}/rule"),
        ("nativeSource", Lean.toJson rule.sourceID), ("handle", Lean.toJson rule.handle),
        ("objectIndex", Lean.toJson rule.objectIndex),
        ("expressionIndices", Lean.toJson rule.expressionIndices),
        ("comment", Lean.toJson rule.comment)]))])),
    ("report", report)]

private def linuxScope : IO Unit := do
  IO.println "Scope: main-table IPv4 transit under these supplied assumptions."
  for assumption in linuxAssumptions do IO.println assumption

private def linux (path : String) (json : Bool) : IO UInt32 := do
  let snapshot ← unwrap (Import.LinuxDeployment.Snapshot.parse (← IO.FS.readFile path))
  let report ← unwrap (DataPlane.Check.check snapshot.compile)
  if json then IO.println (linuxEnvelope snapshot (DataPlane.Check.renderJson report)).pretty
  else
    linuxScope
    IO.println (DataPlane.Check.render report)
  return if report.compliant then 0 else 1

private def linuxTraffic (path queryId selectionPath : String) (budget : Nat) (json : Bool) : IO UInt32 := do
  let snapshot ← unwrap (Import.LinuxDeployment.Snapshot.parse (← IO.FS.readFile path))
  let config := snapshot.compile
  let query ← match config.requirements.find? (·.id == queryId) with
    | none => throw (IO.userError s!"Unknown traffic query: {queryId}.")
    | some query => pure query
  let selection ← unwrap (DataPlane.Config.parseTrafficSelection (← IO.FS.readFile selectionPath))
  let checked ← unwrap (DataPlane.Check.checkTraffic config query selection budget)
  if json then
    let report := Lean.Json.mkObj [
      ("compliant", Lean.toJson checked.value), ("requirement", Lean.toJson query.id),
      ("scope", Lean.toJson "all-selected-packets"),
      ("partitionCells", Lean.toJson (config.trafficPartition selection).cellCount),
      ("evidence", Lean.toJson checked.evidence)]
    IO.println (linuxEnvelope snapshot report).pretty
  else
    linuxScope
    IO.println (if checked.value then "COMPLIANT" else "NONCOMPLIANT")
    IO.println s!"Requirement {query.id}: all selected packets and endpoint pairs."
    for line in checked.evidence do IO.println line
  return if checked.value then 0 else 1

private def compileACL (path : String) (budget : Nat) : IO UInt32 := do
  let intents ← unwrap (Compile.Policy.parse (← IO.FS.readFile path))
  match Compile.Nftables.compile intents budget with
  | .ok emitted => IO.println emitted.toJson.pretty; return 0
  | .error error@(.intent (.conflict _)) =>
    (← IO.getStderr).putStrLn error.describe
    return 1
  | .error error => throw (IO.userError error.describe)

private def transfer (path : String) (budget : Nat) (json : Bool) : IO UInt32 := do
  let input ← unwrap (Import.TransferConfig.Input.parse (← IO.FS.readFile path))
  let result ← unwrap (Check.Transfer.check input.config input.query budget)
  IO.println (if json then (Import.TransferConfig.resultJson input result).pretty
    else Import.TransferConfig.render input result)
  return if result.value then 0 else 1

private def natTrace (path : String) (budget : Nat) (json : Bool) : IO UInt32 := do
  let input ← unwrap (Check.NATTrace.Input.parse (← IO.FS.readFile path) budget)
  let report := input.check
  IO.println (if json then report.renderJson.pretty else report.render)
  return if report.compliant then 0 else 1

private def wifi (path : String) (model : Option String) (json : Bool) : IO UInt32 := do
  let ap ← IO.FS.readFile path
  let report ← match model with
    | none => unwrap (Wifi.checkText ap)
    | some model => unwrap (Wifi.checkDeployment ap (← IO.FS.readFile model))
  standardsReport report json

private def analyze (path : String) (goalPath : Option String) (budget : Nat) : IO UInt32 := do
  let goals ← match goalPath with
    | none => pure []
    | some path => readRequirements path
  let report ← unwrap (Analysis.analyze (← readRequirements path) goals budget)
  IO.println (Analysis.render report)
  return if report.consistent && report.gaps.isEmpty then 0 else 1

private def budgetValue (text : String) : IO Nat :=
  match text.toNat? with
  | some budget => pure budget
  | none => throw (IO.userError "Use a natural number for the budget.")

private def run (args : List String) : IO UInt32 := do
  match args with
  | ["--help"] | ["-h"] | [] => IO.println usage; return 0
  | ["check", config, policy] => check config policy false
  | ["check", config, policy, "--json"] => check config policy true
  | ["formalize", policy] =>
    IO.println (Render.formalized (← readRequirements policy))
    return 0
  | ["dataplane", path] => dataPlane path false
  | ["dataplane", path, "--json"] => dataPlane path true
  | ["traffic", path, query, selection] => traffic path query selection 100000 false
  | ["traffic", path, query, selection, "--json"] => traffic path query selection 100000 true
  | ["traffic", path, query, selection, "--budget", budget] =>
    traffic path query selection (← budgetValue budget) false
  | ["traffic", path, query, selection, "--budget", budget, "--json"] =>
    traffic path query selection (← budgetValue budget) true
  | ["linux", path] => linux path false
  | ["linux", path, "--json"] => linux path true
  | ["linux-traffic", path, query, selection] => linuxTraffic path query selection 100000 false
  | ["linux-traffic", path, query, selection, "--json"] => linuxTraffic path query selection 100000 true
  | ["linux-traffic", path, query, selection, "--budget", budget] =>
    linuxTraffic path query selection (← budgetValue budget) false
  | ["linux-traffic", path, query, selection, "--budget", budget, "--json"] =>
    linuxTraffic path query selection (← budgetValue budget) true
  | ["compile-acl", path] => compileACL path 100000
  | ["compile-acl", path, "--budget", budget] => compileACL path (← budgetValue budget)
  | ["transfer", path] => transfer path 4096 false
  | ["transfer", path, "--json"] => transfer path 4096 true
  | ["transfer", path, "--budget", budget] => transfer path (← budgetValue budget) false
  | ["transfer", path, "--budget", budget, "--json"] => transfer path (← budgetValue budget) true
  | ["nat-trace", path] => natTrace path 100000 false
  | ["nat-trace", path, "--json"] => natTrace path 100000 true
  | ["nat-trace", path, "--budget", budget] => natTrace path (← budgetValue budget) false
  | ["nat-trace", path, "--budget", budget, "--json"] => natTrace path (← budgetValue budget) true
  | ["fiveg", path] => standardsReport (← unwrap (FiveG.run (← IO.FS.readFile path))) false
  | ["fiveg", path, "--json"] => standardsReport (← unwrap (FiveG.run (← IO.FS.readFile path))) true
  | ["fiveg-coverage"] => standardsReport FiveG.coverage false
  | ["fiveg-coverage", "--json"] => standardsReport FiveG.coverage true
  | ["wifi", path] => wifi path none false
  | ["wifi", path, "--json"] => wifi path none true
  | ["wifi", path, model] => wifi path (some model) false
  | ["wifi", path, model, "--json"] => wifi path (some model) true
  | ["wifi-coverage"] => standardsReport Wifi.coverage false
  | ["wifi-coverage", "--json"] => standardsReport Wifi.coverage true
  | ["analyze", policy] =>
    analyze policy none 100000
  | ["analyze", policy, "--budget", budget] => analyze policy none (← budgetValue budget)
  | ["analyze", policy, goals, "--budget", budget] =>
    analyze policy (some goals) (← budgetValue budget)
  | ["analyze", policy, goals] =>
    analyze policy (some goals) 100000
  | ["demo"] =>
    IO.println "Secure two-layer architecture with replicated inner gateways:"
    let secure ← check "examples/secure.json" "examples/requirements.netlib" false
    IO.println "\nAfter one replica fails:"
    let failover ← check "examples/failover.json" "examples/requirements.netlib" false
    IO.println "\nAfter a direct bypass is introduced (expected violation):"
    let bypass ← check "examples/bypass.json" "examples/requirements.netlib" false
    return if secure == 0 && failover == 0 && bypass == 1 then 0 else 1
  | _ => throw (IO.userError usage)

def main (args : List String) : IO UInt32 := do
  try run args
  catch error =>
    (← IO.getStderr).putStrLn s!"error: {error}"
    return (2 : UInt32)
