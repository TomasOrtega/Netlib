import Netlib.Check.Render
import Netlib.Policy.Analysis
import Netlib.Check.VerifiedCompliance
import Netlib.Check.DataPlane
import Netlib.Standards.ThreeGPP.ServiceAccess
import Netlib.Standards.IEEE80211.Deployment

open Netlib

private def usage : String := "Netlib: checked network requirements\n\n\
  netlib check CONFIG.json REQUIREMENTS.netlib [--json]\n\
  netlib analyze REQUIREMENTS.netlib [GOALS.netlib] [--budget N]\n\
  netlib formalize REQUIREMENTS.netlib\n\
  netlib dataplane CONFIG.json [--json]\n\
  netlib fiveg TRACE.json [--json]\n\
  netlib fiveg-coverage [--json]\n\
  netlib wifi AP.conf [DEPLOYMENT.json] [--json]\n\
  netlib wifi-coverage [--json]\n\
  netlib demo\n\n\
Exit codes: 0 = compliant / sufficient consistent policy; 1 = violation / policy gaps; 2 = input error."

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
  | none => throw (IO.userError "Use a natural number for the search budget.")

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
