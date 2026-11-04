import Netlib.Check.Render
import Netlib.Policy.Analysis
import Netlib.Check.VerifiedCompliance

open Netlib

private def usage : String := "Netlib: checked network requirements\n\n\
  netlib check CONFIG.json REQUIREMENTS.netlib [--json]\n\
  netlib analyze REQUIREMENTS.netlib [GOALS.netlib]\n\
  netlib formalize REQUIREMENTS.netlib\n\
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

private def run (args : List String) : IO UInt32 := do
  match args with
  | ["--help"] | ["-h"] | [] => IO.println usage; return 0
  | ["check", config, policy] => check config policy false
  | ["check", config, policy, "--json"] => check config policy true
  | ["formalize", policy] =>
    IO.println (Render.formalized (← readRequirements policy))
    return 0
  | ["analyze", policy] =>
    let report ← unwrap (Analysis.analyze (← readRequirements policy) [])
    IO.println (Analysis.render report)
    return if report.consistent && report.gaps.isEmpty then 0 else 1
  | ["analyze", policy, goals] =>
    let report ← unwrap (Analysis.analyze (← readRequirements policy) (← readRequirements goals))
    IO.println (Analysis.render report)
    return if report.consistent && report.gaps.isEmpty then 0 else 1
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
