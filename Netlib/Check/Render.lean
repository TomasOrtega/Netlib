import Netlib.Check.Compliance

namespace Netlib.Render

open Lean

def formula : Formula Observation → String
  | .atom a => a.render
  | .top => "true"
  | .bot => "false"
  | .neg p => s!"not ({formula p})"
  | .conj p q => s!"({formula p}) and ({formula q})"
  | .disj p q => s!"({formula p}) or ({formula q})"
  | .impl p q => s!"if ({formula p}) then ({formula q})"

def formalized (requirements : List Requirement) : String :=
  String.intercalate "\n" (requirements.map fun r =>
    s!"{r.id} (line {r.line}): {formula r.formula}\n  source: {r.text}")

def report (r : Compliance.Report) : String := Id.run do
  let mut lines := [if r.compliant then "COMPLIANT" else "NONCOMPLIANT"]
  for (requirement, satisfied) in r.results do
    lines := lines ++ [s!"{if satisfied then "PASS" else "FAIL"} {requirement.id} (line {requirement.line}): {requirement.text}"]
  for finding in r.findings do
    lines := lines ++ [s!"{finding.observation.render}: {finding.value} ({finding.pairs} endpoint pairs)"]
    lines := lines ++ finding.evidence.map ("  " ++ ·)
  if r.findings.any (fun f => match f.observation with | .mediated .. => true | _ => false) then
    lines := lines ++ ["Mediation can hold when no path exists. Add reach requirements for availability."]
  return String.intercalate "\n" lines

def reportJson (r : Compliance.Report) : Json :=
  Json.mkObj [
    ("compliant", toJson r.compliant),
    ("requirements", toJson (r.results.map fun (req, passed) => Json.mkObj [
      ("id", toJson req.id), ("line", toJson req.line), ("source", toJson req.text),
      ("formal", toJson (formula req.formula)), ("passed", toJson passed)])),
    ("observations", toJson (r.findings.map fun f => Json.mkObj [
      ("claim", toJson f.observation.render), ("value", toJson f.value),
      ("pairs", toJson f.pairs), ("evidence", toJson f.evidence)])),
    ("semantics", toJson "directed, named traffic class, zero-hop paths, endpoint-inclusive gateways; mediation does not imply availability")]

end Netlib.Render
