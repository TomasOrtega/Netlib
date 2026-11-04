import Netlib.Standards.ThreeGPP.ServiceAccess

namespace NetlibTest.FiveG

open Netlib Netlib.Protocol

private def context : Context := ⟨"amf", "udm", "nrf"⟩
private def readScope : Scope := ⟨"nudm-sdm", "read"⟩
private def writeScope : Scope := ⟨"nudm-sdm", "write"⟩
private def token : Credential := ⟨"nrf", "amf", "udm", [readScope], 10, true⟩
private def ready : Session := ⟨true, some token, 0, none⟩

example : Session.permits context ready readScope = true := by decide
example : Session.permits context ready writeScope = false := by decide
example : Session.permits context .initial readScope = false := by decide
example : Session.permits context { ready with authenticated := false } readScope = false := by decide
example : Session.permits context { ready with credential := none } readScope = false := by decide
example : Session.permits context { ready with now := 10 } readScope = false := by decide
example : Session.permits context { ready with now := 9 } readScope = true := by decide
example : Session.permits context
    { ready with credential := some { token with issuer := "other-nrf" } } readScope = false := by decide
example : Session.permits context
    { ready with credential := some { token with subject := "other-amf" } } readScope = false := by decide
example : Session.permits context
    { ready with credential := some { token with audience := "other-udm" } } readScope = false := by decide
example : Session.permits context
    { ready with credential := some { token with integrity := false } } readScope = false := by decide
example : Session.permits context
    { ready with credential := some { token with scopes := [] } } readScope = false := by decide

example : (Session.step context ready (.request readScope)).admitted = some readScope := by decide
example : (Session.step context ready (.request writeScope)).admitted = none := by decide
example : Session.permits context (Session.step context ready .revoke) readScope = false :=
  Session.revoked_denied _ _ _
example : Session.permits context (Session.step context ready .close) readScope = false :=
  Session.closed_denied _ _ _
example : Session.permits context
    (Session.step context ready (.request readScope)) readScope = true := by decide
example : (Session.step context { ready with now := 8 } (.advance 3)).now = 8 := by decide
example : (Session.step context ready (.advance 10)).admitted = none := by decide
example : Session.Safe context (Session.step context ready (.request readScope)) :=
  Session.step_safe _ _ _
example : Session.Safe context
    (Session.run context .initial [.authenticate true, .install token, .request readScope]) :=
  Session.run_safe _ _ _ (Session.initial_safe _)
example : (Session.policy context ready).allows ⟨"amf", "nudm-sdm", "read"⟩ = true := by decide
example : (Session.policy context ready).allows ⟨"other-amf", "nudm-sdm", "read"⟩ = false := by decide

private def secure : Netlib.FiveG.Trace :=
  ⟨context, [.authenticate true, .token token, .request readScope true,
    .request readScope true, .request writeScope false,
    .tick 10, .request readScope false, .close, .request readScope false]⟩

private def violation : Netlib.FiveG.Trace :=
  ⟨context, [.authenticate true, .token token, .request writeScope true]⟩

example : (Netlib.FiveG.check secure).compliant = true := by decide
example : (Netlib.FiveG.check violation).compliant = false := by decide
example : (Netlib.FiveG.check ⟨context, []⟩).compliant = false := by decide
example : (Netlib.FiveG.check ⟨context, []⟩).complete = false := by decide
example : Netlib.FiveG.coverage.compliant = false := by decide
example : Netlib.FiveG.coverage.complete = false := by decide
example (attempt : Netlib.FiveG.Admission) (member : attempt ∈ Netlib.FiveG.admissions secure)
    (accepted : attempt.accepted = true) :
    Session.Valid context attempt.state attempt.scope :=
  Netlib.FiveG.check_compliant_safe secure (by decide) attempt member accepted

private def checkThat (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def unwrap (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw (IO.userError message)

private def expectError (value : Except String α) (message : String) : IO Unit :=
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"Expected an input error: {message}.")

def run : IO Unit := do
  let base ← IO.FS.readFile "examples/5g/secure.json"
  let parsed ← unwrap (Netlib.FiveG.parse base)
  let report := Netlib.FiveG.check parsed
  checkThat report.compliant "The secure 5G trace failed."
  checkThat (report.findings.length == 9) "The 5G report lost a requirement."
  checkThat ((Netlib.FiveG.admissions parsed).length == 5) "The trace lost a request."
  checkThat (report.findings.all (fun f => f.requirement.source.version == "19.5.0 Release 19"))
    "The report lost its source version."
  let denial ← unwrap (Netlib.FiveG.run (← IO.FS.readFile "examples/5g/correct-denial.json"))
  checkThat denial.compliant "A correct denial failed the admission safety profile."
  for (file, id) in [
      ("unauthenticated", "5G-MUTUAL-AUTH"), ("missing-token", "5G-TOKEN"),
      ("bad-issuer", "5G-ISSUER"), ("bad-integrity", "5G-INTEGRITY"),
      ("bad-subject", "5G-SUBJECT"), ("bad-audience", "5G-AUDIENCE"),
      ("bad-scope", "5G-SCOPE"), ("expired", "5G-EXPIRATION")] do
    let report ← unwrap (Netlib.FiveG.run (← IO.FS.readFile s!"examples/5g/{file}.json"))
    checkThat (!report.compliant) s!"The profile accepted the {file} violation."
    checkThat (report.findings.any (fun f =>
      f.requirement.id == id && f.status == .violated))
      s!"The report did not identify {id}."
  for file in ["invalid-clock", "unsupported-revocation"] do
    expectError (Netlib.FiveG.parse (← IO.FS.readFile s!"examples/5g/{file}.json")) file
  for (text, label) in [
      ("{", "malformed JSON"),
      (base.replace "\"schema\": 1" "\"schema\": 2", "unknown schema"),
      (base.replace "\"schema\": 1" "\"schema\": 1.5", "fractional schema"),
      (base.replace "\"schema\": 1" "\"schema\": -1", "negative schema"),
      (base.replace "\"mode\": \"direct-nf-instance\"" "\"mode\": \"indirect\"", "wrong mode"),
      (base.replace "\"consumer\": \"amf\"" "\"consumer\": \"\"", "empty identity"),
      (base.replace "\"issuer\": \"nrf\"" "\"issuer\": \"nrf\", \"slice\": \"s1\"", "unsupported claim"),
      (base.replace "\"expiresAt\": 10" "\"expiresAt\": 1.5", "fractional expiration"),
      (base.replace "\"expiresAt\": 10" "\"expiresAt\": -1", "negative expiration"),
      (base.replace "\"integrity\": true" "\"integrity\": \"true\"", "non-Boolean integrity"),
      (base.replace "\"accepted\": true" "\"accepted\": 1", "non-Boolean admission")] do
    expectError (Netlib.FiveG.parse text) label
  IO.println "5G session and profile tests passed."

end NetlibTest.FiveG
