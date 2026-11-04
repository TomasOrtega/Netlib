import Netlib.Check.VerifiedCompliance

namespace NetlibTest.Compliance

open Netlib

private def checkThat (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def unwrap (result : Except String α) (label : String) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError s!"{label}: {message}")

private def expectError (result : Except String α) (label : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"expected rejection: {label}")

private def fixture : Config :=
  { devices := [⟨"a", "red", "client"⟩, ⟨"a2", "red", "client"⟩,
      ⟨"g1", "gray", "gateway"⟩, ⟨"g2", "gray", "gateway"⟩,
      ⟨"b", "black", "server"⟩, ⟨"b2", "black", "server"⟩,
      ⟨"orphan", "outside", "device"⟩]
    links := [⟨"a", "g1", "tls", true⟩, ⟨"g1", "b", "tls", true⟩,
      ⟨"g1", "a", "tls", true⟩, ⟨"a2", "g2", "tls", true⟩,
      ⟨"g2", "b", "tls", true⟩, ⟨"g2", "b2", "*", true⟩,
      ⟨"a", "b", "tls", false⟩]
    groups := [⟨"gateways", ["g1", "g2"]⟩] }

private def expectFinding (config : Config) (observation : Observation)
    (expected : Bool) (pairs : Nat) (label : String) : IO Unit := do
  let finding ← unwrap (Netlib.Compliance.observe config observation) label
  checkThat (finding.value == expected) s!"{label}: expected {expected}, got {finding.value}; {finding.evidence}"
  checkThat (finding.pairs == pairs) s!"{label}: wrong number of endpoint pairs"
  checkThat (finding.evidence.length == pairs) s!"{label}: missing per-pair evidence"

private def certificateTests : IO Unit := do
  let nodes := ["a", "b", "c", "d"]
  let edge := fun a b => [("a", "b"), ("b", "c")].contains (a, b)
  let path := Netlib.Certificate.validPath nodes edge "a" "c"
  checkThat (path ["a", "b", "c"]) "valid path rejected"
  checkThat (!path []) "empty path accepted"
  checkThat (!path ["a", "c"]) "missing path edge accepted"
  checkThat (!path ["b", "c"]) "wrong path source accepted"
  checkThat (!path ["a", "b"]) "wrong path destination accepted"
  checkThat (!Netlib.Certificate.validPath ["a", "c"] edge "a" "c" ["a", "b", "c"])
    "undeclared intermediate vertex accepted"
  checkThat (Netlib.Certificate.validPath nodes edge "a" "a" ["a"])
    "zero-hop path rejected"
  checkThat (!Netlib.Certificate.validPath nodes edge "a" "c" ["a"])
    "singleton path with different endpoints accepted"
  checkThat (!Netlib.Certificate.validPath nodes edge "unknown" "unknown" ["unknown"])
    "undeclared singleton accepted"
  checkThat (Netlib.Certificate.validCut nodes edge "a" "d" ["a", "b", "c"])
    "valid closed cut rejected"
  checkThat (!Netlib.Certificate.validCut nodes edge "a" "c" ["a", "b"])
    "cut missing an outgoing successor accepted"
  checkThat (!Netlib.Certificate.validCut nodes edge "a" "d" ["b", "c"])
    "cut missing source accepted"
  checkThat (!Netlib.Certificate.validCut nodes edge "a" "c" ["a", "b", "c"])
    "cut containing target accepted"
  checkThat (!Netlib.Certificate.validCut nodes edge "a" "a" ["a", "b", "c"])
    "cut separating identical endpoints accepted"

private def configTests : IO Unit := do
  let valid := r#"{"devices":[{"id":"a","zone":"red","role":"client"}],"links":[],"groups":[]}"#
  let parsed ← unwrap (Config.parse valid) "minimal JSON"
  checkThat (parsed.ids == ["a"]) "parsed device identity changed"
  for (label, text) in [
    ("malformed JSON", "{"),
    ("unknown top-level field", valid.replace "\"groups\":[]" "\"groups\":[],\"extra\":true"),
    ("missing top-level field", valid.replace ",\"groups\":[]" ""),
    ("unknown device field", valid.replace "\"role\":\"client\"" "\"role\":\"client\",\"extra\":true"),
    ("wrong devices type", valid.replace "\"devices\":[{\"id\":\"a\",\"zone\":\"red\",\"role\":\"client\"}]" "\"devices\":false"),
    ("duplicate device ID", valid.replace
      r#""devices":[{"id":"a","zone":"red","role":"client"}]"#
      r#""devices":[{"id":"a","zone":"red","role":"client"},{"id":"a","zone":"black","role":"server"}]"#),
    ("dangling link", valid.replace "\"links\":[]" "\"links\":[{\"from\":\"a\",\"to\":\"unknown\",\"service\":\"tls\",\"enabled\":true}]"),
    ("non-Boolean enabled flag", valid.replace "\"links\":[]" "\"links\":[{\"from\":\"a\",\"to\":\"a\",\"service\":\"tls\",\"enabled\":\"true\"}]"),
    ("unknown link field", valid.replace "\"links\":[]" "\"links\":[{\"from\":\"a\",\"to\":\"a\",\"service\":\"tls\",\"enabled\":true,\"extra\":true}]"),
    ("empty gateway group", valid.replace "\"groups\":[]" "\"groups\":[{\"name\":\"g\",\"members\":[]}]"),
    ("unknown gateway member", valid.replace "\"groups\":[]" "\"groups\":[{\"name\":\"g\",\"members\":[\"unknown\"]}]"),
    ("duplicate gateway member", valid.replace "\"groups\":[]" "\"groups\":[{\"name\":\"g\",\"members\":[\"a\",\"a\"]}]"),
    ("unknown group field", valid.replace "\"groups\":[]" "\"groups\":[{\"name\":\"g\",\"members\":[\"a\"],\"extra\":true}]") ] do
    expectError (Config.parse text) label
  expectError ({ fixture with groups := fixture.groups ++ fixture.groups }.validate)
    "duplicate group names"
  expectError ({ fixture with devices := [] }.validate) "empty model"

private def languageTests : IO Unit := do
  let text := "# reviewed source\n\nR1: node:a must reach node:b for tls.\nR2: if node:a must reach node:orphan for tls then node:a must reach node:b2 for tls."
  let requirements ← unwrap (Language.parse text) "controlled document"
  checkThat (requirements.length == 2) "wrong parsed requirement count"
  checkThat ((requirements.map (·.line)) == [3, 4]) "source line numbers lost"
  checkThat ((requirements.map (·.id)) == ["R1", "R2"]) "requirement identifiers lost"
  for (label, invalid) in [
    ("empty document", "# only comments\n"),
    ("unsupported sentence", "R1: node:a should encrypt traffic."),
    ("missing period", "R1: node:a must reach node:b for tls"),
    ("duplicate ID", "R1: node:a must reach node:b for tls.\nR1: node:a must reach node:b for tls."),
    ("unknown selector kind", "R1: subnet:red must reach node:b for tls."),
    ("empty selector", "R1: node: must reach node:b for tls."),
    ("invalid selector name", "R1: node:a? must reach node:b for tls."),
    ("wildcard query service", "R1: node:a must reach node:b for *."),
    ("multiple then clauses", "R1: if node:a must reach node:b for tls then node:a must reach node:b for tls then node:a must reach node:b for tls."),
    ("missing conditional consequent", "R1: if node:a must reach node:b for tls then."),
    ("invalid ID", "R 1: node:a must reach node:b for tls.") ] do
    expectError (Language.parse invalid) label
  let report ← unwrap (Netlib.Compliance.check fixture requirements) "conditional evaluation"
  checkThat report.compliant "false antecedent did not imply false consequent"

private def networkTests : IO Unit := do
  let _ ← unwrap fixture.validate "fixture"
  expectFinding fixture (.reach (.node "a") (.node "b") "tls" true) true 1
    "permitted path through cyclic topology"
  expectFinding fixture (.reach (.node "a") (.node "orphan") "tls" true) false 1
    "disconnected target in cyclic topology"
  expectFinding fixture (.reach (.node "a") (.node "a") "tls" true) true 1
    "zero-hop reachability"
  expectFinding fixture (.reach (.node "a") (.node "b") "ssh" true) false 1
    "service-specific isolation"
  expectFinding fixture (.reach (.node "g2") (.node "b2") "ssh" true) true 1
    "wildcard link permits a named service"
  expectFinding fixture (.reach (.zone "red") (.zone "black") "tls" true) false 4
    "universal reachability checks every pair"
  expectFinding fixture (.reach (.zone "red") (.zone "black") "tls" false) true 4
    "existential reachability differs from universal reachability"
  expectFinding fixture (.mediated (.zone "red") (.zone "black") (.group "gateways") "tls")
    true 4 "HA mediation accepts either group member"
  expectFinding fixture (.mediated (.zone "red") (.zone "black") (.role "gateway") "tls")
    true 4 "role selector matches gateway group"
  expectFinding fixture (.mediated (.node "a") (.node "b") (.node "g2") "tls")
    false 1 "visiting a different gateway does not satisfy the selected gateway"
  expectFinding fixture (.mediated (.node "a") (.node "orphan") (.group "gateways") "tls")
    true 1 "mediation is vacuously true without a path"
  expectFinding fixture (.mediated (.node "g1") (.node "b") (.group "gateways") "tls")
    true 1 "gateway at source endpoint"
  expectFinding fixture (.mediated (.node "a") (.node "g1") (.group "gateways") "tls")
    true 1 "gateway at target endpoint"
  expectFinding fixture (.mediated (.node "a") (.node "a") (.group "gateways") "tls")
    false 1 "zero-hop bypass outside gateways"
  expectFinding fixture (.mediated (.node "g1") (.node "g1") (.group "gateways") "tls")
    true 1 "zero-hop path at gateway"
  let bypass := { fixture with links := fixture.links ++ [⟨"a", "b", "tls", true⟩] }
  expectFinding bypass (.mediated (.node "a") (.node "b") (.group "gateways") "tls")
    false 1 "enabled direct link creates a gateway bypass"
  let isolated ← unwrap (Language.parse "ISO: node:a must be isolated from node:orphan for tls.")
    "isolation requirement"
  let isolationReport ← unwrap (Netlib.Compliance.check fixture isolated) "isolation check"
  checkThat isolationReport.compliant "disconnected pair failed isolation"
  let notIsolated ← unwrap (Language.parse "ISO: zone:red must be isolated from zone:black for tls.")
    "quantified isolation requirement"
  let notIsolatedReport ← unwrap (Netlib.Compliance.check fixture notIsolated) "quantified isolation"
  checkThat (!notIsolatedReport.compliant) "isolation sampled endpoint pairs"
  for selector in [Selector.node "unknown", .zone "unknown", .role "unknown", .group "unknown"] do
    expectError (Netlib.Compliance.observe fixture (.reach selector (.node "b") "tls" true))
      "empty source selector"
    expectError (Netlib.Compliance.observe fixture (.reach (.node "a") selector "tls" true))
      "empty target selector"
    expectError (Netlib.Compliance.observe fixture (.mediated (.node "a") (.node "b") selector "tls"))
      "empty gateway selector"

private def certifiedTests : IO Unit := do
  for (observation, expected) in [
    (Observation.reach (.zone "red") (.zone "black") "tls" true, false),
    (.reach (.zone "red") (.zone "black") "tls" false, true),
    (.reach (.node "a") (.node "a") "tls" true, true),
    (.mediated (.node "a") (.node "a") (.group "gateways") "tls", false),
    (.mediated (.node "g1") (.node "g1") (.group "gateways") "tls", true),
    (.mediated (.zone "red") (.zone "black") (.group "gateways") "tls", true) ] do
    let certified ← unwrap (Verification.evaluate fixture observation)
      s!"certified evaluator: {observation.render}"
    checkThat (certified.value == expected)
      s!"certified evaluator disagrees with expected semantics: {observation.render}"
  let policy ← unwrap (Language.parse
    ("AVAILABLE: node:a must reach node:b for tls.\n" ++
      "GATEWAY: zone:red must traverse group:gateways before zone:black for tls.\n" ++
      "ISOLATED: node:a must be isolated from node:orphan for tls."))
    "verified policy"
  let bypass := { fixture with links := fixture.links ++ [⟨"a", "b", "tls", true⟩] }
  for (config, expected) in [(fixture, true), (bypass, false)] do
    let report ← unwrap (VerifiedCompliance.check config policy) "verified compliance"
    checkThat (report.compliant == expected) "verified report failed secure/bypass distinction"
    checkThat (report.findings.length == 3) "verified report lost policy observations"
    for finding in report.findings do
      let certified ← unwrap (Verification.evaluate config finding.observation)
        "verified finding reevaluation"
      checkThat (finding.value == certified.value) "reported and certified findings disagree"
    let gateway := report.results.find? (fun result => result.1.id == "GATEWAY")
    checkThat ((gateway.map Prod.snd) == some expected) "wrong verified gateway requirement result"
  for sentence in [
    "node:unknown must reach node:b for tls.",
    "node:a must reach zone:unknown for tls.",
    "node:a must traverse group:unknown before node:b for tls.",
    "if node:a must reach node:orphan for tls then node:unknown must reach node:b for tls." ] do
    let requirements ← unwrap (Language.parse ("INVALID: " ++ sentence)) "unknown-selector policy"
    expectError (VerifiedCompliance.check fixture requirements)
      "verified wrapper must reject empty selectors even in inactive conditional branches"

def run : IO Unit := do
  certificateTests
  configTests
  languageTests
  networkTests
  certifiedTests
  IO.println "Compliance tests passed"

end NetlibTest.Compliance
