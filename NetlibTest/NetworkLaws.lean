import Netlib.Policy.Analysis

namespace NetlibTest.NetworkLaws

open Netlib

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def chain := "AB: node:a must reach node:b for https.\nBC: node:b must reach node:c for https."

private def independent (count : Nat) : List Requirement :=
  (List.range count).map fun n =>
    ⟨s!"R{n}", n + 1, "Independent reachability.",
      .atom (.reach (.node s!"a{n}") (.node s!"b{n}") "https" true)⟩

private def independentTests : IO Unit := do
  for count in [8, 40, 80] do
    let requirements := independent count
    let observations := Reasoning.support (requirements.map (·.formula))
    let laws := Language.laws observations
    require (laws.length == 2 * count)
      s!"Independent reach policies generated unrelated laws: {count} requirements, {laws.length} laws."
    let report ← unwrap (Analysis.analyze requirements [])
    require (report.consistent && report.retained.length == count && report.redundant.isEmpty)
      "Independent reach requirements lost their meanings."
    require (report.atomCount == 2 * count) "Independent reach policies introduced unrelated atoms."

def run : IO Unit := do
  independentTests
  let premises ← unwrap (Language.parse chain)
  let goal ← unwrap (Language.parse "AC: node:a must reach node:c for https.")
  let entailed ← unwrap (Analysis.analyze premises goal)
  require (entailed.consistent && entailed.gaps.isEmpty) "Reachability did not compose."
  let longer ← unwrap (Language.parse (chain ++ "\nCD: node:c must reach node:d for https."))
  let distant ← unwrap (Language.parse "AD: node:a must reach node:d for https.")
  let closure ← unwrap (Analysis.analyze longer distant)
  require (closure.consistent && closure.gaps.isEmpty) "A longer path did not compose."
  let reordered ← unwrap (Analysis.analyze longer.reverse distant)
  require (reordered.consistent && reordered.gaps.isEmpty) "Composition depended on clause order."
  let extended := (List.range 8).map fun n =>
    (⟨s!"H{n}", n + 1, "One hop in a longer chain.",
      .atom (.reach (.node s!"n{n}") (.node s!"n{n + 1}") "https" true)⟩ : Requirement)
  let endToEnd : Requirement := ⟨"END", 9, "The complete chain reaches its target.",
    .atom (.reach (.node "n0") (.node "n8") "https" true)⟩
  let chained ← unwrap (Analysis.analyze extended.reverse [endToEnd])
  require (chained.consistent && chained.gaps.isEmpty) "An eight-hop path did not compose."
  let copies := longer.map fun requirement => { requirement with id := requirement.id ++ "_COPY" }
  let duplicate ← unwrap (Analysis.analyze (longer ++ copies) distant)
  require (duplicate.consistent && duplicate.gaps.isEmpty && duplicate.retained.length == longer.length)
    "Fixed background laws changed during chain minimization."
  let isolated ← unwrap (Language.parse "DENY: node:a must be isolated from node:c for https.")
  let conflict ← unwrap (Analysis.analyze (premises ++ isolated) [])
  require (!conflict.consistent) "An impossible reachability chain was consistent."
  let self ← unwrap (Language.parse "SELF: node:a must be isolated from node:a for https.")
  let reflexive ← unwrap (Analysis.analyze self [])
  require (!reflexive.consistent) "A node was isolated from itself."
  let mixed ← unwrap (Language.parse
    "AB: node:a must reach node:b for https.\nBC: node:b must reach node:c for ssh.")
  let separate ← unwrap (Analysis.analyze mixed goal)
  require (separate.consistent && separate.gaps.length == 1) "Different services composed."
  let someLeft : Requirement := ⟨"LEFT", 1, "Some first path.",
    .atom (.reach (.node "a") (.group "relay") "https" false)⟩
  let someRight : Requirement := ⟨"RIGHT", 2, "Some second path.",
    .atom (.reach (.group "relay") (.node "c") "https" false)⟩
  let existential ← unwrap (Analysis.analyze [someLeft, someRight] goal)
  require (existential.consistent && existential.gaps.length == 1)
    "Paths through different group members composed."
  let universal ← unwrap (Language.parse
    "LEFT: node:a must reach group:relay for https.\nRIGHT: group:relay must reach node:c for https.")
  let grouped ← unwrap (Analysis.analyze universal goal)
  require (grouped.consistent && grouped.gaps.isEmpty) "Universal group paths did not compose."
  IO.println "Network law tests passed."

end NetlibTest.NetworkLaws
