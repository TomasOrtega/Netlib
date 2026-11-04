import Netlib.Policy.Analysis

namespace NetlibTest.LargePolicy

open Netlib

private def policy (count : Nat) : List Requirement :=
  (List.range count).map fun n =>
    ⟨s!"R{n}", n + 1, s!"Gateway {n} must mediate the path.",
      .atom (.mediated (.node "a") (.node "b") (.group s!"g{n}") "tls")⟩

private def checkThat (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

def run : IO Unit := do
  match Analysis.analyze (policy 40) (policy 1) with
  | .error message => throw (IO.userError s!"Large policy failed: {message}")
  | .ok report =>
    unless report.consistent && report.gaps.isEmpty && report.retained.length == 40 do
      throw (IO.userError "The large policy result is incorrect.")
  let eighty ← unwrap (Analysis.analyze (policy 80) (policy 2))
  checkThat (eighty.consistent && eighty.gaps.isEmpty && eighty.retained.length == 80)
    "The 80-clause policy failed."
  let first ← match (policy 1).head? with
    | some first => pure first
    | none => throw (IO.userError "The fixture has no first requirement.")
  let contradiction : Requirement :=
    ⟨"DENY0", 81, "The first gateway requirement is false.", .neg first.formula⟩
  let conflict ← unwrap (Analysis.analyze (policy 80 ++ [contradiction]) [])
  checkThat (!conflict.consistent && conflict.conflict.length == 2)
    "The large contradictory policy lost its conflict."
  let duplicate ← unwrap (Analysis.analyze (policy 40 ++ [first]) [])
  checkThat (duplicate.consistent && duplicate.retained.length == 40 &&
    duplicate.redundant.length == 1)
    "The large duplicate policy changed its meaning."
  for budget in [0, 1, 2] do
    match Analysis.analyze (policy 40) [] budget with
    | .error message =>
      checkThat ((message.splitOn "budget").length > 1) "The budget error lost its cause."
    | .ok _ => throw (IO.userError "A tiny budget produced a policy result.")
  IO.println "Large policy tests passed."

end NetlibTest.LargePolicy
