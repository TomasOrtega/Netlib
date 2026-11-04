import Netlib.Core.Solver

namespace NetlibTest.Solver

open Netlib

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def expectBudgetError (result : Except String α) : IO Unit :=
  match result with
  | .error message => ensure ((message.splitOn "budget").length > 1) "Explain the solver budget error."
  | .ok _ => throw (IO.userError "An exhausted search budget must not produce a result.")

private def scalingTests : IO Unit := do
  for size in [40, 100] do
    let policy := (List.range size).map (fun atom => Formula.atom atom)
    let result ← unwrap (Netlib.Solver.solve policy (2 * size + 1))
    match result with
    | none => throw (IO.userError "Independent unit requirements must have a model.")
    | some model => ensure ((List.range size).all model) "The model must satisfy every unit requirement."
    let contradiction := policy ++ [.neg (.atom (size - 1))]
    let result ← unwrap (Netlib.Solver.solve contradiction (2 * size + 1))
    match result with
    | some _ => throw (IO.userError "Contradictory unit requirements must have no model.")
    | none => pure ()
    let entailed ← unwrap (Netlib.Solver.entails policy (.atom (size - 1)) (2 * size + 1))
    ensure entailed "The final unit requirement must follow from the policy."
    expectBudgetError (Netlib.Solver.solve policy (2 * size))
  expectBudgetError (Netlib.Solver.solve ([] : List (Formula Nat)) 0)
  let budget := 1000
  let policy := (List.range 100).map (fun atom => Formula.atom atom)
  let outcome := Netlib.Solver.search budget (Netlib.Solver.conjoin policy)
  ensure (outcome.remaining == 799) "Both search branches must share the node budget."

private def crosscheckTests : IO Unit := do
  let base : List (Formula Nat) := [.top, .bot, .atom 0, .atom 1, .atom 2]
  let binary := base.flatMap (fun left => base.flatMap
    (fun right => [.conj left right, .disj left right, .impl left right]))
  let formulas := base ++ base.map Formula.neg ++ binary
  for premise in formulas do
    for other in base do
      let policy := [premise, other]
      let value ← unwrap (Netlib.Solver.satisfiable policy 1000)
      ensure (value == Reasoning.satisfiable policy) "Branch search and the truth table must agree on satisfiability."
      for goal in base do
        let entailed ← unwrap (Netlib.Solver.entails policy goal 1000)
        ensure (entailed == Reasoning.entails policy goal) "Branch search and the truth table must agree on entailment."
        let witness ← unwrap (Netlib.Solver.countermodel? policy goal 1000)
        match witness with
        | none => ensure entailed "No countermodel must mean entailment."
        | some model =>
          ensure (Reasoning.satisfies model policy && !goal.eval model)
            "A countermodel must satisfy the policy and refute the goal."

def run : IO Unit := do
  scalingTests
  crosscheckTests
  IO.println "Solver tests passed."

end NetlibTest.Solver
