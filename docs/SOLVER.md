# Budgeted policy analysis

The executable analysis has no fixed atom limit.
It uses a branch-and-simplify solver with a search node budget.
The original truth-table solver remains a reference interface.

## Search

The solver turns the input formulas into one conjunction.
It selects an atom and checks its false branch first.
An assignment replaces that atom with a constant.
The solver also simplifies constant connectives.

Each completed search returns a model or an impossibility proof.
An unfinished search returns an error.
It cannot report an exhausted search as inconsistent or entailed.

The default budget is 100,000 search nodes per solver query.
Both branches share the remaining budget of that query.
The analysis starts a new budget for each query.
The budget is not a limit on total analysis time or memory.

A larger budget can resolve a search that previously stopped.
A search can still require exponential work.
The removal of the atom cap does not guarantee a fast answer for every policy.

## Guarantees

`Solver.eval_assign` proves the meaning of an atom assignment.
`Solver.solve_model_sound` proves that a returned model satisfies every input formula.
`Solver.solve_unsat_sound` rules out every model after an impossibility result.
`Solver.entails_correct` connects a completed entailment result to the reference semantics.
`Solver.countermodel_sound` proves that a returned countermodel satisfies the policy and refutes the goal.

`Analysis.simplifyUnderFast` removes redundant requirements in sequence.
It keeps the same background laws throughout that process.
Each deletion needs a completed entailment proof.
Its `Reduction.correct` field proves equivalence for every valuation.
It preserves source requirement records in the retained and redundant lists.

Analysis uses the budgeted solver for consistency, removal, gaps, and completion.
It does not enumerate truth-table assignments through a hidden fallback.
An error stops the report instead of returning partial assurance.

## Scope

The solver checks propositional formulas.
Domain laws connect selected observations to the network model.
An abstract model can still describe a combination that no network realizes.
The solver does not add omitted network laws or infer an unstated goal.

## Validation

The local suites compare small solver answers with the reference truth table.
They also check larger independent policies and contradictions.
The analysis suite accepts 40-clause and 80-clause policies.
It checks a large inconsistent core and a duplicate requirement.
Tiny budgets must return an error.

The source and documentation checks in CI do not compile Lean.
Run the Lean suites locally before a source commit.
