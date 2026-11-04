import Netlib.Core.Reasoning

/-!
# Budgeted propositional search

The solver assigns one atom at each branch and simplifies constants.
Each answer carries a proof.
The budget counts search nodes across both branches.
A budget error makes no satisfiability claim.
-/

namespace Netlib.Solver

variable {Atom : Type u} [DecidableEq Atom]

private def smartNeg : Formula Atom → Formula Atom
  | .top => .bot
  | .bot => .top
  | p => .neg p

private def smartAnd : Formula Atom → Formula Atom → Formula Atom
  | .bot, _ | _, .bot => .bot
  | .top, p | p, .top => p
  | p, q => .conj p q

private def smartOr : Formula Atom → Formula Atom → Formula Atom
  | .top, _ | _, .top => .top
  | .bot, p | p, .bot => p
  | p, q => .disj p q

private def smartImp : Formula Atom → Formula Atom → Formula Atom
  | .bot, _ | _, .top => .top
  | .top, p => p
  | p, .bot => smartNeg p
  | p, q => .impl p q

omit [DecidableEq Atom] in
private theorem eval_smartNeg (p : Formula Atom) (v : Atom → Bool) :
    (smartNeg p).eval v = !p.eval v := by
  cases p <;> simp [smartNeg, Formula.eval]

omit [DecidableEq Atom] in
private theorem eval_smartAnd (p q : Formula Atom) (v : Atom → Bool) :
    (smartAnd p q).eval v = (p.eval v && q.eval v) := by
  cases p <;> cases q <;> simp [smartAnd, Formula.eval]

omit [DecidableEq Atom] in
private theorem eval_smartOr (p q : Formula Atom) (v : Atom → Bool) :
    (smartOr p q).eval v = (p.eval v || q.eval v) := by
  cases p <;> cases q <;> simp [smartOr, Formula.eval]

omit [DecidableEq Atom] in
private theorem eval_smartImp (p q : Formula Atom) (v : Atom → Bool) :
    (smartImp p q).eval v = (!p.eval v || q.eval v) := by
  cases p <;> cases q <;> simp [smartImp, Formula.eval, eval_smartNeg]

/-- An assignment changes exactly one atom value. -/
def update (v : Atom → Bool) (key : Atom) (value : Bool) : Atom → Bool :=
  fun atom => if atom = key then value else v atom

/-- Replace one atom by a constant and simplify each connective. -/
def assign (key : Atom) (value : Bool) : Formula Atom → Formula Atom
  | .atom atom => if atom = key then (if value then .top else .bot) else .atom atom
  | .top => .top
  | .bot => .bot
  | .neg p => smartNeg (assign key value p)
  | .conj p q => smartAnd (assign key value p) (assign key value q)
  | .disj p q => smartOr (assign key value p) (assign key value q)
  | .impl p q => smartImp (assign key value p) (assign key value q)

/-- Formula replacement agrees with the corresponding valuation update. -/
theorem eval_assign (key : Atom) (value : Bool) (p : Formula Atom) (v : Atom → Bool) :
    (assign key value p).eval v = p.eval (update v key value) := by
  induction p with
  | atom atom => by_cases same : atom = key <;> cases value <;> simp [assign, Formula.eval, update, same]
  | top => rfl
  | bot => rfl
  | neg p ih => simp only [assign, eval_smartNeg, Formula.eval, ih]
  | conj p q ihp ihq => simp only [assign, eval_smartAnd, Formula.eval, ihp, ihq]
  | disj p q ihp ihq => simp only [assign, eval_smartOr, Formula.eval, ihp, ihq]
  | impl p q ihp ihq => simp only [assign, eval_smartImp, Formula.eval, ihp, ihq]

private theorem update_current (v : Atom → Bool) (key : Atom) : update v key (v key) = v := by
  funext atom
  by_cases same : atom = key <;> simp [update, same]

private theorem unsat_branches (p : Formula Atom) (key : Atom)
    (left : ∀ v, (assign key false p).eval v = false)
    (right : ∀ v, (assign key true p).eval v = false) : ∀ v, p.eval v = false := by
  intro v
  have branch : (assign key (v key) p).eval v = false := by
    cases value : v key with
    | false => exact left v
    | true => exact right v
  simpa only [eval_assign, update_current] using branch

/-- A model or an impossibility proof justifies each completed answer. -/
inductive Answer (p : Formula Atom) where
  | sat (valuation : Atom → Bool) (correct : p.eval valuation = true)
  | unsat (correct : ∀ valuation, p.eval valuation = false)
  | unknown

structure Outcome (p : Formula Atom) (budget : Nat) where
  answer : Answer p
  remaining : Nat
  bounded : remaining ≤ budget

/-- Search consumes one node before each branch or constant result. -/
def search (budget : Nat) (p : Formula Atom) : Outcome p budget :=
  match budget with
  | 0 => ⟨.unknown, 0, Nat.le_refl _⟩
  | fuel + 1 =>
    match atoms : p.atoms with
    | [] =>
      let v := fun _ => false
      match value : p.eval v with
      | true => ⟨.sat v value, fuel, Nat.le_succ _⟩
      | false =>
        ⟨.unsat (fun other => by
          have agree := p.eval_eq_of_agree other v (fun atom member => by simp [atoms] at member)
          exact agree.trans value), fuel, Nat.le_succ _⟩
    | key :: _ =>
      let left := search fuel (assign key false p)
      match left.answer with
      | .sat v correct =>
        ⟨.sat (update v key false) (by rw [← eval_assign]; exact correct),
          left.remaining, Nat.le_trans left.bounded (Nat.le_succ _)⟩
      | .unknown => ⟨.unknown, left.remaining, Nat.le_trans left.bounded (Nat.le_succ _)⟩
      | .unsat rejectedLeft =>
        let right := search left.remaining (assign key true p)
        let bounded := Nat.le_trans right.bounded (Nat.le_trans left.bounded (Nat.le_succ _))
        match right.answer with
        | .sat v correct =>
          ⟨.sat (update v key true) (by rw [← eval_assign]; exact correct), right.remaining, bounded⟩
        | .unsat rejectedRight =>
          ⟨.unsat (unsat_branches p key rejectedLeft rejectedRight), right.remaining, bounded⟩
        | .unknown => ⟨.unknown, right.remaining, bounded⟩
termination_by budget
decreasing_by
  · omega
  · exact Nat.lt_succ_of_le (Outcome.bounded _)

/-- A policy is the conjunction of its original formulas. -/
def conjoin : List (Formula Atom) → Formula Atom
  | [] => .top
  | p :: policy => .conj p (conjoin policy)

omit [DecidableEq Atom] in
theorem conjoin_correct (policy : List (Formula Atom)) (v : Atom → Bool) :
    (conjoin policy).eval v = true ↔ Reasoning.Models v policy := by
  induction policy with
  | nil => simp [conjoin, Formula.eval, Reasoning.Models]
  | cons p policy ih =>
    simp only [conjoin, Formula.eval, Bool.and_eq_true, Reasoning.models_cons]
    exact and_congr (Formula.eval_eq_true_iff _ _) ih

/-- An exhausted budget is an error. It is never an unsatisfiable answer. -/
def solve (policy : List (Formula Atom)) (budget : Nat := 100000) :
    Except String (Option (Atom → Bool)) :=
  match (search budget (conjoin policy)).answer with
  | .sat valuation _ => .ok (some valuation)
  | .unsat _ => .ok none
  | .unknown => .error s!"The solver used its budget of {budget} search nodes."

theorem solve_model_sound (policy : List (Formula Atom)) (budget : Nat) (v : Atom → Bool)
    (found : solve policy budget = .ok (some v)) : Reasoning.Models v policy := by
  unfold solve at found
  cases answer : (search budget (conjoin policy)).answer with
  | sat valuation correct =>
    simp only [answer, Except.ok.injEq, Option.some.injEq] at found
    subst valuation
    exact (conjoin_correct _ _).mp correct
  | unsat correct => simp [answer] at found
  | unknown => simp [answer] at found

theorem solve_unsat_sound (policy : List (Formula Atom)) (budget : Nat)
    (found : solve policy budget = .ok none) : ∀ v, ¬Reasoning.Models v policy := by
  unfold solve at found
  cases answer : (search budget (conjoin policy)).answer with
  | sat valuation correct => simp [answer] at found
  | unsat correct =>
    intro v model
    have := (conjoin_correct _ _).mpr model
    simp [correct v] at this
  | unknown => simp [answer] at found

def satisfiable (policy : List (Formula Atom)) (budget : Nat := 100000) : Except String Bool :=
  match solve policy budget with
  | .error message => .error message
  | .ok none => .ok false
  | .ok (some _) => .ok true

def countermodel? (policy : List (Formula Atom)) (goal : Formula Atom) (budget : Nat := 100000) :
    Except String (Option (Atom → Bool)) :=
  solve (policy ++ [.neg goal]) budget

def entails (policy : List (Formula Atom)) (goal : Formula Atom) (budget : Nat := 100000) :
    Except String Bool :=
  match countermodel? policy goal budget with
  | .error message => .error message
  | .ok none => .ok true
  | .ok (some _) => .ok false

theorem countermodel_sound (policy : List (Formula Atom)) (goal : Formula Atom)
    (budget : Nat) (v : Atom → Bool) (found : countermodel? policy goal budget = .ok (some v)) :
    Reasoning.Models v policy ∧ ¬goal.Holds v := by
  have model := solve_model_sound (policy ++ [.neg goal]) budget v (by simpa only [countermodel?] using found)
  simpa [Reasoning.models_append, Reasoning.models_cons, Formula.Holds] using model

theorem entails_sound (policy : List (Formula Atom)) (goal : Formula Atom) (budget : Nat)
    (found : entails policy goal budget = .ok true) : Reasoning.entails policy goal = true := by
  apply (Reasoning.entails_iff _ _).mpr
  intro v model
  unfold entails at found
  cases answer : countermodel? policy goal budget with
  | error message => simp [answer] at found
  | ok result =>
    cases result with
    | some valuation => simp [answer] at found
    | none =>
      have impossible := solve_unsat_sound (policy ++ [.neg goal]) budget (by simpa only [countermodel?] using answer) v
      classical
      exact Classical.byContradiction (fun falseGoal => impossible
        ((Reasoning.models_append _ _ _).mpr ⟨model, by
          simpa [Reasoning.Models, Formula.Holds] using falseGoal⟩))

/-- A false entailment result has a model that refutes the goal. -/
theorem entails_false_countermodel (policy : List (Formula Atom)) (goal : Formula Atom)
    (budget : Nat) (found : entails policy goal budget = .ok false) :
    ∃ v, Reasoning.Models v policy ∧ ¬goal.Holds v := by
  unfold entails at found
  cases answer : countermodel? policy goal budget with
  | error message => simp [answer] at found
  | ok result =>
    cases result with
    | none => simp [answer] at found
    | some valuation => exact ⟨valuation, countermodel_sound policy goal budget valuation answer⟩

/-- A successful satisfiability result agrees with the exact logical semantics. -/
theorem satisfiable_correct (policy : List (Formula Atom)) (budget : Nat) (value : Bool)
    (found : satisfiable policy budget = .ok value) : Reasoning.satisfiable policy = value := by
  unfold satisfiable at found
  cases answer : solve policy budget with
  | error message => simp [answer] at found
  | ok result =>
    cases result with
    | none =>
      have none := solve_unsat_sound policy budget answer
      have falseResult : Reasoning.satisfiable policy = false := by
        cases old : Reasoning.satisfiable policy with
        | false => rfl
        | true =>
          obtain ⟨v, model⟩ := (Reasoning.satisfiable_iff _).mp old
          exact False.elim (none v model)
      have same : false = value := by simpa [answer] using found
      exact falseResult.trans same
    | some valuation =>
      have model := solve_model_sound policy budget valuation answer
      have trueResult := (Reasoning.satisfiable_iff policy).mpr ⟨valuation, model⟩
      have same : true = value := by simpa [answer] using found
      exact trueResult.trans same

/-- A successful entailment result agrees with exact finite propositional entailment. -/
theorem entails_correct (policy : List (Formula Atom)) (goal : Formula Atom) (budget : Nat)
    (value : Bool) (found : entails policy goal budget = .ok value) :
    Reasoning.entails policy goal = value := by
  cases value with
  | true => exact entails_sound policy goal budget found
  | false =>
    obtain ⟨v, model, falseGoal⟩ := entails_false_countermodel policy goal budget found
    cases old : Reasoning.entails policy goal with
    | false => rfl
    | true => exact False.elim (falseGoal ((Reasoning.entails_iff _ _).mp old v model))

end Netlib.Solver
