import Netlib.Standards.Basic
import Netlib.Core.Solver

namespace Netlib.Standards.Composition

universe u

/-- A supported clause separates applicability, feature selection, and its obligation. -/
structure Clause (Atom : Type u) where
  requirement : Requirement
  applicability : Formula Atom := .top
  feature : Formula Atom := .top
  condition : Option (Formula Atom)

namespace Clause

def guard (clause : Clause Atom) : Formula Atom :=
  .conj clause.applicability clause.feature

def Meaning (clause : Clause Atom) (valuation : Atom → Bool) : Prop :=
  clause.applicability.Holds valuation → clause.feature.Holds valuation →
    ∃ condition, clause.condition = some condition ∧ condition.Holds valuation

def formula (clause : Clause Atom) : Formula Atom :=
  .impl clause.guard (clause.condition.getD .bot)

theorem formula_correct (clause : Clause Atom) (valuation : Atom → Bool) :
    clause.formula.Holds valuation ↔ clause.Meaning valuation := by
  cases condition : clause.condition <;>
    simp [formula, guard, Meaning, Formula.Holds, condition]

def evaluate (clause : Clause Atom) (valuation : Atom → Bool) : Finding where
  requirement := clause.requirement
  status :=
    if clause.guard.eval valuation then
      match clause.condition with
      | none => .unsupported
      | some condition => if condition.eval valuation then .satisfied else .violated
    else .notApplicable
  evidence :=
    if clause.guard.eval valuation then
      match clause.condition with
      | none => ["The active clause has no formal condition."]
      | some condition =>
        if condition.eval valuation then ["The active formal condition holds."]
        else ["The active formal condition fails."]
    else ["The applicability or feature guard is false."]

@[simp] theorem evaluate_requirement (clause : Clause Atom) (valuation : Atom → Bool) :
    (clause.evaluate valuation).requirement = clause.requirement := rfl

theorem evaluate_passes_iff (clause : Clause Atom) (valuation : Atom → Bool) :
    (clause.evaluate valuation).status.passes = true ↔ clause.Meaning valuation := by
  rw [← formula_correct]
  change (clause.evaluate valuation).status.passes = true ↔
    (clause.guard.Holds valuation → (clause.condition.getD .bot).Holds valuation)
  rw [← Formula.eval_eq_true_iff valuation clause.guard]
  cases condition : clause.condition with
  | none =>
    cases active : clause.guard.eval valuation <;>
      simp [evaluate, active, condition, Status.passes, Formula.Holds]
  | some test =>
    cases active : clause.guard.eval valuation <;> cases result : test.eval valuation <;>
      simp [evaluate, active, condition, Status.passes, ← Formula.eval_eq_true_iff, result]

end Clause

structure Profile (Atom : Type u) where
  name : String
  clauses : List (Clause Atom)

namespace Profile

def Meaning (profile : Profile Atom) (valuation : Atom → Bool) : Prop :=
  ∀ clause ∈ profile.clauses, clause.Meaning valuation

def formula (profile : Profile Atom) : Formula Atom :=
  Solver.conjoin (profile.clauses.map Clause.formula)

theorem formula_correct (profile : Profile Atom) (valuation : Atom → Bool) :
    profile.formula.Holds valuation ↔ profile.Meaning valuation := by
  apply (Formula.eval_eq_true_iff valuation profile.formula).symm.trans
  apply (Solver.conjoin_correct (profile.clauses.map Clause.formula) valuation).trans
  constructor
  · intro model clause member
    exact (Clause.formula_correct _ _).mp
      (model clause.formula (List.mem_map.mpr ⟨clause, member, rfl⟩))
  · intro meaning condition member
    obtain ⟨clause, belongs, rfl⟩ := List.mem_map.mp member
    exact (Clause.formula_correct _ _).mpr (meaning clause belongs)

def compose (left right : Profile Atom) : Profile Atom where
  name := left.name ++ " + " ++ right.name
  clauses := left.clauses ++ right.clauses

theorem compose_meaning (left right : Profile Atom) (valuation : Atom → Bool) :
    (compose left right).Meaning valuation ↔ left.Meaning valuation ∧ right.Meaning valuation := by
  simp only [compose, Meaning, List.mem_append]
  constructor
  · intro both
    exact ⟨fun clause member => both clause (.inl member),
      fun clause member => both clause (.inr member)⟩
  · rintro ⟨left, right⟩ clause (member | member)
    · exact left clause member
    · exact right clause member

def requirements (profile : Profile Atom) : List Requirement :=
  profile.clauses.map Clause.requirement

def evaluate (profile : Profile Atom) (valuation : Atom → Bool) : Report where
  profile := profile.name
  findings := profile.clauses.map (·.evaluate valuation)

theorem evaluate_sources (profile : Profile Atom) (valuation : Atom → Bool) :
    ((profile.evaluate valuation).findings.map Finding.requirement) = profile.requirements := by
  simp [evaluate, requirements, List.map_map, Function.comp_def]

theorem evaluate_compliant_iff (profile : Profile Atom) (valuation : Atom → Bool) :
    (profile.evaluate valuation).compliant = true ↔
      profile.clauses ≠ [] ∧ profile.Meaning valuation := by
  change (!(profile.clauses.map (·.evaluate valuation)).isEmpty &&
    (profile.clauses.map (·.evaluate valuation)).all (fun finding => finding.status.passes)) = true ↔ _
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨nonempty, passing⟩
    refine ⟨?_, ?_⟩
    · intro empty
      simp [empty] at nonempty
    · intro clause member
      apply (Clause.evaluate_passes_iff _ _).mp
      exact (List.all_eq_true.mp passing) _ (List.mem_map.mpr ⟨clause, member, rfl⟩)
  · rintro ⟨nonempty, meaning⟩
    constructor
    · cases clauses : profile.clauses with
      | nil => exact False.elim (nonempty clauses)
      | cons clause rest => simp
    · apply List.all_eq_true.mpr
      intro finding member
      obtain ⟨clause, belongs, rfl⟩ := List.mem_map.mp member
      exact (Clause.evaluate_passes_iff _ _).mpr (meaning clause belongs)

end Profile

def Meaning (context : List (Formula Atom)) (profiles : List (Profile Atom))
    (valuation : Atom → Bool) : Prop :=
  Reasoning.Models valuation context ∧ ∀ profile ∈ profiles, profile.Meaning valuation

def formulas (context : List (Formula Atom)) (profiles : List (Profile Atom)) : List (Formula Atom) :=
  context ++ profiles.map Profile.formula

theorem formulas_correct (context : List (Formula Atom)) (profiles : List (Profile Atom))
    (valuation : Atom → Bool) :
    Reasoning.Models valuation (formulas context profiles) ↔ Meaning context profiles valuation := by
  unfold formulas Meaning
  rw [Reasoning.models_append]
  apply and_congr Iff.rfl
  constructor
  · intro model profile member
    exact (Profile.formula_correct _ _).mp
      (model profile.formula (List.mem_map.mpr ⟨profile, member, rfl⟩))
  · intro meaning condition member
    obtain ⟨profile, belongs, rfl⟩ := List.mem_map.mp member
    exact (Profile.formula_correct _ _).mpr (meaning profile belongs)

def requirements (profiles : List (Profile Atom)) : List Requirement :=
  profiles.flatMap Profile.requirements

def unsupported (profiles : List (Profile Atom)) : List Requirement :=
  profiles.flatMap fun profile =>
    (profile.clauses.filter (fun clause => clause.condition.isNone)).map Clause.requirement

inductive ErrorKind where
  | unsupported
  | resource
  deriving Repr, DecidableEq

structure Error where
  kind : ErrorKind
  message : String
  requirements : List Requirement
  deriving Repr

/-- Every completed result carries its justification for the original profiles. -/
inductive Compatibility (context : List (Formula Atom)) (profiles : List (Profile Atom)) where
  | compatible (valuation : Atom → Bool) (correct : Meaning context profiles valuation)
  | conflict (correct : ∀ valuation, ¬Meaning context profiles valuation)

namespace Compatibility

def isCompatible {context : List (Formula Atom)} {profiles : List (Profile Atom)} :
    Compatibility context profiles → Bool
  | .compatible _ _ => true
  | .conflict _ => false

def witness? {context : List (Formula Atom)} {profiles : List (Profile Atom)} :
    Compatibility context profiles → Option (Atom → Bool)
  | .compatible valuation _ => some valuation
  | .conflict _ => none

/-- Conflict sources describe the entire inconsistent set, without a minimality claim. -/
def sources {context : List (Formula Atom)} {profiles : List (Profile Atom)}
    (_result : Compatibility context profiles) : List Requirement := requirements profiles

def evidence {context : List (Formula Atom)} {profiles : List (Profile Atom)} :
    Compatibility context profiles → List Report
  | .compatible valuation _ => profiles.map (·.evaluate valuation)
  | .conflict _ => []

theorem witness_sound {context : List (Formula Atom)} {profiles : List (Profile Atom)}
    (result : Compatibility context profiles) (valuation : Atom → Bool)
    (found : result.witness? = some valuation) : Meaning context profiles valuation := by
  cases result with
  | compatible model correct =>
    cases found
    exact correct
  | conflict impossible => cases found

theorem conflict_sound {context : List (Formula Atom)} {profiles : List (Profile Atom)}
    (result : Compatibility context profiles) (failed : result.isCompatible = false) :
    ∀ valuation, ¬Meaning context profiles valuation := by
  cases result with
  | compatible model correct => cases failed
  | conflict impossible => exact impossible

@[simp] theorem sources_exact {context : List (Formula Atom)} {profiles : List (Profile Atom)}
    (result : Compatibility context profiles) : result.sources = requirements profiles := rfl

theorem evidence_sources {context : List (Formula Atom)} {profiles : List (Profile Atom)}
    (result : Compatibility context profiles) (valuation : Atom → Bool)
    (found : result.witness? = some valuation) :
    result.evidence.map (fun report => report.findings.map Finding.requirement) =
      profiles.map Profile.requirements := by
  cases result with
  | compatible model correct =>
    simp [evidence, List.map_map, Function.comp_def, Profile.evaluate_sources]
  | conflict impossible => cases found

end Compatibility

/-- Unsupported clauses and exhausted searches return errors with their source records. -/
def checkCompatibility [DecidableEq Atom] (context : List (Formula Atom))
    (profiles : List (Profile Atom)) (budget : Nat := 100000) :
    Except Error (Compatibility context profiles) :=
  if (unsupported profiles).isEmpty then
    match answer : Solver.solve (formulas context profiles) budget with
    | .error message => .error ⟨.resource, message, requirements profiles⟩
    | .ok none => .ok (.conflict (fun valuation meaning =>
        Solver.solve_unsat_sound _ _ answer valuation ((formulas_correct _ _ _).mpr meaning)))
    | .ok (some valuation) => .ok (.compatible valuation
        ((formulas_correct _ _ _).mp (Solver.solve_model_sound _ _ _ answer)))
  else .error ⟨.unsupported, "A clause has no formal condition.", unsupported profiles⟩

/-- A stronger version permits only models already permitted by the weaker version. -/
def Refines (context : List (Formula Atom)) (stronger weaker : Profile Atom) : Prop :=
  ∀ valuation, Reasoning.Models valuation context → stronger.Meaning valuation → weaker.Meaning valuation

theorem refines_refl (context : List (Formula Atom)) (profile : Profile Atom) :
    Refines context profile profile := fun _ _ => id

theorem refines_trans (context : List (Formula Atom)) (first second third : Profile Atom)
    (left : Refines context first second) (right : Refines context second third) :
    Refines context first third := fun valuation assumptions safe =>
  right valuation assumptions (left valuation assumptions safe)

inductive Refinement (context : List (Formula Atom)) (stronger weaker : Profile Atom) where
  | proved (correct : Refines context stronger weaker)
  | counterexample (valuation : Atom → Bool)
      (correct : Reasoning.Models valuation context ∧ stronger.Meaning valuation ∧ ¬weaker.Meaning valuation)

namespace Refinement

def isRefinement {context : List (Formula Atom)} {stronger weaker : Profile Atom} :
    Refinement context stronger weaker → Bool
  | .proved _ => true
  | .counterexample _ _ => false

def witness? {context : List (Formula Atom)} {stronger weaker : Profile Atom} :
    Refinement context stronger weaker → Option (Atom → Bool)
  | .proved _ => none
  | .counterexample valuation _ => some valuation

def sources {context : List (Formula Atom)} {stronger weaker : Profile Atom}
    (_result : Refinement context stronger weaker) : List Requirement :=
  stronger.requirements ++ weaker.requirements

def evidence {context : List (Formula Atom)} {stronger weaker : Profile Atom} :
    Refinement context stronger weaker → List Report
  | .proved _ => []
  | .counterexample valuation _ => [stronger.evaluate valuation, weaker.evaluate valuation]

@[simp] theorem sources_exact {context : List (Formula Atom)} {stronger weaker : Profile Atom}
    (result : Refinement context stronger weaker) :
    result.sources = stronger.requirements ++ weaker.requirements := rfl

theorem witness_sound {context : List (Formula Atom)} {stronger weaker : Profile Atom}
    (result : Refinement context stronger weaker) (valuation : Atom → Bool)
    (found : result.witness? = some valuation) :
    Reasoning.Models valuation context ∧ stronger.Meaning valuation ∧ ¬weaker.Meaning valuation := by
  cases result with
  | proved correct => cases found
  | counterexample model correct => cases found; exact correct

theorem proved_sound {context : List (Formula Atom)} {stronger weaker : Profile Atom}
    (result : Refinement context stronger weaker) (accepted : result.isRefinement = true) :
    Refines context stronger weaker := by
  cases result with
  | proved correct => exact correct
  | counterexample model correct => cases accepted

end Refinement

def checkRefinement [DecidableEq Atom] (context : List (Formula Atom))
    (stronger weaker : Profile Atom) (budget : Nat := 100000) :
    Except Error (Refinement context stronger weaker) :=
  if (unsupported [stronger, weaker]).isEmpty then
    match answer : Solver.countermodel? (context ++ [stronger.formula]) weaker.formula budget with
    | .error message => .error ⟨.resource, message, requirements [stronger, weaker]⟩
    | .ok none => .ok (.proved (by
        intro valuation assumptions safe
        apply Classical.byContradiction
        intro fails
        apply Solver.solve_unsat_sound
          ((context ++ [stronger.formula]) ++ [.neg weaker.formula]) budget
          (by simpa only [Solver.countermodel?] using answer) valuation
        simp only [Reasoning.models_append, Reasoning.models_cons, Reasoning.models_nil,
          and_true, Formula.Holds]
        exact ⟨⟨assumptions, (Profile.formula_correct _ _).mpr safe⟩,
          fun holds => fails ((Profile.formula_correct _ _).mp holds)⟩))
    | .ok (some valuation) => .ok (.counterexample valuation (by
        have result := Solver.countermodel_sound _ _ _ _ answer
        have first := (Reasoning.models_append _ _ _).mp result.1
        refine ⟨first.1, ?_, ?_⟩
        · exact (Profile.formula_correct _ _).mp ((Reasoning.models_cons _ _ _).mp first.2).1
        · exact fun holds => result.2 ((Profile.formula_correct _ _).mpr holds)))
  else .error ⟨.unsupported, "A clause has no formal condition.", unsupported [stronger, weaker]⟩

end Netlib.Standards.Composition
