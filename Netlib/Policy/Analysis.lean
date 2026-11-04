import Netlib.Policy.Language
import Netlib.Core.Reasoning

namespace Netlib.Analysis

def maxAtoms : Nat := 16

structure Gap where
  goal : Requirement
  countermodel : List (Observation × Bool)
  deriving Repr

structure Report where
  requirementCount : Nat
  goalCount : Nat
  atomCount : Nat
  consistent : Bool
  retained : List Requirement
  redundant : List Requirement
  conflict : List Requirement
  gaps : List Gap
  additions : Option (List Requirement)
  deriving Repr

private def formulas (requirements : List Requirement) : List (Formula Observation) :=
  requirements.map (·.formula)

/-- The algorithm keeps the background laws during each requirement removal. -/
private def prune (background : List (Formula Observation)) (kept : List Requirement) :
    List Requirement → List Requirement × List Requirement
  | [] => (kept, [])
  | r :: rs =>
    if Reasoning.entails (background ++ formulas (kept ++ rs)) r.formula then
      let result := prune background kept rs
      (result.1, r :: result.2)
    else prune background (kept ++ [r]) rs

private theorem prune_preserves (v : Observation → Bool)
    (background : List (Formula Observation)) (todo kept : List Requirement) :
    Reasoning.Models v (background ++ formulas (prune background kept todo).1) ↔
      Reasoning.Models v (background ++ formulas (kept ++ todo)) := by
  induction todo generalizing kept with
  | nil => simp [prune]
  | cons r rs ih =>
    simp only [prune]
    split
    next h =>
      dsimp only
      rw [ih]
      have hr := (Reasoning.entails_iff _ _).mp h v
      simp only [formulas, List.map_append, List.map_cons,
        Reasoning.models_append, Reasoning.models_cons] at hr ⊢
      constructor
      · rintro ⟨hb, hk, hs⟩
        exact ⟨hb, hk, hr ⟨hb, hk, hs⟩, hs⟩
      · rintro ⟨hb, hk, _, hs⟩
        exact ⟨hb, hk, hs⟩
    next _ =>
      rw [ih]
      simp [formulas, List.append_assoc]

def simplifyUnder (background : List (Formula Observation)) (requirements : List Requirement) :
    List Requirement × List Requirement :=
  prune background [] requirements

theorem simplifyUnder_preserves (v : Observation → Bool)
    (background : List (Formula Observation)) (requirements : List Requirement) :
    Reasoning.Models v (background ++ (simplifyUnder background requirements).1.map (·.formula)) ↔
      Reasoning.Models v (background ++ requirements.map (·.formula)) := by
  simpa [simplifyUnder, formulas] using prune_preserves v background requirements []

def analyze (requirements goals : List Requirement) : Except String Report := do
  let policy := formulas requirements
  let goalFormulas := formulas goals
  let observations := Reasoning.support (policy ++ goalFormulas)
  let background := Language.laws observations
  let atoms := Reasoning.support (background ++ policy ++ goalFormulas)
  if atoms.length > maxAtoms then
    throw (s!"offline analysis needs {atoms.length} distinct atoms including domain laws and goals; " ++
      s!"the exhaustive solver limit is {maxAtoms} (up to {2 ^ maxAtoms} assignments)")
  let base := background ++ policy
  let consistent := Reasoning.satisfiable base
  let (retained, redundant) := simplifyUnder background requirements
  let mut gaps := []
  if consistent then
    for goal in goals do
      if !Reasoning.entails base goal.formula then
        match Reasoning.countermodel? base goal.formula with
        | none => throw "internal error: missing entailment countermodel"
        | some v => gaps := gaps ++ [⟨goal, atoms.map (fun a => (a, v a))⟩]
  let additions :=
    if consistent && Reasoning.satisfiable (base ++ goalFormulas) then
      some (gaps.map (·.goal))
    else none
  return {
    requirementCount := requirements.length
    goalCount := goals.length
    atomCount := atoms.length
    consistent
    retained
    redundant
    conflict := if consistent then [] else retained
    gaps
    additions
  }

private def describe (r : Requirement) : String :=
  s!"{r.id} (line {r.line}): {r.text}"

private def ids (requirements : List Requirement) : String :=
  if requirements.isEmpty then "none"
  else String.intercalate ", " (requirements.map (·.id))

def render (report : Report) : String := Id.run do
  let mut lines := [
    s!"Requirements: {report.requirementCount}; goals: {report.goalCount}; " ++
      s!"distinct atoms: {report.atomCount}/{maxAtoms}",
    if report.consistent then "CONSISTENT in the propositional abstraction"
    else "INCONSISTENT in the propositional abstraction",
    "Assumes nonempty selectors; a satisfying assignment need not be a realizable network."]
  if !report.consistent then
    lines := lines ++ ["Conflicting requirements (deletion-minimal under fixed domain laws):"]
    lines := lines ++ report.conflict.map (fun r => "  " ++ describe r)
    lines := lines ++ ["Goal coverage and completion withheld because the policy is inconsistent."]
  else
    lines := lines ++ [s!"Redundant requirements under fixed domain laws: {ids report.redundant}",
      s!"Retained requirements: {ids report.retained}"]
    if report.goalCount == 0 then
      lines := lines ++ ["No security goals supplied; completeness was not assessed."]
    else
      lines := lines ++ [s!"Missing explicit goals: {report.gaps.length}"]
      for gap in report.gaps do
        lines := lines ++ ["  " ++ describe gap.goal,
          "  Abstract countermodel (not a concrete network):"]
        lines := lines ++ gap.countermodel.map
          (fun (atom, value) => s!"    {atom.render} = {value}")
      match report.additions with
      | none =>
        lines := lines ++ ["The supplied goals cannot all be added consistently."]
      | some [] =>
        lines := lines ++ ["All supplied goals are entailed; no additions are needed."]
      | some additions =>
        lines := lines ++ ["Proposed additions (supplied goals only; require human review):"]
        lines := lines ++ additions.map (fun r => "  " ++ describe r)
  return String.intercalate "\n" lines

end Netlib.Analysis
