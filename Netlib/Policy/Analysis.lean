import Netlib.Policy.Language
import Netlib.Core.Reasoning
import Netlib.Core.Solver

namespace Netlib.Analysis

structure Gap where
  goal : Requirement
  countermodel : List (Observation × Bool)
  deriving Repr

structure Report where
  requirementCount : Nat
  goalCount : Nat
  atomCount : Nat
  searchBudget : Nat
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

/-- The result carries a proof under the fixed background laws. -/
structure Reduction (background : List (Formula Observation)) (original : List Requirement) where
  retained : List Requirement
  redundant : List Requirement
  correct : ∀ v, Reasoning.Models v (background ++ retained.map (·.formula)) ↔
    Reasoning.Models v (background ++ original.map (·.formula))

private theorem drop_entailed (background : List (Formula Observation))
    (kept rest : List Requirement) (r : Requirement)
    (entailed : Reasoning.entails (background ++ formulas (kept ++ rest)) r.formula = true)
    (v : Observation → Bool) :
    Reasoning.Models v (background ++ formulas (kept ++ rest)) ↔
      Reasoning.Models v (background ++ formulas (kept ++ r :: rest)) := by
  have hr := (Reasoning.entails_iff _ _).mp entailed v
  simp only [formulas, List.map_append, List.map_cons,
    Reasoning.models_append, Reasoning.models_cons] at hr ⊢
  constructor
  · rintro ⟨hb, hk, hs⟩
    exact ⟨hb, hk, hr ⟨hb, hk, hs⟩, hs⟩
  · rintro ⟨hb, hk, _, hs⟩
    exact ⟨hb, hk, hs⟩

private def pruneFast (background : List (Formula Observation)) (budget : Nat)
    (kept : List Requirement) :
    (todo : List Requirement) → Except String (Reduction background (kept ++ todo))
  | [] => .ok {
      retained := kept
      redundant := []
      correct := fun _ => by simp
    }
  | r :: rest =>
    match checked : Solver.entails (background ++ formulas (kept ++ rest)) r.formula budget with
    | .error message => .error s!"Requirement {r.id}: {message}"
    | .ok true => do
      let reduced ← pruneFast background budget kept rest
      return {
        retained := reduced.retained
        redundant := r :: reduced.redundant
        correct := fun v => (reduced.correct v).trans
          (drop_entailed background kept rest r (Solver.entails_sound _ _ _ checked) v)
      }
    | .ok false => do
      let reduced ← pruneFast background budget (kept ++ [r]) rest
      return {
        retained := reduced.retained
        redundant := reduced.redundant
        correct := fun v => by
          simpa [List.append_assoc] using reduced.correct v
      }

/-- Each deletion uses a proved solver answer. An exhausted search returns an error. -/
def simplifyUnderFast (background : List (Formula Observation))
    (requirements : List Requirement) (budget : Nat := 100000) :
    Except String (Reduction background requirements) := do
  let reduced ← pruneFast background budget [] requirements
  return {
    retained := reduced.retained
    redundant := reduced.redundant
    correct := fun v => by simpa using reduced.correct v
  }

def analyze (requirements goals : List Requirement) (budget : Nat := 100000) :
    Except String Report := do
  let policy := formulas requirements
  let goalFormulas := formulas goals
  let observations := Reasoning.support (policy ++ goalFormulas)
  let background := Language.laws observations
  let atoms := Reasoning.support (background ++ policy ++ goalFormulas)
  let base := background ++ policy
  let consistent ← (Solver.satisfiable base budget).mapError
    (fun message => "Consistency check: " ++ message)
  let reduced ← simplifyUnderFast background requirements budget
  let candidates ← if consistent then goals.mapM (fun goal => do
    match ← Solver.countermodel? base goal.formula budget with
    | none => pure none
    | some valuation => pure (some (⟨goal, atoms.map (fun a => (a, valuation a))⟩ : Gap)))
    else pure []
  let gaps := candidates.filterMap id
  let jointConsistent ← if consistent then Solver.satisfiable (base ++ goalFormulas) budget
    else pure false
  let additions := if jointConsistent then some (gaps.map (·.goal)) else none
  return {
    requirementCount := requirements.length
    goalCount := goals.length
    atomCount := atoms.length
    searchBudget := budget
    consistent
    retained := reduced.retained
    redundant := reduced.redundant
    conflict := if consistent then [] else reduced.retained
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
    s!"Requirements: {report.requirementCount}. Goals: {report.goalCount}. " ++
      s!"Distinct atoms: {report.atomCount}. Search node budget per query: {report.searchBudget}.",
    if report.consistent then "CONSISTENT in the propositional abstraction"
    else "INCONSISTENT in the propositional abstraction",
    "Each selector must contain a device. An abstract model can have no matching network."]
  if !report.consistent then
    lines := lines ++ ["Conflicting requirements (deletion-minimal under fixed domain laws):"]
    lines := lines ++ report.conflict.map (fun r => "  " ++ describe r)
    lines := lines ++ ["The policy is inconsistent. The checker does not assess its goals."]
  else
    lines := lines ++ [s!"Redundant requirements under fixed domain laws: {ids report.redundant}",
      s!"Retained requirements: {ids report.retained}"]
    if report.goalCount == 0 then
      lines := lines ++ ["The input has no security goals. The checker did not assess completeness."]
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
        lines := lines ++ ["The requirements imply all supplied goals. No additions are necessary."]
      | some additions =>
        lines := lines ++ ["Proposed source goals. Review each addition:"]
        lines := lines ++ additions.map (fun r => "  " ++ describe r)
  return String.intercalate "\n" lines

end Netlib.Analysis
