import Netlib.Network.Basic

namespace Netlib.Certificate

variable {Node : Type u} [DecidableEq Node]

/-- Only declared nodes can participate in a forwarding step. -/
def finiteNetwork (nodes : List Node) (edge : Node → Node → Bool) : Network Node :=
  ⟨fun a b => a ∈ nodes ∧ b ∈ nodes ∧ edge a b = true⟩

/-- A complete vertex trace, including both endpoints. -/
def validPath (nodes : List Node) (edge : Node → Node → Bool)
    (source target : Node) : List Node → Bool
  | [] => false
  | [a] => decide (a = source) && decide (a = target) && decide (a ∈ nodes)
  | a :: b :: rest =>
      decide (a = source) && decide (a ∈ nodes) && decide (b ∈ nodes) &&
        edge a b && validPath nodes edge b target (b :: rest)

theorem validPath_sound (nodes : List Node) (edge : Node → Node → Bool)
    (source target : Node) (trace : List Node)
    (valid : validPath nodes edge source target trace = true) :
    Network.Reachable (finiteNetwork nodes edge) source target := by
  induction trace generalizing source with
  | nil => simp [validPath] at valid
  | cons a tail ih =>
    cases tail with
    | nil =>
      simp only [validPath, Bool.and_eq_true, decide_eq_true_eq] at valid
      rcases valid with ⟨⟨rfl, rfl⟩, _⟩
      exact .refl a
    | cons b rest =>
      simp only [validPath, Bool.and_eq_true, decide_eq_true_eq] at valid
      rcases valid with ⟨⟨⟨⟨rfl, aNode⟩, bNode⟩, link⟩, suffix⟩
      exact .step ⟨aNode, bNode, link⟩ (ih b suffix)

/-- A forward-closed cut separates the requested endpoints. -/
def validCut (nodes : List Node) (edge : Node → Node → Bool)
    (source target : Node) (region : List Node) : Bool :=
  decide (source ∈ region) && decide (target ∉ region) &&
    region.all (fun a => nodes.all (fun b => !edge a b || decide (b ∈ region)))

theorem validCut_sound (nodes : List Node) (edge : Node → Node → Bool)
    (source target : Node) (region : List Node)
    (valid : validCut nodes edge source target region = true) :
    ¬Network.Reachable (finiteNetwork nodes edge) source target := by
  simp only [validCut, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at valid
  obtain ⟨⟨sourceInside, targetOutside⟩, closed⟩ := valid
  have preserve : ∀ {a b}, Network.Reachable (finiteNetwork nodes edge) a b →
      a ∈ region → b ∈ region := by
    intro a b path
    induction path with
    | refl => exact id
    | @step a b c link _ ih =>
      intro aInside
      apply ih
      have closure := closed a aInside b link.2.1
      simpa [link.2.2] using closure
  intro path
  exact targetOutside (preserve path sourceInside)

end Netlib.Certificate
