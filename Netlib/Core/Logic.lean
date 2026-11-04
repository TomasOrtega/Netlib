import Std

namespace Netlib

/-- A requirements language independent of any particular network model. -/
inductive Formula (Atom : Type u) where
  | atom : Atom → Formula Atom
  | top : Formula Atom
  | bot : Formula Atom
  | neg : Formula Atom → Formula Atom
  | conj : Formula Atom → Formula Atom → Formula Atom
  | disj : Formula Atom → Formula Atom → Formula Atom
  | impl : Formula Atom → Formula Atom → Formula Atom
  deriving Repr, DecidableEq

namespace Formula

def eval (v : Atom → Bool) : Formula Atom → Bool
  | .atom a => v a
  | .top => true
  | .bot => false
  | .neg p => !eval v p
  | .conj p q => eval v p && eval v q
  | .disj p q => eval v p || eval v q
  | .impl p q => !eval v p || eval v q

def Holds (v : Atom → Bool) : Formula Atom → Prop
  | .atom a => v a = true
  | .top => True
  | .bot => False
  | .neg p => ¬Holds v p
  | .conj p q => Holds v p ∧ Holds v q
  | .disj p q => Holds v p ∨ Holds v q
  | .impl p q => Holds v p → Holds v q

@[simp] theorem eval_eq_true_iff (v : Atom → Bool) (f : Formula Atom) :
    eval v f = true ↔ Holds v f := by
  induction f with
  | atom a => rfl
  | top => simp [eval, Holds]
  | bot => simp [eval, Holds]
  | neg p ih => simp [eval, Holds, ← ih]
  | conj p q ihp ihq => simp [eval, Holds, ihp, ihq]
  | disj p q ihp ihq => simp [eval, Holds, ihp, ihq]
  | impl p q ihp ihq =>
    simp only [eval, Bool.or_eq_true, Bool.not_eq_true', Holds, ← ihp, ← ihq]
    cases eval v p <;> simp

def atoms : Formula Atom → List Atom
  | .atom a => [a]
  | .top | .bot => []
  | .neg p => atoms p
  | .conj p q | .disj p q | .impl p q => atoms p ++ atoms q

/-- Atom renaming also serves as compilation into another interpretation. -/
def map (f : Atom → Other) : Formula Atom → Formula Other
  | .atom a => .atom (f a)
  | .top => .top
  | .bot => .bot
  | .neg p => .neg (map f p)
  | .conj p q => .conj (map f p) (map f q)
  | .disj p q => .disj (map f p) (map f q)
  | .impl p q => .impl (map f p) (map f q)

@[simp] theorem eval_map (f : Atom → Other) (v : Other → Bool) (p : Formula Atom) :
    (p.map f).eval v = p.eval (v ∘ f) := by
  induction p <;> simp_all [map, eval]

theorem eval_eq_of_agree (p : Formula Atom) (v w : Atom → Bool)
    (h : ∀ a ∈ p.atoms, v a = w a) : p.eval v = p.eval w := by
  induction p with
  | atom a => exact h a (by simp [atoms])
  | top => rfl
  | bot => rfl
  | neg p ih => simp [eval, ih h]
  | conj p q ihp ihq =>
    simp only [eval]
    rw [ihp (fun a ha => h a (by simp [atoms, ha])),
      ihq (fun a ha => h a (by simp [atoms, ha]))]
  | disj p q ihp ihq =>
    simp only [eval]
    rw [ihp (fun a ha => h a (by simp [atoms, ha])),
      ihq (fun a ha => h a (by simp [atoms, ha]))]
  | impl p q ihp ihq =>
    simp only [eval]
    rw [ihp (fun a ha => h a (by simp [atoms, ha])),
      ihq (fun a ha => h a (by simp [atoms, ha]))]

theorem holds_map (f : Atom → Other) (v : Other → Bool) (p : Formula Atom) :
    (p.map f).Holds v ↔ p.Holds (v ∘ f) := by
  rw [← eval_eq_true_iff, ← eval_eq_true_iff, eval_map]

end Formula
end Netlib
