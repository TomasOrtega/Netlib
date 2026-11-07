import Std

/-!
# Complete finite products

The empty product has one member. Its count can be checked before allocating
any tuples, and membership retains the choice at each position.
-/

namespace Netlib.Theory.FiniteProduct

universe u

variable {α : Type u}

def tuples : List (List α) → List (List α)
  | [] => [[]]
  | choices :: rest => choices.flatMap fun value => (tuples rest).map (value :: ·)

def count : List (List α) → Nat
  | [] => 1
  | choices :: rest => choices.length * count rest

def Matches : List (List α) → List α → Prop
  | [], [] => True
  | choices :: rest, value :: tail => value ∈ choices ∧ Matches rest tail
  | _, _ => False

theorem mem_tuples (choices : List (List α)) (values : List α) :
    values ∈ tuples choices ↔ Matches choices values := by
  induction choices generalizing values with
  | nil => cases values <;> simp [tuples, Matches]
  | cons head rest ih =>
    cases values with
    | nil => simp [tuples, Matches]
    | cons value tail => simp [tuples, Matches, ih]

private theorem extend_length (choices : List α) (tails : List (List α)) :
    (choices.flatMap fun value => tails.map (value :: ·)).length = choices.length * tails.length := by
  induction choices with
  | nil => simp
  | cons value rest ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons, ih]
    simp [Nat.add_mul, Nat.add_comm]

theorem tuples_length (choices : List (List α)) : (tuples choices).length = count choices := by
  induction choices with
  | nil => rfl
  | cons head rest ih => simp only [tuples, count, extend_length, ih]

theorem Matches.length {choices : List (List α)} {values : List α} (matched : Matches choices values) :
    values.length = choices.length := by
  induction choices generalizing values with
  | nil => cases values <;> simp_all [Matches]
  | cons head rest ih =>
    cases values with
    | nil => cases matched
    | cons value tail => exact congrArg Nat.succ (ih matched.2)

theorem Matches.getElem {choices : List (List α)} {values : List α} (matched : Matches choices values)
    (index : Nat) (left : index < choices.length) (right : index < values.length) :
    values[index] ∈ choices[index] := by
  induction choices generalizing values index with
  | nil => simp at left
  | cons head rest ih =>
    cases values with
    | nil => cases matched
    | cons value tail =>
      cases index with
      | zero => exact matched.1
      | succ index =>
        exact ih matched.2 index
          (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using left)
          (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using right)

theorem matches_of_getElem {choices : List (List α)} {values : List α}
    (same : values.length = choices.length)
    (selected : ∀ index (left : index < choices.length) (right : index < values.length), values[index] ∈ choices[index]) :
    Matches choices values := by
  induction choices generalizing values with
  | nil => cases values <;> simp_all [Matches]
  | cons head rest ih =>
    cases values with
    | nil => simp at same
    | cons value tail =>
      exact ⟨selected 0 (by simp) (by simp), ih (by simpa using same)
        (fun index left right => selected (index + 1)
          (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using left)
          (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using right))⟩

def vector (values : List α) (same : values.length = size) : Vector α size :=
  ⟨values.toArray, by simpa using same⟩

@[simp] theorem vector_toList (values : List α) (same : values.length = size) :
    (vector values same).toList = values := by simp [vector]

@[simp] theorem vector_get (values : List α) (same : values.length = size) (index : Fin size) :
    (vector values same).get index = values[index.val]'(by omega) := by
  simp [vector, Vector.get, Fin.cast]

end Netlib.Theory.FiniteProduct
