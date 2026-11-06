import Netlib.Theory.BoundedProgress

/-!
# Finite checks for persistent-demand service

The input functions read demands and actions at stored slots.
The check uses only slots within the supplied finite length.
-/

namespace Netlib.Theory.BoundedServiceCheck

universe u v

variable {Demand : Type u} {Action : Type v} [DecidableEq Demand]

def Serviced (length : Nat) (pending : Nat → Option Demand) (action : Nat → Action)
    (serves : Demand → Action → Bool) (bound : Nat) : Prop :=
  ∀ start, start + bound ≤ length → ∀ demand,
    pending start = some demand →
    (∀ offset, offset < bound → pending (start + offset) = some demand) →
    ∃ offset, offset < bound ∧ serves demand (action (start + offset)) = true

def check (length : Nat) (pending : Nat → Option Demand) (action : Nat → Action)
    (serves : Demand → Action → Bool) (bound : Nat) : Bool :=
  (List.range (length + 1)).all fun start =>
    if start + bound ≤ length then
      match pending start with
      | none => true
      | some demand =>
        if (List.range bound).all (fun offset => decide (pending (start + offset) = some demand)) then
          (List.range bound).any (fun offset => serves demand (action (start + offset)))
        else true
    else true

theorem check_correct (length : Nat) (pending : Nat → Option Demand) (action : Nat → Action)
    (serves : Demand → Action → Bool) (bound : Nat) :
    check length pending action serves bound = true ↔ Serviced length pending action serves bound := by
  constructor
  · intro checked start within demand selected persistent
    have member : start ∈ List.range (length + 1) := List.mem_range.mpr (by omega)
    have value := List.all_eq_true.mp checked start member
    have retained : (List.range bound).all (fun offset => decide (pending (start + offset) = some demand)) = true := by
      apply List.all_eq_true.mpr
      intro offset inside
      exact decide_eq_true (persistent offset (List.mem_range.mp inside))
    simp only [within, ↓reduceIte, selected, retained] at value
    obtain ⟨offset, inside, served⟩ := List.any_eq_true.mp value
    exact ⟨offset, List.mem_range.mp inside, served⟩
  · intro serviced
    apply List.all_eq_true.mpr
    intro start member
    by_cases within : start + bound ≤ length
    · simp only [within, ↓reduceIte]
      cases selected : pending start with
      | none => rfl
      | some demand =>
        simp only
        split
        · rename_i retained
          have persistent : ∀ offset, offset < bound → pending (start + offset) = some demand := by
            intro offset inside
            exact of_decide_eq_true (List.all_eq_true.mp retained offset (List.mem_range.mpr inside))
          obtain ⟨offset, inside, served⟩ := serviced start within demand selected persistent
          exact List.any_eq_true.mpr ⟨offset, List.mem_range.mpr inside, served⟩
        · rfl
    · simp only [within, ↓reduceIte]

end Netlib.Theory.BoundedServiceCheck
