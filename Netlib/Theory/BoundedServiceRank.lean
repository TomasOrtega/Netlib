import Netlib.Theory.BoundedServiceCheck

/-!
# Finite rank descent under persistent service

Each service window lies within the supplied finite prefix.
Equal positive rank retains the same current demand.
-/

namespace Netlib.Theory.BoundedServiceRank

universe u v

variable {Demand : Type u} {Action : Type v}
variable {length bound : Nat} {pending : Nat → Option Demand} {action : Nat → Action}
variable {serves : Demand → Action → Bool} {rank : Nat → Nat}

theorem rank_mono
    (nonincrease : ∀ slot, slot < length → rank (slot + 1) ≤ rank slot)
    {first last : Nat} (order : first ≤ last) (within : last ≤ length) : rank last ≤ rank first := by
  obtain ⟨count, rfl⟩ := Nat.exists_eq_add_of_le order
  induction count with
  | zero => simp
  | succ count ih =>
    have step := nonincrease (first + count) (by omega)
    exact Nat.le_trans step (ih (by omega) (by omega))

theorem block_decreases
    (service : BoundedServiceCheck.Serviced length pending action serves bound)
    (nonincrease : ∀ slot, slot < length → rank (slot + 1) ≤ rank slot)
    (demand : ∀ slot, slot ≤ length → 0 < rank slot → ∃ value, pending slot = some value)
    (persistent : ∀ slot, slot < length → 0 < rank slot → ∀ value, rank (slot + 1) = rank slot →
      pending slot = some value → pending (slot + 1) = some value)
    (strict : ∀ slot, slot < length → 0 < rank slot → ∀ value, pending slot = some value →
      serves value (action slot) = true → rank (slot + 1) < rank slot)
    (start : Nat) (within : start + bound ≤ length) (positive : 0 < rank start) :
    rank (start + bound) < rank start := by
  by_cases decreased : rank (start + bound) < rank start
  · exact decreased
  · have whole := rank_mono nonincrease (show start ≤ start + bound by omega) within
    have same : rank (start + bound) = rank start := by omega
    have equal : ∀ offset, offset ≤ bound → rank (start + offset) = rank start := by
      intro offset selected
      have lower := rank_mono nonincrease (show start + offset ≤ start + bound by omega) within
      have upper := rank_mono nonincrease (show start ≤ start + offset by omega) (by omega)
      omega
    obtain ⟨value, selected⟩ := demand start (by omega) positive
    have retained : ∀ offset, offset ≤ bound → pending (start + offset) = some value := by
      intro offset
      induction offset with
      | zero => simpa using selected
      | succ offset ih =>
        intro inside
        have previous := ih (by omega)
        have beforeEq := equal offset (by omega)
        have afterEq := equal (offset + 1) inside
        have next := persistent (start + offset) (by omega) (by omega) value
          (by simpa only [Nat.add_assoc] using afterEq.trans beforeEq.symm) previous
        simpa only [Nat.add_assoc] using next
    obtain ⟨offset, inside, served⟩ := service start within value selected
      (fun offset inside => retained offset (by omega))
    have beforeEq := equal offset (by omega)
    have decrease := strict (start + offset) (by omega) (by omega) value (retained offset (by omega)) served
    have afterEq := equal (offset + 1) (by omega)
    simp only [Nat.add_assoc] at decrease
    omega

theorem rank_after_blocks
    (service : BoundedServiceCheck.Serviced length pending action serves bound)
    (nonincrease : ∀ slot, slot < length → rank (slot + 1) ≤ rank slot)
    (demand : ∀ slot, slot ≤ length → 0 < rank slot → ∃ value, pending slot = some value)
    (persistent : ∀ slot, slot < length → 0 < rank slot → ∀ value, rank (slot + 1) = rank slot →
      pending slot = some value → pending (slot + 1) = some value)
    (strict : ∀ slot, slot < length → 0 < rank slot → ∀ value, pending slot = some value →
      serves value (action slot) = true → rank (slot + 1) < rank slot)
    (start blocks : Nat) (within : start + blocks * bound ≤ length) :
    rank (start + blocks * bound) ≤ rank start - blocks := by
  induction blocks with
  | zero => simp
  | succ blocks ih =>
    have index : start + (blocks + 1) * bound = start + blocks * bound + bound := by
      simp only [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
    rw [index] at within ⊢
    have previous := ih (by omega)
    have next := rank_mono nonincrease
      (show start + blocks * bound ≤ start + blocks * bound + bound by omega) within
    by_cases empty : rank (start + blocks * bound) = 0
    · omega
    · have positive : 0 < rank (start + blocks * bound) := by omega
      have decrease := block_decreases service nonincrease demand persistent strict
        (start + blocks * bound) within positive
      omega

theorem zero_by_at
    (service : BoundedServiceCheck.Serviced length pending action serves bound)
    (nonincrease : ∀ slot, slot < length → rank (slot + 1) ≤ rank slot)
    (demand : ∀ slot, slot ≤ length → 0 < rank slot → ∃ value, pending slot = some value)
    (persistent : ∀ slot, slot < length → 0 < rank slot → ∀ value, rank (slot + 1) = rank slot →
      pending slot = some value → pending (slot + 1) = some value)
    (strict : ∀ slot, slot < length → 0 < rank slot → ∀ value, pending slot = some value →
      serves value (action slot) = true → rank (slot + 1) < rank slot)
    (start : Nat) (within : start + rank start * bound ≤ length) :
    rank (start + rank start * bound) = 0 := by
  have reduced := rank_after_blocks service nonincrease demand persistent strict start (rank start) within
  omega

theorem zero_by
    (service : BoundedServiceCheck.Serviced length pending action serves bound)
    (nonincrease : ∀ slot, slot < length → rank (slot + 1) ≤ rank slot)
    (demand : ∀ slot, slot ≤ length → 0 < rank slot → ∃ value, pending slot = some value)
    (persistent : ∀ slot, slot < length → 0 < rank slot → ∀ value, rank (slot + 1) = rank slot →
      pending slot = some value → pending (slot + 1) = some value)
    (strict : ∀ slot, slot < length → 0 < rank slot → ∀ value, pending slot = some value →
      serves value (action slot) = true → rank (slot + 1) < rank slot)
    (within : rank 0 * bound ≤ length) : rank (rank 0 * bound) = 0 := by
  simpa only [Nat.zero_add] using zero_by_at service nonincrease demand persistent strict 0 (by simpa using within)

end Netlib.Theory.BoundedServiceRank
