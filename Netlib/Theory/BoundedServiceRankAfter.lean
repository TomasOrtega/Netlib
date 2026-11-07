import Netlib.Theory.BoundedServiceRank

/-!
# Finite rank descent at a later recorded slot

A coarse deadline can exceed the exact current rank budget.
All service windows and later slots stay within the supplied prefix.
-/

namespace Netlib.Theory.BoundedServiceRank

universe u v

variable {Demand : Type u} {Action : Type v}
variable {length bound : Nat} {pending : Nat → Option Demand} {action : Nat → Action}
variable {serves : Demand → Action → Bool} {rank : Nat → Nat}

theorem zero_after_at
    (service : BoundedServiceCheck.Serviced length pending action serves bound)
    (nonincrease : ∀ slot, slot < length → rank (slot + 1) ≤ rank slot)
    (demand : ∀ slot, slot ≤ length → 0 < rank slot → ∃ value, pending slot = some value)
    (persistent : ∀ slot, slot < length → 0 < rank slot → ∀ value, rank (slot + 1) = rank slot →
      pending slot = some value → pending (slot + 1) = some value)
    (strict : ∀ slot, slot < length → 0 < rank slot → ∀ value, pending slot = some value →
      serves value (action slot) = true → rank (slot + 1) < rank slot)
    (start last : Nat) (order : start + rank start * bound ≤ last) (within : last ≤ length) :
    rank last = 0 := by
  have zero := zero_by_at service nonincrease demand persistent strict start (Nat.le_trans order within)
  have later := rank_mono nonincrease order within
  omega

theorem zero_after
    (service : BoundedServiceCheck.Serviced length pending action serves bound)
    (nonincrease : ∀ slot, slot < length → rank (slot + 1) ≤ rank slot)
    (demand : ∀ slot, slot ≤ length → 0 < rank slot → ∃ value, pending slot = some value)
    (persistent : ∀ slot, slot < length → 0 < rank slot → ∀ value, rank (slot + 1) = rank slot →
      pending slot = some value → pending (slot + 1) = some value)
    (strict : ∀ slot, slot < length → 0 < rank slot → ∀ value, pending slot = some value →
      serves value (action slot) = true → rank (slot + 1) < rank slot)
    (last : Nat) (order : rank 0 * bound ≤ last) (within : last ≤ length) : rank last = 0 := by
  exact zero_after_at service nonincrease demand persistent strict 0 last (by simpa only [Nat.zero_add] using order) within

end Netlib.Theory.BoundedServiceRank
