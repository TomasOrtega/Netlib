import Netlib.Theory.BoundedServiceCheck

/-!
# A selected class of demands from one service check

The larger execution can have other demands when the local demand is absent.
Every local persistent demand retains its actual service window.
-/

namespace Netlib.Theory.BoundedServiceProjection

open BoundedServiceCheck

universe u v w x

variable {Demand : Type u} {WholeDemand : Type v} {Action : Type w} {WholeAction : Type x}
variable {length offset count bound : Nat}
variable {pending : Nat → Option Demand} {wholePending : Nat → Option WholeDemand}
variable {action : Nat → Action} {wholeAction : Nat → WholeAction}
variable {serves : Demand → Action → Bool} {wholeServes : WholeDemand → WholeAction → Bool}

theorem restrict (service : Serviced length wholePending wholeAction wholeServes bound)
    (within : offset + count ≤ length) (tag : Demand → WholeDemand) (actionTag : Action → WholeAction)
    (selected : ∀ slot, slot ≤ count → ∀ demand, pending slot = some demand →
      wholePending (offset + slot) = some (tag demand))
    (actionEq : ∀ slot, slot < count → wholeAction (offset + slot) = actionTag (action slot))
    (servesEq : ∀ demand event, wholeServes (tag demand) (actionTag event) = serves demand event) :
    Serviced count pending action serves bound := by
  intro start window demand present persistent
  have presentWhole := selected start (by omega) demand present
  have persistentWhole : ∀ inner, inner < bound →
      wholePending (offset + start + inner) = some (tag demand) := by
    intro inner inside
    rw [Nat.add_assoc]
    exact selected (start + inner) (by omega) demand (persistent inner inside)
  obtain ⟨inner, inside, served⟩ := service (offset + start) (by omega) (tag demand) presentWhole persistentWhole
  refine ⟨inner, inside, ?_⟩
  rw [Nat.add_assoc, actionEq (start + inner) (by omega), servesEq] at served
  exact served

variable {wholeServes : WholeDemand → Action → Bool}

theorem project (service : Serviced length wholePending action wholeServes bound)
    (tag : Demand → WholeDemand)
    (selected : ∀ slot, slot ≤ length → ∀ demand, pending slot = some demand →
      wholePending slot = some (tag demand))
    (servesEq : ∀ demand event, wholeServes (tag demand) event = serves demand event) :
    Serviced length pending action serves bound := by
  apply restrict (offset := 0) service (by omega) tag id
  · intro slot within demand present
    simpa only [Nat.zero_add] using selected slot within demand present
  · intro slot _
    simp only [Nat.zero_add, id_eq]
  · exact servesEq

end Netlib.Theory.BoundedServiceProjection
