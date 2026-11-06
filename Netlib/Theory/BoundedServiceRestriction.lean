import Netlib.Theory.BoundedServiceCheck

/-!
# Service on an interval of one execution

Demand tags preserve the selected local demand.
Every service window stays inside the same recorded interval.
-/

namespace Netlib.Theory.BoundedServiceRestriction

open BoundedServiceCheck

universe u v w x

variable {Demand : Type u} {WholeDemand : Type v} {Action : Type w} {WholeAction : Type x}

theorem pending_some_iff (tag : Demand → WholeDemand)
    (injective : ∀ first second, tag first = tag second → first = second)
    {pending : Option Demand} {whole : Option WholeDemand} (same : whole = pending.map tag) (demand : Demand) :
    whole = some (tag demand) ↔ pending = some demand := by
  rw [same]
  cases pending with
  | none => constructor <;> intro impossible <;> cases impossible
  | some selected =>
    simp only [Option.map_some, Option.some.injEq]
    exact ⟨injective selected demand, congrArg tag⟩

variable {length offset count bound : Nat}
variable {pending : Nat → Option Demand} {wholePending : Nat → Option WholeDemand}
variable {action : Nat → Action} {wholeAction : Nat → WholeAction}
variable {serves : Demand → Action → Bool} {wholeServes : WholeDemand → WholeAction → Bool}

theorem restrict (service : Serviced length wholePending wholeAction wholeServes bound)
    (within : offset + count ≤ length) (tag : Demand → WholeDemand)
    (injective : ∀ first second, tag first = tag second → first = second) (actionTag : Action → WholeAction)
    (pendingEq : ∀ slot, slot ≤ count → wholePending (offset + slot) = (pending slot).map tag)
    (actionEq : ∀ slot, slot < count → wholeAction (offset + slot) = actionTag (action slot))
    (servesEq : ∀ demand event, wholeServes (tag demand) (actionTag event) = serves demand event) :
    Serviced count pending action serves bound := by
  intro start window demand selected persistent
  have selectedWhole : wholePending (offset + start) = some (tag demand) :=
    (pending_some_iff tag injective (pendingEq start (by omega)) demand).mpr selected
  have persistentWhole : ∀ inner, inner < bound → wholePending (offset + start + inner) = some (tag demand) := by
    intro inner inside
    rw [Nat.add_assoc]
    exact (pending_some_iff tag injective (pendingEq (start + inner) (by omega)) demand).mpr (persistent inner inside)
  obtain ⟨inner, inside, served⟩ := service (offset + start) (by omega) (tag demand) selectedWhole persistentWhole
  refine ⟨inner, inside, ?_⟩
  rw [Nat.add_assoc, actionEq (start + inner) (by omega), servesEq] at served
  exact served

variable {wholeAction : Nat → Action} {wholeServes : Demand → Action → Bool}

theorem subinterval (service : Serviced length pending wholeAction wholeServes bound)
    (within : offset + count ≤ length) :
    Serviced count (fun slot => pending (offset + slot)) (fun slot => wholeAction (offset + slot)) wholeServes bound := by
  exact restrict service within id (fun _ _ same => same) id
    (fun _ _ => by rw [Option.map_id]; rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem prefix_service (service : Serviced length pending action serves bound) (within : count ≤ length) :
    Serviced count pending action serves bound := by
  simpa only [Nat.zero_add] using subinterval (offset := 0) service (by omega : 0 + count ≤ length)

theorem suffix_service (service : Serviced length pending action serves bound) (within : offset ≤ length) :
    Serviced (length - offset) (fun slot => pending (offset + slot)) (fun slot => action (offset + slot)) serves bound :=
  subinterval service (by omega)

end Netlib.Theory.BoundedServiceRestriction
