import Netlib.Theory.BoundedServiceRestriction

/-!
# Array tables for the same finite service check

Exact stored callbacks retain the original service condition.
The pending table includes the endpoint slot for a zero bound.
-/

namespace Netlib.Theory.BoundedServiceTable

open BoundedServiceCheck

universe u v

variable {Demand : Type u} {Action : Type v}

def pendingAt (table : Array (Option Demand)) (slot : Nat) : Option Demand :=
  (table[slot]?).getD none

def actionAt (table : Array Action) (fallback : Action) (slot : Nat) : Action :=
  (table[slot]?).getD fallback

private theorem service_transfer {length bound : Nat}
    {priorPending pending : Nat → Option Demand} {priorAction action : Nat → Action} {serves : Demand → Action → Bool}
    (service : Serviced length priorPending priorAction serves bound)
    (pendingEq : ∀ slot, slot ≤ length → priorPending slot = pending slot)
    (actionEq : ∀ slot, slot < length → priorAction slot = action slot) :
    Serviced length pending action serves bound := by
  apply BoundedServiceRestriction.restrict service (offset := 0) (by omega) id (fun _ _ same => same) id
  · intro slot inside
    rw [Nat.zero_add, Option.map_id]
    exact pendingEq slot inside
  · intro slot inside
    simpa only [Nat.zero_add, id_eq] using actionEq slot inside
  · intro demand event
    rfl

variable [DecidableEq Demand]

def check (length : Nat) (pendingTable : Array (Option Demand)) (actionTable : Array Action)
    (fallback : Action) (serves : Demand → Action → Bool) (bound : Nat) : Bool :=
  BoundedServiceCheck.check length (pendingAt pendingTable) (actionAt actionTable fallback) serves bound

variable {length bound : Nat} {pendingTable : Array (Option Demand)} {actionTable : Array Action} {fallback : Action}
variable {pending : Nat → Option Demand} {action : Nat → Action} {serves : Demand → Action → Bool}

theorem check_correct
    (pendingEq : ∀ slot, slot ≤ length → (pendingTable[slot]?).getD none = pending slot)
    (actionEq : ∀ slot, slot < length → (actionTable[slot]?).getD fallback = action slot) :
    check length pendingTable actionTable fallback serves bound = true ↔ Serviced length pending action serves bound := by
  rw [check, BoundedServiceCheck.check_correct]
  exact ⟨fun service => service_transfer service pendingEq actionEq,
    fun service => service_transfer service (fun slot inside => (pendingEq slot inside).symm)
      (fun slot inside => (actionEq slot inside).symm)⟩

theorem check_eq
    (pendingEq : ∀ slot, slot ≤ length → (pendingTable[slot]?).getD none = pending slot)
    (actionEq : ∀ slot, slot < length → (actionTable[slot]?).getD fallback = action slot) :
    check length pendingTable actionTable fallback serves bound = BoundedServiceCheck.check length pending action serves bound := by
  have same := (check_correct (bound := bound) (serves := serves) pendingEq actionEq).trans
    (BoundedServiceCheck.check_correct length pending action serves bound).symm
  cases checked : check length pendingTable actionTable fallback serves bound <;>
    cases reference : BoundedServiceCheck.check length pending action serves bound <;> simp_all

end Netlib.Theory.BoundedServiceTable
