import Netlib.Check.CampusTCPRevocationControl
import Netlib.Check.CampusTCPTwoProgressReceiptFrames
import Netlib.Theory.BoundedServiceRank

/-!
# Bounded resolution of the actual TCP link frontier

The same stored service condition resolves each pending receiver-link identity.
Ingress responses and work tickets need not become empty.
-/

namespace Netlib.Check.CampusTCPRevocationDrainBound

open CampusTCPModel

namespace C
export CampusTCPRevocationCustody (frontier potential first_link first_pending isLink)
end C
namespace M
export CampusTCPRevocationMonitor (Installation observe monitorAt nextDemand)
end M
namespace D
export CampusTCPRevocationControl (Demand linkDemand pending pendingAt serves service)
end D
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

variable {input : Input} {initial final : State input}
variable {events remaining : List Event} {steps : List (Step input)}

private theorem observe_nil (names : M.Installation → String) (event : Event) :
    M.observe names [] event = [] := by
  unfold CampusTCPRevocationMonitor.observe
  split <;> rfl

theorem monitorAt_nil (names : M.Installation → String) (steps : List (Step input)) (slot : Nat) :
    M.monitorAt names [] steps slot = [] := by
  induction steps generalizing slot with
  | nil => rfl
  | cons actual rest ih =>
    cases slot with
    | zero => rfl
    | succ slot => simpa only [M.monitorAt, observe_nil] using ih slot

theorem pendingAt_drain (names : M.Installation → String) (initial : State input)
    (steps : List (Step input)) (slot : Nat) :
    D.pendingAt names initial [] steps slot =
      (C.frontier (S.stateAt initial steps slot)).head?.bind D.linkDemand := by
  simp only [D.pendingAt, D.pending, monitorAt_nil, M.nextDemand, List.head?_nil]

theorem demand_exists (state : State input) (positive : 0 < C.potential state) :
    ∃ demand, (C.frontier state).head?.bind D.linkDemand = some demand := by
  cases selected : (C.frontier state).head? with
  | none =>
    have empty := List.head?_eq_none_iff.mp selected
    rw [CampusTCPRevocationCustody.potential_length, empty] at positive
    cases Nat.not_lt_zero _ positive
  | some item =>
    obtain ⟨index, served, emission, emitted, payload, _⟩ := C.first_link state item selected
    exact ⟨.resolveLink item.id index emission.bytes,
      by simp only [Option.bind_some, D.linkDemand, payload]⟩

theorem served_strict (names : M.Installation → String) (actual : Step input)
    (history : Theory.PacketCustody.History actual.before.custody)
    (denied : ∀ served, actual.result.service = some served → served.evidence.output = none)
    (demand : D.Demand) (selected : (C.frontier actual.before).head?.bind D.linkDemand = some demand)
    (served : D.serves names demand actual.event = true) :
    C.potential actual.result.state < C.potential actual.before := by
  cases head : (C.frontier actual.before).head? with
  | none => simp only [head, Option.bind_none, reduceCtorEq] at selected
  | some item =>
    obtain ⟨index, service, emission, emitted, payload, _⟩ := C.first_link actual.before item head
    have selectedDemand : (.resolveLink item.id index emission.bytes : D.Demand) = demand := by
      simpa only [head, Option.bind_some, D.linkDemand, payload, Option.some.injEq] using selected
    subst demand
    cases event : actual.event <;> simp only [event, D.serves, Bool.false_eq_true] at served
    · rename_i actualIndex bytes policy
      exact CampusTCPRevocationCustody.Step.deliver_strict actual history actualIndex bytes policy event denied
    · rename_i actualID
      have idEq : actualID = item.id := of_decide_eq_true served
      obtain ⟨resolved, _, after⟩ := CampusTCPCustodyFacts.Step.drop actual actualID event
      have pending := C.first_pending actual.before item head
      have exactItem : resolved.item = item := resolved.item_eq history.valid item pending idEq.symm
      have matching : C.isLink resolved.item.value.payload = true := by rw [exactItem, payload]; rfl
      change actual.result.state.custody.frontierCount C.isLink < actual.before.custody.frontierCount C.isLink
      rw [after]
      exact resolved.frontierCount_strict C.isLink matching

theorem drain_by (names : M.Installation → String)
    (trace : Trace input initial events steps final remaining)
    (history : Theory.PacketCustody.History initial.custody)
    (nocopy : ∀ actual ∈ steps, ∀ id, actual.event ≠ .copyPacket id)
    (denied : ∀ actual ∈ steps, ∀ served,
      actual.result.service = some served → served.evidence.output = none)
    (bound : Nat) (checked : D.service names initial [] steps bound = true)
    (enough : C.potential initial * bound ≤ steps.length) :
    C.frontier (S.stateAt initial steps (C.potential initial * bound)) = [] := by
  let rank := fun slot => C.potential (S.stateAt initial steps slot)
  have serviced := (Theory.BoundedServiceCheck.check_correct _ _ _ _ _).mp checked
  have nonincrease : ∀ slot, slot < steps.length → rank (slot + 1) ≤ rank slot := by
    intro slot inside
    obtain ⟨actual, found, before, _, after⟩ := CampusTCPSchedule.Trace.at trace slot inside
    have member := List.mem_of_getElem? found
    have bounded := CampusTCPRevocationCustody.Step.potential_nonincrease actual
      (nocopy actual member) (denied actual member)
    simpa only [rank, before, after] using bounded
  have demand : ∀ slot, slot ≤ steps.length → 0 < rank slot →
      ∃ value, D.pendingAt names initial [] steps slot = some value := by
    intro slot _ positive
    rw [pendingAt_drain]
    exact demand_exists _ positive
  have persistent : ∀ slot, slot < steps.length → 0 < rank slot → ∀ value,
      rank (slot + 1) = rank slot → D.pendingAt names initial [] steps slot = some value →
      D.pendingAt names initial [] steps (slot + 1) = some value := by
    intro slot inside _ value equal selected
    obtain ⟨actual, found, before, _, after⟩ := CampusTCPSchedule.Trace.at trace slot inside
    have member := List.mem_of_getElem? found
    have same := CampusTCPRevocationCustody.Step.frontier_eq_of_potential_eq actual
      (nocopy actual member) (denied actual member) (by simpa only [rank, before, after] using equal)
    rw [pendingAt_drain] at selected ⊢
    rw [← before] at selected
    rw [← after]
    rw [same]
    exact selected
  have strict : ∀ slot, slot < steps.length → 0 < rank slot → ∀ value,
      D.pendingAt names initial [] steps slot = some value →
      D.serves names value (S.eventAt steps slot) = true → rank (slot + 1) < rank slot := by
    intro slot inside _ value selected served
    obtain ⟨actual, found, before, event, after⟩ := CampusTCPSchedule.Trace.at trace slot inside
    have member := List.mem_of_getElem? found
    have currentHistory := CampusTCPCustodyFacts.Trace.each_history trace history actual member
    have selectedActual : (C.frontier actual.before).head?.bind D.linkDemand = some value := by
      simpa only [pendingAt_drain, ← before] using selected
    have decrease := served_strict names actual currentHistory (denied actual member) value selectedActual
      (by simpa only [event] using served)
    simpa only [rank, before, after] using decrease
  have zero := Theory.BoundedServiceRank.zero_by serviced nonincrease demand persistent strict
    (by simpa only [rank, CampusTCPSchedule.stateAt_zero] using enough)
  apply (CampusTCPRevocationCustody.potential_zero _).mp
  simpa only [rank, CampusTCPSchedule.stateAt_zero] using zero

private theorem exists_first_zero (rank : Nat → Nat) (last : Nat) (zero : rank last = 0) :
    ∃ slot, slot ≤ last ∧ rank slot = 0 ∧ ∀ earlier, earlier < slot → rank earlier ≠ 0 := by
  classical
  induction last using Nat.strongRecOn with
  | ind last ih =>
    by_cases previous : ∃ slot, slot < last ∧ rank slot = 0
    · obtain ⟨slot, before, empty⟩ := previous
      obtain ⟨first, early, zero, minimal⟩ := ih slot before empty
      exact ⟨first, Nat.le_trans early (Nat.le_of_lt before), zero, minimal⟩
    · exact ⟨last, Nat.le_refl _, zero, fun earlier before empty => previous ⟨earlier, before, empty⟩⟩

structure Cut (initial : State input) (steps : List (Step input)) (bound : Nat) where
  slot : Nat
  early : slot ≤ C.potential initial * bound
  within : slot ≤ steps.length
  empty : C.frontier (S.stateAt initial steps slot) = []
  first : ∀ earlier, earlier < slot → C.potential (S.stateAt initial steps earlier) ≠ 0
  trace : Trace input initial ((steps.take slot).map (·.event)) (steps.take slot)
    (S.stateAt initial steps slot) []

theorem exists_cut (names : M.Installation → String)
    (trace : Trace input initial events steps final remaining)
    (history : Theory.PacketCustody.History initial.custody)
    (nocopy : ∀ actual ∈ steps, ∀ id, actual.event ≠ .copyPacket id)
    (denied : ∀ actual ∈ steps, ∀ served,
      actual.result.service = some served → served.evidence.output = none)
    (bound : Nat) (checked : D.service names initial [] steps bound = true)
    (enough : C.potential initial * bound ≤ steps.length) : Nonempty (Cut initial steps bound) := by
  have empty := drain_by names trace history nocopy denied bound checked enough
  obtain ⟨slot, early, zero, first⟩ := exists_first_zero (fun slot => C.potential (S.stateAt initial steps slot))
    (C.potential initial * bound) ((CampusTCPRevocationCustody.potential_zero _).mpr empty)
  have within : slot ≤ steps.length := Nat.le_trans early enough
  exact ⟨⟨slot, early, within, (CampusTCPRevocationCustody.potential_zero _).mp zero, first,
    CampusTCPSchedule.Trace.take trace slot within⟩⟩

theorem Step.no_delivery_when_empty (actual : Step input)
    (history : Theory.PacketCustody.History actual.before.custody)
    (empty : C.frontier actual.before = []) (index : Nat) (bytes : List UInt8) (policy : Bool) :
    actual.event ≠ .deliver index bytes policy := by
  intro event
  obtain ⟨_, resolved, _, _, linked, _, _⟩ :=
    CampusTCPCustodyFacts.Step.deliver actual index bytes policy event history
  have matching := CampusTCPRevocationCustody.linkAt_isLink index _ linked
  have member : resolved.item ∈ C.frontier actual.before :=
    (actual.before.custody.frontier_member C.isLink resolved.item).mpr ⟨resolved.member, matching⟩
  rw [empty] at member
  cases member

theorem Step.no_receipt_when_empty (actual : Step input)
    (history : Theory.PacketCustody.History actual.before.custody)
    (empty : C.frontier actual.before = []) : actual.result.receipt = none := by
  cases recorded : actual.result.receipt with
  | none => rfl
  | some receipt =>
    obtain ⟨index, bytes, policy, event⟩ := CampusTCPTwoProgressReceiptFrames.Step.receipt_event actual receipt recorded
    exact False.elim (Step.no_delivery_when_empty actual history empty index bytes policy event)

end Netlib.Check.CampusTCPRevocationDrainBound
