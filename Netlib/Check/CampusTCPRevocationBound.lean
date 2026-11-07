import Netlib.Check.CampusTCPRevocationInstallation
import Netlib.Check.CampusTCPRevocationDenial
import Netlib.Check.CampusTCPRevocationDrainBound
import Netlib.Check.CampusTCPRevocationLoss

/-!
# One bounded TCP shutdown after the actual authentication trigger

Four stored native targets precede resolution of the retained link frontier.
The whole action and service checks cover both phases and the original loss gate.
-/

namespace Netlib.Check.CampusTCPRevocationBound

open CampusTCPModel CampusTCPRevocationTargets

namespace C
export CampusTCPRevocationCustody (frontier potential)
end C
namespace M
export CampusTCPRevocationMonitor (initial monitorAt)
end M
namespace D
export CampusTCPRevocationControl (allowed actions pending pendingAt service serves)
end D
namespace I
export CampusTCPRevocationInstallation (actions_member installed_at empty_after)
end I
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

variable {input : Input} {initial final : State input} {events remaining : List Event}
variable {steps : List (Step input)} {allowance bound : Nat}

def slots (initial : State input) (bound : Nat) : Nat :=
  4 * bound + (C.potential initial + 4 * bound) * bound

private theorem member_drop_state (trace : Trace input initial events steps final remaining)
    (offset : Nat) (actual : Step input) (member : actual ∈ steps.drop offset) :
    ∃ index, offset ≤ index ∧ index < steps.length ∧ actual.before = S.stateAt initial steps index := by
  obtain ⟨localSlot, selected⟩ := List.mem_iff_getElem?.mp member
  have found : steps[offset + localSlot]? = some actual := by
    simpa only [List.getElem?_drop] using selected
  have inside := (List.getElem?_eq_some_iff.mp found).1
  obtain ⟨recorded, located, before, _, _⟩ := CampusTCPSchedule.Trace.at trace (offset + localSlot) inside
  have same : recorded = actual := Option.some.inj (located.symm.trans found)
  exact ⟨offset + localSlot, by omega, inside, by simpa only [same] using before⟩

theorem no_copies (names : CampusTCPRevocationMonitor.Installation → String)
    (actions : D.actions names allowance steps = true) :
    ∀ actual ∈ steps, ∀ id, actual.event ≠ .copyPacket id := by
  intro actual member
  exact CampusTCPRevocationControl.allowed_no_copy names allowance actual.before actual.event
    (I.actions_member names actions actual member)

theorem services_denied_after (trace : Trace input initial events steps final remaining)
    (targets : Targets input initial) (actions : D.actions targets.names allowance steps = true)
    (checked : D.service targets.names initial M.initial steps bound = true)
    (closed : revoked input initial.authentication = true) (enough : 4 * bound ≤ steps.length)
    (offset : Nat) (afterInstall : 4 * bound ≤ offset) :
    ∀ actual ∈ steps.drop offset, ∀ served,
      actual.result.service = some served → served.evidence.output = none := by
  intro actual member served present
  obtain ⟨index, afterOffset, inside, before⟩ := member_drop_state trace offset actual member
  have installed := (I.installed_at trace targets actions checked enough (by omega : 4 * bound ≤ index)
    (Nat.le_of_lt inside)).1
  exact targets.service_output_none closed actual served present (by rw [before]; exact installed)

theorem barrier_potential (trace : Trace input initial events steps final remaining)
    (names : CampusTCPRevocationMonitor.Installation → String) (actions : D.actions names allowance steps = true)
    (enough : 4 * bound ≤ steps.length) :
    C.potential (S.stateAt initial steps (4 * bound)) ≤ C.potential initial + 4 * bound := by
  have bounded := CampusTCPRevocationCustody.Trace.potential_le_slots
    (CampusTCPSchedule.Trace.take trace (4 * bound) enough)
    (fun actual member => no_copies names actions actual (List.mem_of_mem_take member))
  simpa only [List.length_take, Nat.min_eq_left enough] using bounded

theorem drain_service (names : CampusTCPRevocationMonitor.Installation → String)
    (checked : D.service names initial M.initial steps bound = true) (enough : 4 * bound ≤ steps.length) :
    D.service names (S.stateAt initial steps (4 * bound)) [] (steps.drop (4 * bound)) bound = true := by
  have whole := (Theory.BoundedServiceCheck.check_correct _ _ _ _ _).mp checked
  apply (Theory.BoundedServiceCheck.check_correct _ _ _ _ _).mpr
  apply Theory.BoundedServiceProjection.restrict (offset := 4 * bound) whole
    (by rw [List.length_drop]; omega) id id
  · intro slot within demand selected
    have inside : 4 * bound + slot ≤ steps.length := by rw [List.length_drop] at within; omega
    have empty := I.empty_after names checked enough (Nat.le_add_right _ _) inside
    unfold D.pendingAt D.pending at selected ⊢
    rw [CampusTCPRevocationDrainBound.monitorAt_nil, CampusTCPTraceSlices.stateAt_drop] at selected
    rw [empty]
    exact selected
  · intro slot _
    exact (CampusTCPTraceSlices.eventAt_drop steps (4 * bound) slot).symm
  · intro _ _
    rfl

theorem frontier_empty_after (trace : Trace input initial events steps final remaining)
    (targets : Targets input initial) (actions : D.actions targets.names allowance steps = true)
    (checked : D.service targets.names initial M.initial steps bound = true)
    (closed : revoked input initial.authentication = true) (enough : 4 * bound ≤ steps.length)
    (cut : Nat) (afterInstall : 4 * bound ≤ cut) (cutWithin : cut ≤ steps.length)
    (empty : C.frontier (S.stateAt initial steps cut) = [])
    (later : Nat) (afterCut : cut ≤ later) (within : later ≤ steps.length) :
    C.frontier (S.stateAt initial steps later) = [] := by
  have suffix := CampusTCPTraceSlices.Trace.drop trace cutWithin
  have part := CampusTCPSchedule.Trace.take suffix (later - cut) (by rw [List.length_drop]; omega)
  have retained := CampusTCPRevocationCustody.Trace.frontier_empty part
    (fun actual member => no_copies targets.names actions actual (List.mem_of_mem_drop (List.mem_of_mem_take member)))
    (fun actual member => services_denied_after trace targets actions checked closed enough cut afterInstall
      actual (List.mem_of_mem_take member)) empty
  simpa only [CampusTCPTraceSlices.stateAt_drop, Nat.add_sub_of_le afterCut] using retained

theorem receipts_none_after (trace : Trace input initial events steps final remaining)
    (targets : Targets input initial) (actions : D.actions targets.names allowance steps = true)
    (checked : D.service targets.names initial M.initial steps bound = true)
    (closed : revoked input initial.authentication = true) (enough : 4 * bound ≤ steps.length)
    (history : Theory.PacketCustody.History initial.custody)
    (cut : Nat) (afterInstall : 4 * bound ≤ cut) (cutWithin : cut ≤ steps.length)
    (empty : C.frontier (S.stateAt initial steps cut) = []) :
    ∀ actual ∈ steps.drop cut, actual.result.receipt = none := by
  intro actual member
  obtain ⟨index, afterCut, inside, before⟩ := member_drop_state trace cut actual member
  have emptyAt := frontier_empty_after trace targets actions checked closed enough cut afterInstall cutWithin
    empty index afterCut (Nat.le_of_lt inside)
  exact CampusTCPRevocationDrainBound.Step.no_receipt_when_empty actual
    (CampusTCPCustodyFacts.Trace.each_history trace history actual (List.mem_of_mem_drop member))
    (by rw [before]; exact emptyAt)

structure Result (initial : State input) (targets : Targets input initial) (steps : List (Step input)) (bound : Nat) where
  slot : Nat
  afterInstall : 4 * bound ≤ slot
  deadline : slot ≤ slots initial bound
  within : slot ≤ steps.length
  empty : C.frontier (S.stateAt initial steps slot) = []
  installed : targets.Installed (S.stateAt initial steps slot)
  current : targets.CurrentAt (S.stateAt initial steps slot)
  trace : Trace input initial ((steps.take slot).map (·.event)) (steps.take slot) (S.stateAt initial steps slot) []
  laterEmpty : ∀ later, slot ≤ later → later ≤ steps.length → C.frontier (S.stateAt initial steps later) = []
  noService : ∀ actual ∈ steps.drop slot, ∀ served,
    actual.result.service = some served → served.evidence.output = none
  noReceipt : ∀ actual ∈ steps.drop slot, actual.result.receipt = none

theorem complete (trace : Trace input initial events steps final remaining) (targets : Targets input initial)
    (actions : D.actions targets.names allowance steps = true)
    (checked : D.service targets.names initial M.initial steps bound = true)
    (closed : revoked input initial.authentication = true) (history : Theory.PacketCustody.History initial.custody)
    (enough : slots initial bound ≤ steps.length) : Nonempty (Result initial targets steps bound) := by
  have installWithin : 4 * bound ≤ steps.length := by unfold slots at enough; omega
  have upper := barrier_potential trace targets.names actions installWithin
  have capacity : C.potential (S.stateAt initial steps (4 * bound)) * bound ≤ (steps.drop (4 * bound)).length := by
    rw [List.length_drop]
    have product := Nat.mul_le_mul_right bound upper
    unfold slots at enough
    omega
  have suffix := CampusTCPTraceSlices.Trace.drop trace installWithin
  have barrierHistory := CampusTCPCustodyFacts.Trace.history
    (CampusTCPSchedule.Trace.take trace (4 * bound) installWithin) history
  obtain ⟨drained⟩ := CampusTCPRevocationDrainBound.exists_cut targets.names suffix barrierHistory
    (fun actual member => no_copies targets.names actions actual (List.mem_of_mem_drop member))
    (services_denied_after trace targets actions checked closed installWithin (4 * bound) (Nat.le_refl _))
    bound (drain_service targets.names checked installWithin) capacity
  let cut := 4 * bound + drained.slot
  have cutWithin : cut ≤ steps.length := by
    have bounded := drained.within
    rw [List.length_drop] at bounded
    dsimp only [cut]
    omega
  have afterInstall : 4 * bound ≤ cut := Nat.le_add_right _ _
  have empty : C.frontier (S.stateAt initial steps cut) = [] := by
    simpa only [CampusTCPTraceSlices.stateAt_drop, cut] using drained.empty
  have installed := I.installed_at trace targets actions checked installWithin afterInstall cutWithin
  refine ⟨⟨cut, afterInstall, ?_, cutWithin, empty, installed.1, installed.2,
    CampusTCPSchedule.Trace.take trace cut cutWithin,
    frontier_empty_after trace targets actions checked closed installWithin cut afterInstall cutWithin empty,
    services_denied_after trace targets actions checked closed installWithin cut afterInstall,
    receipts_none_after trace targets actions checked closed installWithin history cut afterInstall cutWithin empty⟩⟩
  have product := Nat.mul_le_mul_right bound upper
  have early := drained.early
  unfold slots
  dsimp only [cut]
  omega

theorem whole_budget (trace : Trace input initial events steps final remaining) (targets : Targets input initial)
    (actions : D.actions targets.names allowance steps = true) (prior : initial.custody.dropped ≤ allowance) :
    final.custody.dropped ≤ allowance :=
  CampusTCPRevocationLoss.Trace.budget trace targets.names allowance actions prior

end Netlib.Check.CampusTCPRevocationBound
