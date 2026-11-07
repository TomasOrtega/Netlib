import Netlib.Check.CampusTCPTwoTransferEvidenceHandoff

/-!
# Handoff on one actual trace and service condition

Stopped prefixes derive current evidence before the first finished slot.
The raw control bound cannot end invalid because that same prefix has evidence.
-/

namespace Netlib.Check.CampusTCPTwoTransferEvidenceHandoffTrace

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)
open CampusTCPTwoTransferEvidence (Evidence)

namespace W
export CampusTCPTwoTransferMonitor (Monitor Allowed observe monitorAt controlDemand Serviced actions check)
end W
namespace B
export CampusTCPTwoTransferControlBound (potentialAt phase_at controls_exit_by monitorAt_next)
end B
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {steps : List (Step input)} {events remaining : List Event} {final : State input}
variable {start slot last bound : Nat} {kind : CampusTCPTwoTransferMonitor.Control}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

structure At (initial : TwoWriteInitial cut sender gateway lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (routing : Routing cut gateway)
    (quantum allowance : Nat) (reverseLower reverseUpper : List UInt8) (steps : List (Step input)) (slot : Nat) where
  current : Cut input complete
  location : Gateway
  evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current
    (W.monitorAt (config initial checks routing quantum allowance reverseLower reverseUpper) .initial steps slot) location
  final : current.report.final = S.stateAt cut.report.final steps slot
  history : current.report.steps = cut.report.steps ++ steps.take slot

def At.ofEvidence (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (stateEq : current.report.final = S.stateAt cut.report.final steps slot)
    (history : current.report.steps = cut.report.steps ++ steps.take slot)
    (monitorEq : monitor = W.monitorAt cfg .initial steps slot) :
    At initial checks routing quantum allowance reverseLower reverseUpper steps slot :=
  ⟨current, location, monitorEq ▸ evidence, stateEq, history⟩

theorem At.suffix (point : At initial checks routing quantum allowance reverseLower reverseUpper steps slot) :
    point.evidence.recorded.suffix = steps.take slot := by
  apply List.append_cancel_left
  exact point.evidence.recorded.history.symm.trans point.history

theorem At.loss_suffix (point : At initial checks routing quantum allowance reverseLower reverseUpper steps slot) :
    point.evidence.core.losses.suffix = steps.take slot := point.evidence.loss_suffix.symm.trans point.suffix

theorem At.now_le (point : At initial checks routing quantum allowance reverseLower reverseUpper steps slot) (actor : Actor) :
    (endpoint point.current.endpoints actor).now ≤ (endpoint cut.endpoints actor).now + slot * quantum := by
  have elapsed := point.evidence.now_le actor
  rw [point.loss_suffix] at elapsed
  have length : (steps.take slot).length ≤ slot := by rw [List.length_take]; exact Nat.min_le_left _ _
  exact Nat.le_trans elapsed (Nat.add_le_add_left (Nat.mul_le_mul_right quantum length) _)

private theorem take_next {α : Type} {values : List α} {index : Nat} {value : α} (found : values[index]? = some value) :
    values.take (index + 1) = values.take index ++ [value] := by
  induction values generalizing index with
  | nil => simp at found
  | cons head rest ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found; subst value; rfl
    | succ index => simpa only [List.take_succ_cons, List.cons_append] using congrArg (List.cons head) (ih found)

theorem At.step (point : At initial checks routing quantum allowance reverseLower reverseUpper steps slot)
    (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ index, index < steps.length → W.Allowed cfg (S.stateAt cut.report.final steps index)
      (W.monitorAt cfg .initial steps index) (S.eventAt steps index))
    (selected : W.controlDemand (W.monitorAt cfg .initial steps slot) = some kind) (inside : slot < steps.length) :
    Nonempty (At initial checks routing quantum allowance reverseLower reverseUpper steps (slot + 1)) := by
  obtain ⟨actual, found, before, event, after⟩ := CampusTCPSchedule.Trace.at trace slot inside
  have allowed : W.Allowed cfg point.current.report.final (W.monitorAt cfg .initial steps slot) actual.event := by
    rw [point.final, event]
    exact actions slot inside
  obtain ⟨advance⟩ := point.evidence.control_region_step selected actual (before.trans point.final.symm) allowed
  have observed : W.observe cfg (W.monitorAt cfg .initial steps slot) actual = W.monitorAt cfg .initial steps (slot + 1) :=
    (B.monitorAt_next steps found).symm
  exact ⟨{
    current := advance.move.after
    location := advance.location
    evidence := observed ▸ advance.next
    final := advance.move.final.trans after
    history := by rw [advance.move.history, point.history, take_next found, List.append_assoc] }⟩

private theorem stopped_count (entry : At initial checks routing quantum allowance reverseLower reverseUpper steps start)
    (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ index, index < steps.length → W.Allowed cfg (S.stateAt cut.report.final steps index)
      (W.monitorAt cfg .initial steps index) (S.eventAt steps index))
    (selected : W.controlDemand (W.monitorAt cfg .initial steps start) = some kind) :
    ∀ count, start + count ≤ steps.length →
      (∀ prior, start ≤ prior → prior < start + count → (W.monitorAt cfg .initial steps prior).mode ≠ .finished) →
        Nonempty (At initial checks routing quantum allowance reverseLower reverseUpper steps (start + count)) := by
  intro count
  induction count with
  | zero => intro _ _; simpa only [Nat.add_zero] using (Nonempty.intro entry)
  | succ count ih =>
    intro within stopped
    obtain ⟨point⟩ := ih (by omega) (fun prior order before => stopped prior order (by omega))
    have phase := B.phase_at trace selected (slot := start + count) (by omega) (by omega)
    have current : ∃ kind, W.controlDemand (W.monitorAt cfg .initial steps (start + count)) = some kind := by
      rcases phase with selected | finished | invalid
      · exact selected
      · exact False.elim (stopped (start + count) (by omega) (by omega) finished)
      · exact False.elim (point.evidence.healthy invalid)
    obtain ⟨kind, current⟩ := current
    simpa only [Nat.add_assoc] using point.step trace actions current (by omega)

theorem stopped_prefix (entry : At initial checks routing quantum allowance reverseLower reverseUpper steps start)
    (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ index, index < steps.length → W.Allowed cfg (S.stateAt cut.report.final steps index)
      (W.monitorAt cfg .initial steps index) (S.eventAt steps index))
    (selected : W.controlDemand (W.monitorAt cfg .initial steps start) = some kind)
    (order : start ≤ last) (within : last ≤ steps.length)
    (stopped : ∀ prior, start ≤ prior → prior < last → (W.monitorAt cfg .initial steps prior).mode ≠ .finished) :
    Nonempty (At initial checks routing quantum allowance reverseLower reverseUpper steps last) := by
  obtain ⟨count, rfl⟩ := Nat.exists_eq_add_of_le order
  exact stopped_count entry trace actions selected count within stopped

structure Finished (initial : TwoWriteInitial cut sender gateway lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (routing : Routing cut gateway)
    (quantum allowance : Nat) (reverseLower reverseUpper : List UInt8) (steps : List (Step input)) (slot : Nat) where
  point : At initial checks routing quantum allowance reverseLower reverseUpper steps slot
  finished : (W.monitorAt (config initial checks routing quantum allowance reverseLower reverseUpper) .initial steps slot).mode = .finished

theorem Finished.standby_location (value : Finished initial checks routing quantum allowance reverseLower reverseUpper steps slot) :
    value.point.location = .standby := by
  have phase : CampusTCPTwoTransferControlState.Phase value.point.current.report.final .finished value.point.location :=
    value.finished ▸ value.point.evidence.controls
  generalize locationEq : value.point.location = currentLocation at phase ⊢
  cases phase
  rfl

theorem Finished.standby_routing (value : Finished initial checks routing quantum allowance reverseLower reverseUpper steps slot) :
    Routing value.point.current .standby :=
  CampusTCPTwoTransferControlState.finished_routing (value.finished ▸ value.point.evidence.controls)

private theorem first_within {predicate : Nat → Prop} {limit : Nat} (found : ∃ slot, slot ≤ limit ∧ predicate slot) :
    ∃ slot, slot ≤ limit ∧ predicate slot ∧ ∀ prior, prior < slot → ¬predicate prior := by
  classical
  induction limit with
  | zero =>
    obtain ⟨slot, within, selected⟩ := found
    have same : slot = 0 := by omega
    subst slot
    exact ⟨0, Nat.le_refl _, selected, by intro prior impossible; omega⟩
  | succ limit ih =>
    by_cases earlier : ∃ slot, slot ≤ limit ∧ predicate slot
    · obtain ⟨slot, within, selected, first⟩ := ih earlier
      exact ⟨slot, by omega, selected, first⟩
    · obtain ⟨slot, within, selected⟩ := found
      have last : slot = limit + 1 := by
        by_cases before : slot ≤ limit
        · exact False.elim (earlier ⟨slot, before, selected⟩)
        · omega
      exact ⟨slot, within, selected, fun prior before selected => earlier ⟨prior, by omega, selected⟩⟩

theorem finishes_by (entry : At initial checks routing quantum allowance reverseLower reverseUpper steps start)
    (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ index, index < steps.length → W.Allowed cfg (S.stateAt cut.report.final steps index)
      (W.monitorAt cfg .initial steps index) (S.eventAt steps index))
    (service : W.Serviced cfg cut.report.final .initial steps bound)
    (selected : W.controlDemand (W.monitorAt cfg .initial steps start) = some kind)
    (enough : start + B.potentialAt cfg cut.report.final .initial steps start * bound ≤ steps.length) :
    ∃ slot, start ≤ slot ∧ slot ≤ start + B.potentialAt cfg cut.report.final .initial steps start * bound ∧
      Nonempty (Finished initial checks routing quantum allowance reverseLower reverseUpper steps slot) := by
  classical
  let deadline := start + B.potentialAt cfg cut.report.final .initial steps start * bound
  have exits := B.controls_exit_by trace service selected enough
  by_cases found : ∃ slot, start ≤ slot ∧ slot ≤ deadline ∧ (W.monitorAt cfg .initial steps slot).mode = .finished
  · obtain ⟨slot, within, properties, first⟩ := first_within (predicate := fun slot =>
      start ≤ slot ∧ (W.monitorAt cfg .initial steps slot).mode = .finished)
      (show ∃ slot, slot ≤ deadline ∧ start ≤ slot ∧ (W.monitorAt cfg .initial steps slot).mode = .finished from
        by obtain ⟨slot, order, within, finished⟩ := found; exact ⟨slot, within, order, finished⟩)
    have stopped : ∀ prior, start ≤ prior → prior < slot → (W.monitorAt cfg .initial steps prior).mode ≠ .finished := by
      intro prior order before finished
      exact first prior before ⟨order, finished⟩
    obtain ⟨point⟩ := stopped_prefix entry trace actions selected properties.1 (by omega) stopped
    exact ⟨slot, properties.1, within, ⟨⟨point, properties.2⟩⟩⟩
  · have stopped : ∀ prior, start ≤ prior → prior < deadline → (W.monitorAt cfg .initial steps prior).mode ≠ .finished := by
      intro prior order before finished
      exact found ⟨prior, order, by omega, finished⟩
    obtain ⟨point⟩ := stopped_prefix entry trace actions selected (by omega) enough stopped
    have finished : (W.monitorAt cfg .initial steps deadline).mode = .finished := exits.resolve_right point.evidence.healthy
    exact False.elim (found ⟨deadline, by omega, Nat.le_refl _, finished⟩)

theorem finishes_by_eight (entry : At initial checks routing quantum allowance reverseLower reverseUpper steps start)
    (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ index, index < steps.length → W.Allowed cfg (S.stateAt cut.report.final steps index)
      (W.monitorAt cfg .initial steps index) (S.eventAt steps index))
    (service : W.Serviced cfg cut.report.final .initial steps bound)
    (selected : W.controlDemand (W.monitorAt cfg .initial steps start) = some kind)
    (enough : start + 8 * bound ≤ steps.length) :
    ∃ slot, start ≤ slot ∧ slot ≤ start + 8 * bound ∧
      Nonempty (Finished initial checks routing quantum allowance reverseLower reverseUpper steps slot) := by
  have potential : B.potentialAt cfg cut.report.final .initial steps start ≤ 8 := by
    rw [B.potentialAt, ← entry.final]
    exact entry.evidence.control_potential_le_eight selected
  have deadline : start + B.potentialAt cfg cut.report.final .initial steps start * bound ≤ start + 8 * bound :=
    Nat.add_le_add_left (Nat.mul_le_mul_right bound potential) start
  obtain ⟨slot, order, within, finished⟩ := finishes_by entry trace actions service selected (Nat.le_trans deadline enough)
  exact ⟨slot, order, Nat.le_trans within deadline, finished⟩

theorem finishes_by_eight_checked (entry : At initial checks routing quantum allowance reverseLower reverseUpper steps start)
    (trace : Trace input cut.report.final events steps final remaining)
    (actions : W.actions cfg cut.report.final .initial steps = true)
    (service : W.check cfg cut.report.final .initial steps bound = true)
    (selected : W.controlDemand (W.monitorAt cfg .initial steps start) = some kind)
    (enough : start + 8 * bound ≤ steps.length) :
    ∃ slot, start ≤ slot ∧ slot ≤ start + 8 * bound ∧
      Nonempty (Finished initial checks routing quantum allowance reverseLower reverseUpper steps slot) :=
  finishes_by_eight entry trace ((CampusTCPTwoTransferMonitor.actions_correct _ _ _ _).mp actions)
    ((CampusTCPTwoTransferMonitor.check_correct _ _ _ _ _).mp service) selected enough

end Netlib.Check.CampusTCPTwoTransferEvidenceHandoffTrace
