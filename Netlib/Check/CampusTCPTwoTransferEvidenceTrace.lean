import Netlib.Check.CampusTCPTwoTransferEvidenceStep
import Netlib.Check.CampusTCPTwoTransferEvidenceHandoffTrace

/-!
# Forward evidence on the supplied trace

Each prefix uses the same actual steps and report history.
The forward read retains its actual slot and terminal evidence.
-/

namespace Netlib.Check.CampusTCPTwoTransferEvidenceTrace

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)
open CampusTCPTwoTransferEvidence (Evidence ReadAdvanced)
open CampusTCPTwoTransferEvidenceHandoffTrace (At)

namespace W
export CampusTCPTwoTransferMonitor (Monitor Allowed observe monitorAt)
end W
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {steps : List (Step input)} {events remaining : List Event} {final : State input}
variable {start slot last : Nat}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

structure ReadAt (initial : TwoWriteInitial cut sender gateway lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (routing : Routing cut gateway)
    (quantum allowance : Nat) (reverseLower reverseUpper : List UInt8) (steps : List (Step input)) (slot : Nat) where
  point : At initial checks routing quantum allowance reverseLower reverseUpper steps slot
  actual : Step input
  found : steps[slot]? = some actual
  advance : ReadAdvanced point.evidence actual
  final : advance.value.finalCut.report.final = S.stateAt cut.report.final steps (slot + 1)
  history : advance.value.finalCut.report.steps = cut.report.steps ++ steps.take (slot + 1)

private theorem take_next {α : Type} {values : List α} {index : Nat} {value : α} (found : values[index]? = some value) :
    values.take (index + 1) = values.take index ++ [value] := by
  induction values generalizing index with
  | nil => simp at found
  | cons head rest ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found; subst value; rfl
    | succ index => simpa only [List.take_succ_cons, List.cons_append] using congrArg (List.cons head) (ih found)

theorem advance_at (point : At initial checks routing quantum allowance reverseLower reverseUpper steps slot)
    (budget : allowance ≤ 2) (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ index, index < steps.length → W.Allowed cfg (S.stateAt cut.report.final steps index)
      (W.monitorAt cfg .initial steps index) (S.eventAt steps index)) (inside : slot < steps.length) :
    Nonempty (At initial checks routing quantum allowance reverseLower reverseUpper steps (slot + 1)) ∨
      Nonempty (ReadAt initial checks routing quantum allowance reverseLower reverseUpper steps slot) := by
  obtain ⟨actual, found, before, event, after⟩ := CampusTCPSchedule.Trace.at trace slot inside
  have allowed : W.Allowed cfg point.current.report.final (W.monitorAt cfg .initial steps slot) actual.event := by
    rw [point.final, event]
    exact actions slot inside
  have observed : W.observe cfg (W.monitorAt cfg .initial steps slot) actual = W.monitorAt cfg .initial steps (slot + 1) :=
    (CampusTCPTwoTransferControlBound.monitorAt_next steps found).symm
  rcases point.evidence.step budget actual (before.trans point.final.symm) allowed with running | done
  · obtain ⟨advance⟩ := running
    exact .inl ⟨{
      current := advance.move.after
      location := advance.location
      evidence := observed ▸ advance.next
      final := advance.move.final.trans after
      history := by rw [advance.move.history, point.history, take_next found, List.append_assoc] }⟩
  · obtain ⟨advance⟩ := done
    exact .inr ⟨{
      point, actual, found, advance
      final := advance.value.value.move.final.trans after
      history := by
        change advance.value.value.move.after.report.steps = _
        rw [advance.value.value.move.history, point.history, take_next found, List.append_assoc] }⟩

theorem ReadAt.after_mode (read : ReadAt initial checks routing quantum allowance reverseLower reverseUpper steps slot) :
    (W.monitorAt cfg .initial steps (slot + 1)).exchange.mode = .needWrite := by
  rw [CampusTCPTwoTransferControlBound.monitorAt_next steps read.found]
  exact read.advance.need_write

theorem original_step (point : At initial checks routing quantum allowance reverseLower reverseUpper steps slot)
    (budget : allowance ≤ 2) (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ index, index < steps.length → W.Allowed cfg (S.stateAt cut.report.final steps index)
      (W.monitorAt cfg .initial steps index) (S.eventAt steps index))
    (originals : (W.monitorAt cfg .initial steps slot).exchange.forward.mode = .originals) (inside : slot < steps.length) :
    Nonempty (At initial checks routing quantum allowance reverseLower reverseUpper steps (slot + 1)) := by
  rcases advance_at point budget trace actions inside with advance | done
  · exact advance
  · obtain ⟨read⟩ := done
    have impossible := read.advance.value.needRead
    rw [originals] at impossible
    cases impossible

private theorem original_count (entry : At initial checks routing quantum allowance reverseLower reverseUpper steps start)
    (budget : allowance ≤ 2) (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ index, index < steps.length → W.Allowed cfg (S.stateAt cut.report.final steps index)
      (W.monitorAt cfg .initial steps index) (S.eventAt steps index)) :
    ∀ count, start + count ≤ steps.length →
      (∀ prior, start ≤ prior → prior < start + count →
        (W.monitorAt cfg .initial steps prior).exchange.forward.mode = .originals) →
      Nonempty (At initial checks routing quantum allowance reverseLower reverseUpper steps (start + count)) := by
  intro count
  induction count with
  | zero => intro _ _; simpa only [Nat.add_zero] using (Nonempty.intro entry)
  | succ count ih =>
    intro within stopped
    obtain ⟨point⟩ := ih (by omega) (fun prior order before => stopped prior order (by omega))
    simpa only [Nat.add_assoc] using original_step point budget trace actions
      (stopped (start + count) (by omega) (by omega)) (by omega)

theorem original_prefix (entry : At initial checks routing quantum allowance reverseLower reverseUpper steps start)
    (budget : allowance ≤ 2) (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ index, index < steps.length → W.Allowed cfg (S.stateAt cut.report.final steps index)
      (W.monitorAt cfg .initial steps index) (S.eventAt steps index)) (order : start ≤ last) (within : last ≤ steps.length)
    (stopped : ∀ prior, start ≤ prior → prior < last →
      (W.monitorAt cfg .initial steps prior).exchange.forward.mode = .originals) :
    Nonempty (At initial checks routing quantum allowance reverseLower reverseUpper steps last) := by
  obtain ⟨count, rfl⟩ := Nat.exists_eq_add_of_le order
  exact original_count entry budget trace actions count within stopped

end Netlib.Check.CampusTCPTwoTransferEvidenceTrace
