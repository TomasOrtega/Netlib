import Netlib.Check.CampusTCPTwoTransferRecoveryAt
import Netlib.Check.CampusTCPTwoTransferRecoveryCap

/-!
# Actual recovery prefixes with a fixed pending cap

Every continued step keeps the cap and the original report prefix.
The terminal alternative retains the actual selected forward read.
-/

namespace Netlib.Check.CampusTCPTwoTransferRecoveryTrace

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)
open CampusTCPTwoTransferEvidenceHandoffTrace (At)
open CampusTCPTwoTransferEvidenceTrace (ReadAt)

namespace W
export CampusTCPTwoTransferMonitor (Allowed observe)
end W
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance capacity : Nat} {reverseLower reverseUpper : List UInt8}
variable {steps : List (Step input)} {events remaining : List Event} {final : State input}
variable {start slot last : Nat}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

private theorem take_next {α : Type} {values : List α} {index : Nat} {value : α} (found : values[index]? = some value) :
    values.take (index + 1) = values.take index ++ [value] := by
  induction values generalizing index with
  | nil => simp at found
  | cons head rest ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found; subst value; rfl
    | succ index => simpa only [List.take_succ_cons, List.cons_append] using congrArg (List.cons head) (ih found)

theorem advance_at (entry : RecoveryAt initial checks routing quantum allowance reverseLower reverseUpper capacity steps slot)
    (budget : allowance ≤ 2) (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ index, index < steps.length → W.Allowed cfg (S.stateAt cut.report.final steps index)
      (W.monitorAt cfg .initial steps index) (S.eventAt steps index)) (inside : slot < steps.length) :
    Nonempty (RecoveryAt initial checks routing quantum allowance reverseLower reverseUpper capacity steps (slot + 1)) ∨
      Nonempty (ReadAt initial checks routing quantum allowance reverseLower reverseUpper steps slot) := by
  obtain ⟨actual, found, before, event, after⟩ := CampusTCPSchedule.Trace.at trace slot inside
  have allowed : W.Allowed cfg entry.point.current.report.final (W.monitorAt cfg .initial steps slot) actual.event := by
    rw [entry.point.final, event]
    exact actions slot inside
  have observed : W.observe cfg (W.monitorAt cfg .initial steps slot) actual = W.monitorAt cfg .initial steps (slot + 1) :=
    (CampusTCPTwoTransferControlBound.monitorAt_next steps found).symm
  rcases entry.point.evidence.step budget actual (before.trans entry.point.final.symm) allowed with running | done
  · obtain ⟨advance⟩ := running
    have nonoriginal := CampusTCPTwoTransferNonoriginal.advanced_nonoriginal advance entry.nonoriginal allowed
    have pendingCap := CampusTCPTwoTransferRecoveryCap.step entry.point.evidence entry.nonoriginal entry.pendingCap budget advance.move allowed
    let point : At initial checks routing quantum allowance reverseLower reverseUpper steps (slot + 1) := {
      current := advance.move.after
      location := advance.location
      evidence := observed ▸ advance.next
      final := advance.move.final.trans after
      history := by rw [advance.move.history, entry.point.history, take_next found, List.append_assoc] }
    refine .inl ⟨⟨point, ?_, ?_⟩⟩
    · rw [← observed]
      exact nonoriginal
    · change CampusTCPTwoTransferHandoffRTO.PendingCap cfg capacity advance.move.after.report.final _
      rw [← observed]
      exact pendingCap
  · obtain ⟨advance⟩ := done
    exact .inr ⟨{
      point := entry.point
      actual, found, advance
      final := advance.value.value.move.final.trans after
      history := by
        change advance.value.value.move.after.report.steps = _
        rw [advance.value.value.move.history, entry.point.history, take_next found, List.append_assoc] }⟩

private theorem stopped_count (entry : RecoveryAt initial checks routing quantum allowance reverseLower reverseUpper capacity steps start)
    (budget : allowance ≤ 2) (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ index, index < steps.length → W.Allowed cfg (S.stateAt cut.report.final steps index)
      (W.monitorAt cfg .initial steps index) (S.eventAt steps index)) :
    ∀ count, start + count ≤ steps.length →
      (∀ prior, start ≤ prior → prior < start + count →
        ¬Nonempty (ReadAt initial checks routing quantum allowance reverseLower reverseUpper steps prior)) →
      Nonempty (RecoveryAt initial checks routing quantum allowance reverseLower reverseUpper capacity steps (start + count)) := by
  intro count
  induction count with
  | zero => intro _ _; simpa only [Nat.add_zero] using (Nonempty.intro entry)
  | succ count ih =>
    intro within stopped
    obtain ⟨point⟩ := ih (by omega) (fun prior order before => stopped prior order (by omega))
    rcases advance_at point budget trace actions (by omega) with continued | read
    · simpa only [Nat.add_assoc] using continued
    · exact False.elim (stopped (start + count) (by omega) (by omega) read)

theorem stopped_prefix (entry : RecoveryAt initial checks routing quantum allowance reverseLower reverseUpper capacity steps start)
    (budget : allowance ≤ 2) (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ index, index < steps.length → W.Allowed cfg (S.stateAt cut.report.final steps index)
      (W.monitorAt cfg .initial steps index) (S.eventAt steps index)) (order : start ≤ last) (within : last ≤ steps.length)
    (stopped : ∀ prior, start ≤ prior → prior < last →
      ¬Nonempty (ReadAt initial checks routing quantum allowance reverseLower reverseUpper steps prior)) :
    Nonempty (RecoveryAt initial checks routing quantum allowance reverseLower reverseUpper capacity steps last) := by
  obtain ⟨count, rfl⟩ := Nat.exists_eq_add_of_le order
  exact stopped_count entry budget trace actions count within stopped

end Netlib.Check.CampusTCPTwoTransferRecoveryTrace
