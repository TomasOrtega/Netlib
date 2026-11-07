import Netlib.Check.CampusTCPTwoTransferCurrentReverseAt
import Netlib.Check.CampusTCPTwoTransferCurrentReverseBounded

/-!
# Reverse evidence on every supplied whole prefix

The actual write starts the local reverse task.
Every later allowed step extends the same stored report, including done clocks.
-/

namespace Netlib.Check.CampusTCPTwoTransferCurrentReverseAtTrace

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferEvidence (Evidence ReadAdvanced)
open CampusTCPTwoTransferPostRead (After)
open CampusTCPTwoTransferCurrentReverseGeometry (Started)
open CampusTCPTwoTransferCurrentReverseAt (Current)
open CampusTCPTwoTransferLocatedCore (config)

namespace W
export CampusTCPTwoTransferMonitor (Monitor Allowed observe monitorAt)
end W
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut readBefore writeBefore : Cut input complete} {sender : Actor} {gateway location : Gateway}
variable {lower upper : List UInt8} {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {readMonitor writeMonitor : W.Monitor} {readActual written : Step input}
variable {evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper readBefore readMonitor location}
variable {forward : ReadAdvanced evidence readActual} {post : After forward writeBefore writeMonitor}
variable {steps : List (Step input)} {offset slot last writeSlot : Nat}
variable {events remaining : List Event} {final : State input}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

structure At (start : Started post written) (steps : List (Step input)) (slot : Nat) where
  current : Cut input complete
  value : Current start current (W.monitorAt cfg .initial steps slot)
  final : current.report.final = S.stateAt cut.report.final steps slot
  history : current.report.steps = cut.report.steps ++ steps.take slot

private theorem take_next {values : List α} {index : Nat} {value : α} (found : values[index]? = some value) :
    values.take (index + 1) = values.take index ++ [value] := by
  induction values generalizing index with
  | nil => simp at found
  | cons head rest ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found; subst value; rfl
    | succ index => simpa only [List.take_succ_cons, List.cons_append] using congrArg (List.cons head) (ih found)

def At.ofWriteAt (write : CampusTCPTwoTransferCurrentReverseBounded.WriteAt forward steps writeSlot) :
    At write.start steps (writeSlot + 1) where
  current := write.start.boundary.write.move.after
  value := by
    rw [CampusTCPTwoTransferControlBound.monitorAt_next steps write.found]
    exact CampusTCPTwoTransferCurrentReverseAt.Current.ofStart write.start
  final := write.final
  history := write.history

variable {start : Started post written}

theorem advance_at (entry : At start steps slot) (budget : allowance ≤ 2)
    (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ index, index < steps.length → W.Allowed cfg (S.stateAt cut.report.final steps index)
      (W.monitorAt cfg .initial steps index) (S.eventAt steps index)) (inside : slot < steps.length) :
    Nonempty (At start steps (slot + 1)) := by
  obtain ⟨actual, found, before, event, after⟩ := CampusTCPSchedule.Trace.at trace slot inside
  have allowed : W.Allowed cfg entry.current.report.final (W.monitorAt cfg .initial steps slot) actual.event := by
    rw [entry.final, event]
    exact actions slot inside
  obtain ⟨advance⟩ := CampusTCPTwoTransferCurrentReverseAt.step entry.value budget actual
    (before.trans entry.final.symm) allowed
  have observed : W.observe cfg (W.monitorAt cfg .initial steps slot) actual = W.monitorAt cfg .initial steps (slot + 1) :=
    (CampusTCPTwoTransferControlBound.monitorAt_next steps found).symm
  exact ⟨{
    current := advance.move.after
    value := observed ▸ advance.next
    final := advance.move.final.trans after
    history := by rw [advance.move.history, entry.history, take_next found, List.append_assoc] }⟩

theorem prefix_at (entry : At start steps offset) (budget : allowance ≤ 2)
    (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ index, index < steps.length → W.Allowed cfg (S.stateAt cut.report.final steps index)
      (W.monitorAt cfg .initial steps index) (S.eventAt steps index))
    (order : offset ≤ last) (within : last ≤ steps.length) : Nonempty (At start steps last) := by
  obtain ⟨count, rfl⟩ := Nat.exists_eq_add_of_le order
  have follow : ∀ count, offset + count ≤ steps.length → Nonempty (At start steps (offset + count)) := by
    intro count
    induction count with
    | zero => intro _; simpa only [Nat.add_zero] using Nonempty.intro entry
    | succ count ih =>
      intro within
      obtain ⟨point⟩ := ih (by omega)
      simpa only [Nat.add_assoc] using advance_at point budget trace actions (by omega)
  exact follow count within

theorem At.currentRouting (point : At start steps slot) : Routing point.current .standby := point.value.currentRouting

theorem At.healthy (point : At start steps slot) : (W.monitorAt cfg .initial steps slot).mode ≠ .invalid := by
  rw [point.value.finished]
  decide

end Netlib.Check.CampusTCPTwoTransferCurrentReverseAtTrace
