import Netlib.Check.CampusTCPTwoProgressGatewayState

/-!
# Unique current lower and upper range records

The lower and upper positions differ by the nonempty lower size.
Equal current coverage therefore gives equal optional range records.
-/

namespace Netlib.Check.CampusTCPTwoProgressCoverage

variable {Meta : Type} {before first after : Theory.SparseCoverage.State Meta}
variable {finish : Nat} {lower upper : List UInt8}

theorem TwoRanges.unique (left : TwoRanges before first finish lower upper)
    (right : TwoRanges before after finish lower upper) (nonempty : lower ≠ [])
    (same : first.runs = after.runs) : left.lowerRun = right.lowerRun ∧ left.upperRun = right.upperRun := by
  rw [left.runs, right.runs, List.append_assoc, List.append_assoc] at same
  have rest := List.append_cancel_left same
  have positive := List.length_pos_iff.mpr nonempty
  have firstEq : left.lowerRun = right.lowerRun := by
    cases leftAt : left.lowerRun with
    | none =>
      cases rightAt : right.lowerRun with
      | none => rfl
      | some run =>
        have runFields := right.lowerFields run (by simp [rightAt])
        cases laterAt : left.upperRun with
        | none =>
          simp only [leftAt, rightAt, laterAt, Option.toList_none, Option.toList_some,
            List.nil_append, List.cons_append] at rest
          cases rest
        | some later =>
          have laterFields := left.upperFields later (by simp [laterAt])
          have heads : later = run := by
            simp only [leftAt, rightAt, laterAt, Option.toList_none, Option.toList_some,
              List.nil_append, List.cons_append] at rest
            exact (List.cons.inj rest).1
          have positions := congrArg (fun value : Theory.SparseCoverage.Run Meta => value.position) heads
          rw [laterFields.1, runFields.1] at positions
          omega
    | some run =>
      cases rightAt : right.lowerRun with
      | none =>
        have runFields := left.lowerFields run (by simp [leftAt])
        cases laterAt : right.upperRun with
        | none => simp only [leftAt, rightAt, laterAt, Option.toList_none, Option.toList_some,
            List.nil_append, List.cons_append, List.cons_ne_nil] at rest
        | some later =>
          have laterFields := right.upperFields later (by simp [laterAt])
          have heads : run = later := by
            simp only [leftAt, rightAt, laterAt, Option.toList_none, Option.toList_some,
              List.nil_append, List.cons_append] at rest
            exact (List.cons.inj rest).1
          have positions := congrArg (fun value : Theory.SparseCoverage.Run Meta => value.position) heads
          rw [runFields.1, laterFields.1] at positions
          omega
      | some other =>
        simp only [leftAt, rightAt, Option.toList_some, List.cons_append] at rest
        exact congrArg some (List.cons.inj rest).1
  have secondEq : left.upperRun = right.upperRun := by
    rw [firstEq] at rest
    have lists := List.append_cancel_left rest
    cases leftAt : left.upperRun with
    | none =>
      cases rightAt : right.upperRun with
      | none => rfl
      | some run =>
        simp only [leftAt, rightAt, Option.toList_none, Option.toList_some] at lists
        cases lists
    | some run =>
      cases rightAt : right.upperRun with
      | none =>
        simp only [leftAt, rightAt, Option.toList_none, Option.toList_some] at lists
        cases lists
      | some other =>
        simp only [leftAt, rightAt, Option.toList_some] at lists
        exact congrArg some (List.cons.inj lists).1
  exact ⟨firstEq, secondEq⟩

end Netlib.Check.CampusTCPTwoProgressCoverage

namespace Netlib.Check.CampusTCPTwoProgressGatewayState

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current next : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}

theorem View.ranges_same (before : View initial current) (after : View initial next)
    (same : beforeService input next.report.final gateway = beforeService input current.report.final gateway) :
    after.ranges.lowerRun = before.ranges.lowerRun ∧ after.ranges.upperRun = before.ranges.upperRun := by
  have phase := after.gateway.phase
  rw [same, before.gateway.phase] at phase
  have session : after.gateway.session = before.gateway.session := (Admission.Phase.data.inj phase).symm
  apply after.ranges.unique before.ranges initial.lowerNonempty
  rw [session]

end Netlib.Check.CampusTCPTwoProgressGatewayState
