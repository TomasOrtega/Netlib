import Netlib.Check.CampusTCPTwoExchangeComplete
import Netlib.Check.CampusTCPTwoProgressRecorded

/-!
# Stored exchange operation order

Both readers surround the same actual reverse write.
-/

namespace Netlib.Check.CampusTCPTwoExchangeComplete

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {reverseLower reverseUpper : List UInt8} {monitor : CampusTCPTwoExchangeMonitor.Monitor}

theorem Complete.reader_slots (value : Complete initial native quantum allowance reverseLower reverseUpper current monitor)
    {supplied : List (Step input)} (history : current.report.steps = cut.report.steps ++ supplied) :
    ∃ forwardSlot writeSlot reverseSlot,
      forwardSlot < writeSlot ∧ writeSlot < reverseSlot ∧ reverseSlot < supplied.length ∧
      supplied[forwardSlot]? = some value.forward.completed.reader ∧
      supplied[writeSlot]? = some value.actual ∧
      supplied[reverseSlot]? = some value.reverse.completed.reader := by
  have forwardMember := CampusTCPTwoProgressRecorded.reader_recorded value.forward value.forward.losses.steps
  have reverseMember := CampusTCPTwoProgressRecorded.reader_recorded value.reverse value.reverse.losses.steps
  obtain ⟨forwardSlot, forwardAt⟩ := List.mem_iff_getElem?.mp forwardMember
  obtain ⟨reverseSlot, reverseAt⟩ := List.mem_iff_getElem?.mp reverseMember
  have forwardBound := (List.getElem?_eq_some_iff.mp forwardAt).1
  have reverseBound := (List.getElem?_eq_some_iff.mp reverseAt).1
  rw [value.recorded_eq history]
  refine ⟨forwardSlot, value.forward.losses.suffix.length,
    value.forward.losses.suffix.length + 1 + reverseSlot, forwardBound, by omega, ?_, ?_, ?_, ?_⟩
  · simp only [Complete.recorded, CampusTCPTwoExchangeLoss.recorded, List.length_append,
      List.length_cons, List.length_nil]
    omega
  · change (value.forward.losses.suffix ++ [value.actual] ++ value.reverse.losses.suffix)[forwardSlot]? = _
    rw [List.getElem?_append_left (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
      List.getElem?_append_left forwardBound]
    exact forwardAt
  · change (value.forward.losses.suffix ++ [value.actual] ++ value.reverse.losses.suffix)[value.forward.losses.suffix.length]? = _
    rw [List.getElem?_append_left (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
      List.getElem?_append_right (Nat.le_refl _)]
    simp only [Nat.sub_self, List.getElem?_cons_zero]
  · change (value.forward.losses.suffix ++ [value.actual] ++ value.reverse.losses.suffix)[value.forward.losses.suffix.length + 1 + reverseSlot]? = _
    rw [List.getElem?_append_right (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)]
    have index : value.forward.losses.suffix.length + 1 + reverseSlot -
        (value.forward.losses.suffix ++ [value.actual]).length = reverseSlot := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [index]
    exact reverseAt

theorem Complete.reverse_write_event (value : Complete initial native quantum allowance reverseLower reverseUpper current monitor) :
    value.actual.event = .write sender.other (reverseLower ++ reverseUpper) :=
  value.start.boundary.write.event

theorem Complete.forward_read_event (value : Complete initial native quantum allowance reverseLower reverseUpper current monitor) :
    value.forward.completed.reader.event = .read sender.other (lower ++ upper).length :=
  value.forward.completed.event

theorem Complete.forward_read_bytes (value : Complete initial native quantum allowance reverseLower reverseUpper current monitor) :
    value.forward.completed.reader.result.read = lower ++ upper :=
  value.forward.completed.returned

theorem Complete.reverse_read_event (value : Complete initial native quantum allowance reverseLower reverseUpper current monitor) :
    value.reverse.completed.reader.event = .read sender (reverseLower ++ reverseUpper).length := by
  have other : sender.other.other = sender := by cases sender <;> rfl
  simpa only [other] using value.reverse.completed.event

theorem Complete.reverse_read_bytes (value : Complete initial native quantum allowance reverseLower reverseUpper current monitor) :
    value.reverse.completed.reader.result.read = reverseLower ++ reverseUpper :=
  value.reverse.completed.returned

end Netlib.Check.CampusTCPTwoExchangeComplete
