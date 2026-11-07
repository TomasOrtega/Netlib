import Netlib.Check.CampusTCPStartupEntry
import Netlib.Check.CampusTCPRecoveredActualSetup

/-!
# Six actual setup steps before the data entry

The monitor forces each immediate predecessor.
The resulting sequence is a literal interval of the same stored report.
-/

namespace Netlib.Check.CampusTCPStartupSetupInterval

open CampusTCPModel CampusTCPStartupEntry

namespace E
export CampusTCPStartupTransferExecution (initial monitorAt)
end E
namespace P
export CampusTCPStartupMonitor (Monitor)
end P
namespace M
export CampusTCPStartupTransferMonitor (Config)
end M
namespace A
export CampusTCPRecoveredActualSetup (Sequence)
end A
namespace S
export CampusTCPSchedule (stateAt)
end S

variable {input : Input} {events : List Event} {config : M.Config} {whole : Report input events} {slot : Nat}

structure Located (entry : Entry config whole slot) where
  start : Nat
  within : start ≤ whole.steps.length
  count : slot + 1 = start + 6
  drive : P.Monitor
  before : E.monitorAt config (E.initial config) whole.steps start = .startup drive
  mode : drive.mode = .drive
  sequence : A.Sequence (CampusTCPSchedule.Report.cut whole start within) (config.transfer.lower ++ config.transfer.upper)
  written : sequence.written = entry.actual
  slice : sequence.steps = CampusTCPTraceSlices.slice whole.steps start 6

private theorem slice_six {steps : List (Step input)} {start : Nat} {a b c d e f : Step input}
    (first : steps[start]? = some a) (second : steps[start + 1]? = some b)
    (third : steps[start + 2]? = some c) (fourth : steps[start + 3]? = some d)
    (fifth : steps[start + 4]? = some e) (sixth : steps[start + 5]? = some f) :
    CampusTCPTraceSlices.slice steps start 6 = [a, b, c, d, e, f] := by
  apply List.ext_getElem?
  intro index
  by_cases inside : index < 6
  · have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [CampusTCPTraceSlices.slice, List.getElem?_take, List.getElem?_drop] using first
    · simpa [CampusTCPTraceSlices.slice, List.getElem?_take, List.getElem?_drop] using second
    · simpa [CampusTCPTraceSlices.slice, List.getElem?_take, List.getElem?_drop] using third
    · simpa [CampusTCPTraceSlices.slice, List.getElem?_take, List.getElem?_drop] using fourth
    · simpa [CampusTCPTraceSlices.slice, List.getElem?_take, List.getElem?_drop] using fifth
    · simpa [CampusTCPTraceSlices.slice, List.getElem?_take, List.getElem?_drop] using sixth
  · have absent : ([a, b, c, d, e, f] : List (Step input))[index]? = none :=
      List.getElem?_eq_none_iff.mpr (by simp only [List.length_cons, List.length_nil]; omega)
    simp only [CampusTCPTraceSlices.slice, List.getElem?_take, inside, ite_false]
    exact absent.symm

theorem locate (entry : Entry config whole slot) : Nonempty (Located entry) := by
  obtain ⟨serverAck⟩ := predecessor .write (whole := whole) (Nat.le_of_lt entry.within) entry.before entry.fields.1
  obtain ⟨clientAck⟩ := predecessor .serverAck (whole := whole) (Nat.le_of_lt serverAck.within) serverAck.before serverAck.mode
  obtain ⟨serverRecovery⟩ := predecessor .clientAck (whole := whole) (Nat.le_of_lt clientAck.within) clientAck.before clientAck.mode
  obtain ⟨clientRecovery⟩ := predecessor .serverRecovery (whole := whole) (Nat.le_of_lt serverRecovery.within) serverRecovery.before serverRecovery.mode
  obtain ⟨finish⟩ := predecessor .clientRecovery (whole := whole) (Nat.le_of_lt clientRecovery.within) clientRecovery.before clientRecovery.mode
  have first : clientRecovery.index = finish.index + 1 := finish.successor
  have second : serverRecovery.index = finish.index + 2 := by
    have := clientRecovery.successor
    omega
  have third : clientAck.index = finish.index + 3 := by
    have := serverRecovery.successor
    omega
  have fourth : serverAck.index = finish.index + 4 := by
    have := clientAck.successor
    omega
  have fifth : slot = finish.index + 5 := by
    have := serverAck.successor
    omega
  let within : finish.index ≤ whole.steps.length := Nat.le_of_lt finish.within
  let sequence : A.Sequence (CampusTCPSchedule.Report.cut whole finish.index within)
      (config.transfer.lower ++ config.transfer.upper) := {
    finish := finish.actual
    finishBefore := finish.beforeState
    finishEvent := finish.event
    finishSupported := finish.supported
    clientRecovery := clientRecovery.actual
    clientRecoveryBefore := by rw [clientRecovery.beforeState, finish.afterState]
    clientRecoveryEvent := clientRecovery.event
    serverRecovery := serverRecovery.actual
    serverRecoveryBefore := by rw [serverRecovery.beforeState, clientRecovery.afterState]
    serverRecoveryEvent := serverRecovery.event
    clientAck := clientAck.actual
    clientAckBefore := by rw [clientAck.beforeState, serverRecovery.afterState]
    clientAckEvent := clientAck.event
    serverAck := serverAck.actual
    serverAckBefore := by rw [serverAck.beforeState, clientAck.afterState]
    serverAckEvent := serverAck.event
    written := entry.actual
    writtenBefore := by rw [entry.at.1, serverAck.afterState]
    writtenEvent := entry.fields.2.1 }
  refine ⟨⟨finish.index, within, by omega, finish.startup, finish.before, finish.mode, sequence, rfl, ?_⟩⟩
  dsimp only [sequence, CampusTCPRecoveredActualSetup.Sequence.steps]
  symm
  exact slice_six finish.selected (by simpa only [first] using clientRecovery.selected)
    (by simpa only [second] using serverRecovery.selected) (by simpa only [third] using clientAck.selected)
    (by simpa only [fourth] using serverAck.selected) (by simpa only [fifth] using entry.selected)

variable {entry : Entry config whole slot}

theorem Located.history (located : Located entry) :
    (CampusTCPSchedule.Report.cut whole located.start located.within).steps ++ located.sequence.steps =
      whole.steps.take (slot + 1) := by
  change whole.steps.take located.start ++ located.sequence.steps = _
  rw [located.slice, CampusTCPTraceSlices.slice, ← List.take_add, ← located.count]

theorem Located.final (located : Located entry) :
    located.sequence.written.result.state = S.stateAt input.initial whole.steps (slot + 1) := by
  rw [located.written]
  exact entry.at.2.2

end Netlib.Check.CampusTCPStartupSetupInterval
