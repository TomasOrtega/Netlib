import Netlib.Check.CampusTCPTwoTransferCurrentReverseStep
import Netlib.Check.CampusTCPTwoTransferEvidenceTrace

/-!
# The actual reverse write within its whole service window

Clock prefixes retain the selected read on the supplied trace.
The one whole service condition selects the same stored reverse write.
-/

namespace Netlib.Check.CampusTCPTwoTransferCurrentReverseBounded

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferEvidence (Evidence ReadAdvanced)
open CampusTCPTwoTransferPostRead (After)
open CampusTCPTwoTransferCurrentReverseGeometry (Started)
open CampusTCPTwoTransferLocatedCore (config)

namespace W
export CampusTCPTwoTransferMonitor (Monitor Allowed observe monitorAt pendingAt nextDemand Serviced)
end W
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut readBefore : Cut input complete} {sender : Actor} {gateway location : Gateway}
variable {lower upper : List UInt8} {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {readMonitor : W.Monitor} {readActual : Step input}
variable {evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper readBefore readMonitor location}
variable {forward : ReadAdvanced evidence readActual}
variable {steps : List (Step input)} {start slot last bound : Nat}
variable {events remaining : List Event} {final : State input}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

structure At (forward : ReadAdvanced evidence readActual) (steps : List (Step input)) (slot : Nat) where
  current : Cut input complete
  value : After forward current (W.monitorAt cfg .initial steps slot)
  final : current.report.final = S.stateAt cut.report.final steps slot
  history : current.report.steps = cut.report.steps ++ steps.take slot

structure WriteAt (forward : ReadAdvanced evidence readActual) (steps : List (Step input)) (slot : Nat) where
  point : At forward steps slot
  actual : Step input
  found : steps[slot]? = some actual
  start : Started point.value actual
  final : start.boundary.write.move.after.report.final = S.stateAt cut.report.final steps (slot + 1)
  history : start.boundary.write.move.after.report.steps = cut.report.steps ++ steps.take (slot + 1)

private theorem take_next {values : List α} {index : Nat} {value : α} (found : values[index]? = some value) :
    values.take (index + 1) = values.take index ++ [value] := by
  induction values generalizing index with
  | nil => simp at found
  | cons head rest ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found; subst value; rfl
    | succ index => simpa only [List.take_succ_cons, List.cons_append] using congrArg (List.cons head) (ih found)

def At.of_read (read : CampusTCPTwoTransferEvidenceTrace.ReadAt initial checks routing quantum allowance
    reverseLower reverseUpper steps slot) : At read.advance steps (slot + 1) where
  current := read.advance.value.finalCut
  value := by
    rw [CampusTCPTwoTransferControlBound.monitorAt_next steps read.found]
    exact CampusTCPTwoTransferPostRead.ofRead (forward := read.advance) read.advance
  final := read.final
  history := read.history

theorem WriteAt.after_mode (written : WriteAt forward steps slot) :
    (W.monitorAt cfg .initial steps (slot + 1)).exchange.mode = .reverse := by
  rw [CampusTCPTwoTransferControlBound.monitorAt_next steps written.found]
  exact written.start.boundary.reverse_mode

theorem advance_at
    (endpointReserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (gatewayReserve : CampusTCPTwoReverseGeometry.Initial initial reverseLower reverseUpper)
    (lowerNonempty : reverseLower ≠ []) (upperNonempty : reverseUpper ≠ [])
    (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ index, index < steps.length → W.Allowed cfg (S.stateAt cut.report.final steps index)
      (W.monitorAt cfg .initial steps index) (S.eventAt steps index))
    (point : At forward steps slot) (inside : slot < steps.length) :
    Nonempty (At forward steps (slot + 1)) ∨ Nonempty (WriteAt forward steps slot) := by
  obtain ⟨actual, found, before, event, after⟩ := CampusTCPSchedule.Trace.at trace slot inside
  have allowed : W.Allowed cfg point.current.report.final (W.monitorAt cfg .initial steps slot) actual.event := by
    rw [point.final, event]
    exact actions slot inside
  have observed : W.observe cfg (W.monitorAt cfg .initial steps slot) actual = W.monitorAt cfg .initial steps (slot + 1) :=
    (CampusTCPTwoTransferControlBound.monitorAt_next steps found).symm
  rcases CampusTCPTwoTransferCurrentReverseStep.needWrite_event point.value actual allowed with write | ⟨actor, millis, clock⟩
  · obtain ⟨started⟩ := CampusTCPTwoTransferCurrentReverseGeometry.start_actual point.value endpointReserve gatewayReserve
      lowerNonempty upperNonempty actual (before.trans point.final.symm) write
    exact .inr ⟨{
      point, actual, found, start := started
      final := started.boundary.write.move.final.trans after
      history := by rw [started.boundary.write.move.history, point.history, take_next found, List.append_assoc] }⟩
  · obtain ⟨clocked⟩ := CampusTCPTwoTransferPostRead.Step.clock point.value actual (before.trans point.final.symm) clock allowed
    exact .inl ⟨{
      current := clocked.move.after
      value := observed ▸ clocked.next
      final := clocked.move.final.trans after
      history := by rw [clocked.move.history, point.history, take_next found, List.append_assoc] }⟩

theorem stopped_prefix
    (endpointReserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (gatewayReserve : CampusTCPTwoReverseGeometry.Initial initial reverseLower reverseUpper)
    (lowerNonempty : reverseLower ≠ []) (upperNonempty : reverseUpper ≠ [])
    (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ index, index < steps.length → W.Allowed cfg (S.stateAt cut.report.final steps index)
      (W.monitorAt cfg .initial steps index) (S.eventAt steps index))
    (entry : At forward steps start) (order : start ≤ last) (within : last ≤ steps.length)
    (stopped : ∀ index, start ≤ index → index ≤ last →
      (W.monitorAt cfg .initial steps index).exchange.mode = .needWrite) : Nonempty (At forward steps last) := by
  obtain ⟨count, rfl⟩ := Nat.exists_eq_add_of_le order
  have follow : ∀ count, start + count ≤ steps.length →
      (∀ index, start ≤ index → index ≤ start + count →
        (W.monitorAt cfg .initial steps index).exchange.mode = .needWrite) →
      Nonempty (At forward steps (start + count)) := by
    intro count
    induction count with
    | zero => intro _ _; simpa only [Nat.add_zero] using Nonempty.intro entry
    | succ count ih =>
      intro within stopped
      obtain ⟨point⟩ := ih (by omega) (fun index after before => stopped index after (by omega))
      rcases advance_at endpointReserve gatewayReserve lowerNonempty upperNonempty trace actions point (by omega) with next | written
      · simpa only [Nat.add_assoc] using next
      · obtain ⟨written⟩ := written
        have mode := written.after_mode
        have same := stopped (start + count + 1) (by omega) (by omega)
        rw [mode] at same
        cases same
  exact follow count within stopped

theorem At.pending (point : At forward steps slot) :
    W.pendingAt cfg cut.report.final .initial steps slot =
      some (.exchange (.reverseWrite sender.other (reverseLower ++ reverseUpper))) := by
  have finished := point.value.finished
  have noDrain := CampusTCPTwoTransferControlObserve.noDrain_of_non_capture point.current.report.final
    (W.monitorAt cfg .initial steps slot) (by rw [finished]; decide)
  have control : CampusTCPTwoTransferMonitor.controlDemand (W.monitorAt cfg .initial steps slot) = none := by
    rw [CampusTCPTwoTransferMonitor.controlDemand, finished]
  unfold W.pendingAt
  rw [← point.final]
  simp only [W.nextDemand, finished, reduceCtorEq, decide_false, Bool.false_eq_true, ite_false,
    noDrain, control, CampusTCPTwoExchangeMonitor.nextDemand, point.value.needWrite, Option.map_some]
  rfl

theorem exits_by
    (endpointReserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (gatewayReserve : CampusTCPTwoReverseGeometry.Initial initial reverseLower reverseUpper)
    (lowerNonempty : reverseLower ≠ []) (upperNonempty : reverseUpper ≠ [])
    (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ index, index < steps.length → W.Allowed cfg (S.stateAt cut.report.final steps index)
      (W.monitorAt cfg .initial steps index) (S.eventAt steps index))
    (entry : At forward steps start)
    (service : W.Serviced cfg cut.report.final .initial steps bound)
    (enough : start + bound ≤ steps.length) :
    ∃ index, start ≤ index ∧ index ≤ start + bound ∧
      (W.monitorAt cfg .initial steps index).exchange.mode ≠ .needWrite := by
  by_cases exits : ∃ index, start ≤ index ∧ index ≤ start + bound ∧
      (W.monitorAt cfg .initial steps index).exchange.mode ≠ .needWrite
  · exact exits
  · have stays : ∀ index, start ≤ index → index ≤ start + bound →
        (W.monitorAt cfg .initial steps index).exchange.mode = .needWrite := by
      intro index after before
      by_cases mode : (W.monitorAt cfg .initial steps index).exchange.mode = .needWrite
      · exact mode
      · exact False.elim (exits ⟨index, after, before, mode⟩)
    have points (index : Nat) (after : start ≤ index) (before : index ≤ start + bound) : Nonempty (At forward steps index) :=
      stopped_prefix endpointReserve gatewayReserve lowerNonempty upperNonempty trace actions entry after (by omega)
        (fun selected afterSelected beforeSelected => stays selected afterSelected (by omega))
    let demand : CampusTCPTwoTransferMonitor.Demand := .exchange (.reverseWrite sender.other (reverseLower ++ reverseUpper))
    obtain ⟨offset, inside, served⟩ := service start enough demand entry.pending (by
      intro offset inside
      obtain ⟨point⟩ := points (start + offset) (by omega) (by omega)
      exact point.pending)
    obtain ⟨point⟩ := points (start + offset) (by omega) (by omega)
    obtain ⟨actual, found, before, event, after⟩ := CampusTCPSchedule.Trace.at trace (start + offset) (by omega)
    have selected : CampusTCPTwoTransferMonitor.serves cfg demand actual.event = true := by rw [event]; exact served
    have allowed : W.Allowed cfg point.current.report.final (W.monitorAt cfg .initial steps (start + offset)) actual.event := by
      rw [point.final, event]
      exact actions _ (by omega)
    rcases CampusTCPTwoTransferCurrentReverseStep.needWrite_event point.value actual allowed with write | ⟨actor, millis, clock⟩
    · obtain ⟨started⟩ := CampusTCPTwoTransferCurrentReverseGeometry.start_actual point.value endpointReserve gatewayReserve
        lowerNonempty upperNonempty actual (before.trans point.final.symm) write
      have reverse : (W.monitorAt cfg .initial steps (start + offset + 1)).exchange.mode = .reverse := by
        rw [CampusTCPTwoTransferControlBound.monitorAt_next steps found]
        exact started.boundary.reverse_mode
      have mode := stays (start + offset + 1) (by omega) (by omega)
      rw [reverse] at mode
      cases mode
    · rw [clock] at selected
      cases selected

private theorem first_exit
    (found : ∃ index, start ≤ index ∧ index ≤ start + bound ∧
      (W.monitorAt cfg .initial steps index).exchange.mode ≠ .needWrite) :
    ∃ index, start ≤ index ∧ index ≤ start + bound ∧
      (W.monitorAt cfg .initial steps index).exchange.mode ≠ .needWrite ∧
      ∀ prior, start ≤ prior → prior < index →
        (W.monitorAt cfg .initial steps prior).exchange.mode = .needWrite := by
  induction bound with
  | zero =>
    obtain ⟨index, after, before, exited⟩ := found
    have same : index = start := by omega
    subst index
    exact ⟨start, Nat.le_refl _, by omega, exited, by intro prior after before; omega⟩
  | succ bound ih =>
    by_cases earlier : ∃ index, start ≤ index ∧ index ≤ start + bound ∧
        (W.monitorAt cfg .initial steps index).exchange.mode ≠ .needWrite
    · obtain ⟨index, after, before, exited, prior⟩ := ih earlier
      exact ⟨index, after, by omega, exited, prior⟩
    · obtain ⟨index, after, before, exited⟩ := found
      have last : index = start + bound + 1 := by
        by_cases before : index ≤ start + bound
        · exact False.elim (earlier ⟨index, after, before, exited⟩)
        · omega
      refine ⟨index, after, before, exited, ?_⟩
      intro prior after before
      by_cases mode : (W.monitorAt cfg .initial steps prior).exchange.mode = .needWrite
      · exact mode
      · exact False.elim (earlier ⟨prior, after, by omega, mode⟩)

theorem write_by
    (endpointReserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (gatewayReserve : CampusTCPTwoReverseGeometry.Initial initial reverseLower reverseUpper)
    (lowerNonempty : reverseLower ≠ []) (upperNonempty : reverseUpper ≠ [])
    (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ index, index < steps.length → W.Allowed cfg (S.stateAt cut.report.final steps index)
      (W.monitorAt cfg .initial steps index) (S.eventAt steps index))
    (entry : At forward steps start)
    (service : W.Serviced cfg cut.report.final .initial steps bound)
    (enough : start + bound ≤ steps.length) :
    ∃ index, start ≤ index ∧ index < start + bound ∧ Nonempty (WriteAt forward steps index) := by
  have exits := exits_by endpointReserve gatewayReserve lowerNonempty upperNonempty trace actions entry service enough
  obtain ⟨exit, afterStart, within, exited, prior⟩ := first_exit exits
  have after : start < exit := by
    have mode := entry.value.needWrite
    by_cases positive : start < exit
    · exact positive
    · have same : exit = start := by omega
      exact False.elim (exited (same ▸ mode))
  obtain ⟨point⟩ := stopped_prefix endpointReserve gatewayReserve lowerNonempty upperNonempty trace actions entry
    (last := exit - 1) (by omega) (by omega) (fun index after before => prior index after (by omega))
  rcases advance_at endpointReserve gatewayReserve lowerNonempty upperNonempty trace actions point (by omega) with next | written
  · obtain ⟨next⟩ := next
    have mode := next.value.needWrite
    have same : exit - 1 + 1 = exit := by omega
    rw [same] at mode
    exact False.elim (exited mode)
  · exact ⟨exit - 1, by omega, by omega, written⟩

end Netlib.Check.CampusTCPTwoTransferCurrentReverseBounded
