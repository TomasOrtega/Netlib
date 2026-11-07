import Netlib.Check.CampusTCPTwoTransferRecoveryTrace
import Netlib.Check.CampusTCPTwoTransferRecoveryRankStep
import Netlib.Theory.BoundedServiceRankAfter
import Netlib.Theory.BoundedServiceRestriction

/-!
# Bounded forward read on the original transfer trace

The pending cap starts at the actual original exit.
One whole service condition bounds the later recovery and actual read.
-/

namespace Netlib.Check.CampusTCPTwoTransferRecoveryBounded

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)
open CampusTCPTwoTransferEvidenceTrace (ReadAt)
open CampusTCPTwoTransferRecoveryTrace (RecoveryAt)

namespace W
export CampusTCPTwoTransferMonitor (Allowed observe monitorAt nextDemand pendingAt serves Serviced actions check)
end W
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S
namespace R
export CampusTCPTwoTransferRecoveryRank (rank boundSlots evidence_positive pending evidence_rank_le)
end R

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance capacity : Nat} {reverseLower reverseUpper : List UInt8}
variable {steps : List (Step input)} {events remaining : List Event} {final : State input}
variable {start slot bound : Nat}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

def coarse (quantum allowance capacity : Nat) : Nat :=
  (allowance + 1) * CampusTCPTwoProgressTimer.waitSlots quantum (2 ^ allowance * capacity) + 8 * allowance + 7

def rankAt (taskConfig : CampusTCPTwoTransferMonitor.Config) (capacity allowance : Nat)
    (state : State input) (steps : List (Step input)) (slot : Nat) : Nat :=
  R.rank taskConfig (R.boundSlots taskConfig capacity allowance) allowance
    (S.stateAt state steps slot) (W.monitorAt taskConfig .initial steps slot)

private theorem laws_at (entry : RecoveryAt initial checks routing quantum allowance reverseLower reverseUpper capacity steps slot)
    (budget : allowance ≤ 2) (positive : 0 < quantum) (capacityPositive : 0 < capacity)
    (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ index, index < steps.length → W.Allowed cfg (S.stateAt cut.report.final steps index)
      (W.monitorAt cfg .initial steps index) (S.eventAt steps index)) (inside : slot < steps.length) :
    rankAt cfg capacity allowance cut.report.final steps (slot + 1) ≤ rankAt cfg capacity allowance cut.report.final steps slot ∧
      (∀ demand, rankAt cfg capacity allowance cut.report.final steps (slot + 1) = rankAt cfg capacity allowance cut.report.final steps slot →
        W.pendingAt cfg cut.report.final .initial steps slot = some demand →
        W.pendingAt cfg cut.report.final .initial steps (slot + 1) = some demand) ∧
      (∀ demand, W.pendingAt cfg cut.report.final .initial steps slot = some demand →
        W.serves cfg demand (S.eventAt steps slot) = true →
        rankAt cfg capacity allowance cut.report.final steps (slot + 1) < rankAt cfg capacity allowance cut.report.final steps slot) := by
  obtain ⟨actual, found, before, event, after⟩ := CampusTCPSchedule.Trace.at trace slot inside
  have allowed : W.Allowed cfg entry.point.current.report.final (W.monitorAt cfg .initial steps slot) actual.event := by
    rw [entry.point.final, event]
    exact actions slot inside
  have observed : W.observe cfg (W.monitorAt cfg .initial steps slot) actual = W.monitorAt cfg .initial steps (slot + 1) :=
    (CampusTCPTwoTransferControlBound.monitorAt_next steps found).symm
  have moves : Nonempty (Move entry.point.current actual) := by
    rcases entry.point.evidence.step budget actual (before.trans entry.point.final.symm) allowed with running | done
    · obtain ⟨advance⟩ := running
      exact ⟨advance.move⟩
    · obtain ⟨read⟩ := done
      exact ⟨read.value.value.move⟩
  obtain ⟨move⟩ := moves
  have nonincrease := CampusTCPTwoTransferRecoveryRankStep.nonincrease entry.point.evidence entry.nonoriginal
    entry.pendingCap budget positive capacityPositive move allowed
  rw [move.final, after, observed, entry.point.final] at nonincrease
  refine ⟨nonincrease, ?_, ?_⟩
  · intro demand equal pending
    have same : R.rank cfg (R.boundSlots cfg capacity allowance) allowance move.after.report.final
        (W.observe cfg (W.monitorAt cfg .initial steps slot) actual) =
        R.rank cfg (R.boundSlots cfg capacity allowance) allowance entry.point.current.report.final
          (W.monitorAt cfg .initial steps slot) := by
      rw [move.final, after, observed, entry.point.final]
      exact equal
    have selected : W.nextDemand cfg entry.point.current.report.final (W.monitorAt cfg .initial steps slot) = some demand := by
      rw [entry.point.final]
      exact pending
    have retained := CampusTCPTwoTransferRecoveryRankStep.persistent entry.point.evidence entry.nonoriginal
      entry.pendingCap budget positive capacityPositive move allowed same demand selected
    rw [move.final, after, observed] at retained
    exact retained
  · intro demand pending served
    have selected : W.nextDemand cfg entry.point.current.report.final (W.monitorAt cfg .initial steps slot) = some demand := by
      rw [entry.point.final]
      exact pending
    have strict := CampusTCPTwoTransferRecoveryRankStep.served_strict entry.point.evidence entry.nonoriginal
      entry.pendingCap budget positive capacityPositive move allowed demand selected (by rw [event]; exact served)
    rw [move.final, after, observed, entry.point.final] at strict
    exact strict

theorem read_from (entry : RecoveryAt initial checks routing quantum allowance reverseLower reverseUpper capacity steps start)
    (budget : allowance ≤ 2) (positive : 0 < quantum) (capacityPositive : 0 < capacity)
    (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ index, index < steps.length → W.Allowed cfg (S.stateAt cut.report.final steps index)
      (W.monitorAt cfg .initial steps index) (S.eventAt steps index))
    (service : W.Serviced cfg cut.report.final .initial steps bound)
    (enough : start + coarse quantum allowance capacity * bound ≤ steps.length) :
    ∃ slot, start ≤ slot ∧ slot < start + coarse quantum allowance capacity * bound ∧
      Nonempty (ReadAt initial checks routing quantum allowance reverseLower reverseUpper steps slot) := by
  classical
  let count := coarse quantum allowance capacity * bound
  let deadline := start + count
  by_cases found : ∃ slot, start ≤ slot ∧ slot < deadline ∧
      Nonempty (ReadAt initial checks routing quantum allowance reverseLower reverseUpper steps slot)
  · exact found
  · have stopped : ∀ prior, start ≤ prior → prior < deadline →
        ¬Nonempty (ReadAt initial checks routing quantum allowance reverseLower reverseUpper steps prior) := by
      intro prior order inside read
      exact found ⟨prior, order, inside, read⟩
    have points : ∀ offset, offset ≤ count →
        Nonempty (RecoveryAt initial checks routing quantum allowance reverseLower reverseUpper capacity steps (start + offset)) := by
      intro offset inside
      exact CampusTCPTwoTransferRecoveryTrace.stopped_prefix entry budget trace actions (by omega) (by omega)
        (fun prior order before => stopped prior order (by omega))
    let score := fun offset => rankAt cfg capacity allowance cut.report.final steps (start + offset)
    have restricted := Theory.BoundedServiceRestriction.subinterval (offset := start) (count := count) service enough
    have nonincrease : ∀ offset, offset < count → score (offset + 1) ≤ score offset := by
      intro offset inside
      obtain ⟨point⟩ := points offset (by omega)
      simpa only [score, Nat.add_assoc] using (laws_at point budget positive capacityPositive trace actions (by omega)).1
    have demand : ∀ offset, offset ≤ count → 0 < score offset →
        ∃ value, W.pendingAt cfg cut.report.final .initial steps (start + offset) = some value := by
      intro offset inside _
      obtain ⟨point⟩ := points offset inside
      obtain ⟨value, selected⟩ := R.pending point.point.evidence point.nonoriginal
      rw [point.point.final] at selected
      exact ⟨value, selected⟩
    have persistent : ∀ offset, offset < count → 0 < score offset → ∀ value, score (offset + 1) = score offset →
        W.pendingAt cfg cut.report.final .initial steps (start + offset) = some value →
        W.pendingAt cfg cut.report.final .initial steps (start + (offset + 1)) = some value := by
      intro offset inside _ value equal pending
      obtain ⟨point⟩ := points offset (by omega)
      have same : rankAt cfg capacity allowance cut.report.final steps (start + offset + 1) =
          rankAt cfg capacity allowance cut.report.final steps (start + offset) := by
        simpa only [score, Nat.add_assoc] using equal
      simpa only [Nat.add_assoc] using (laws_at point budget positive capacityPositive trace actions (by omega)).2.1 value same pending
    have strict : ∀ offset, offset < count → 0 < score offset → ∀ value,
        W.pendingAt cfg cut.report.final .initial steps (start + offset) = some value →
        W.serves cfg value (S.eventAt steps (start + offset)) = true → score (offset + 1) < score offset := by
      intro offset inside _ value pending served
      obtain ⟨point⟩ := points offset (by omega)
      simpa only [score, Nat.add_assoc] using (laws_at point budget positive capacityPositive trace actions (by omega)).2.2 value pending served
    have initialRank : score 0 ≤ coarse quantum allowance capacity := by
      have bounded := R.evidence_rank_le entry.point.evidence entry.nonoriginal entry.pendingCap
      rw [entry.point.final] at bounded
      simpa only [score, Nat.add_zero, rankAt, coarse, R.boundSlots,
        show (cfg).exchange.forward.quantum = quantum by rfl] using bounded
    have order : score 0 * bound ≤ count := Nat.mul_le_mul_right bound initialRank
    have zero := Theory.BoundedServiceRank.zero_after restricted nonincrease demand persistent strict count order (Nat.le_refl _)
    obtain ⟨point⟩ := points count (Nat.le_refl _)
    have positive := R.evidence_positive point.point.evidence (R.boundSlots cfg capacity allowance) point.nonoriginal
    rw [point.point.final] at positive
    change 0 < score count at positive
    omega

def capacityAt (initial : TwoWriteInitial cut sender gateway lower upper) (quantum bound : Nat) : Nat :=
  CampusTCPTwoTransferHandoffRTO.cap initial ((24 * bound) * quantum)

def boundSlots (initial : TwoWriteInitial cut sender gateway lower upper) (quantum allowance bound : Nat) : Nat :=
  24 * bound + coarse quantum allowance (capacityAt initial quantum bound) * bound

theorem forward_read_by
    (initial : TwoWriteInitial cut sender .primary lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (routing : Routing cut .primary)
    (quantum allowance : Nat) (reverseLower reverseUpper : List UInt8)
    (primaryEmpty : cut.report.final.outstanding .primary = 0)
    (targetEmpty : cut.report.final.standby.transport = Checkpoint.Gateway.initial)
    (targetNS : cut.report.final.standby.guard.source.ns = (input.deployment .standby).executionNS)
    (budget : allowance ≤ 2) (positive : 0 < quantum)
    (trace : Trace input cut.report.final events steps final remaining)
    (actions : W.actions (config initial checks routing quantum allowance reverseLower reverseUpper) cut.report.final .initial steps = true)
    (service : W.check (config initial checks routing quantum allowance reverseLower reverseUpper) cut.report.final .initial steps bound = true)
    (enough : boundSlots initial quantum allowance bound ≤ steps.length) :
    ∃ slot, slot < boundSlots initial quantum allowance bound ∧
      Nonempty (ReadAt initial checks routing quantum allowance reverseLower reverseUpper steps slot) := by
  have originalWithin : CampusTCPTwoTransferOriginalBounded.boundSlots bound ≤ steps.length := by
    unfold boundSlots at enough
    change 24 * bound ≤ steps.length
    omega
  obtain ⟨exitSlot, exitWithin, ⟨exit⟩⟩ := CampusTCPTwoTransferOriginalBounded.initial_exits_by initial checks routing
    quantum allowance reverseLower reverseUpper primaryEmpty targetEmpty targetNS budget trace actions service originalWithin
  let entry := RecoveryAt.ofExited exit exitWithin
  have capacityPositive := CampusTCPTwoTransferHandoffRTO.cap_positive initial ((24 * bound) * quantum)
  have room : exitSlot + coarse quantum allowance (capacityAt initial quantum bound) * bound ≤ steps.length := by
    change exitSlot ≤ 24 * bound at exitWithin
    unfold boundSlots at enough
    omega
  obtain ⟨slot, _, before, read⟩ := read_from entry budget positive capacityPositive trace
    ((CampusTCPTwoTransferMonitor.actions_correct _ _ _ _).mp actions)
    ((CampusTCPTwoTransferMonitor.check_correct _ _ _ _ _).mp service) room
  refine ⟨slot, ?_, read⟩
  change exitSlot ≤ 24 * bound at exitWithin
  change slot < exitSlot + coarse quantum allowance (capacityAt initial quantum bound) * bound at before
  unfold boundSlots
  omega

end Netlib.Check.CampusTCPTwoTransferRecoveryBounded
