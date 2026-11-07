import Netlib.Check.CampusTCPTwoTransferEvidenceTrace
import Netlib.Check.CampusTCPTwoTransferOriginalRankStep
import Netlib.Theory.BoundedServiceRank
import Netlib.Theory.BoundedServiceRestriction

/-!
# Bounded exit from the original transfer paths

The proof uses one supplied trace and its whole service condition.
Stopped prefixes derive evidence until the first exit from the original phase.
-/

namespace Netlib.Check.CampusTCPTwoTransferOriginalBounded

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)
open CampusTCPTwoTransferEvidenceHandoffTrace (At Finished)

namespace W
export CampusTCPTwoTransferMonitor (Monitor Allowed observe monitorAt nextDemand pendingAt serves Serviced actions check)
end W
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S
namespace R
export CampusTCPTwoTransferOriginalRank (rank initial_rank pending positive)
end R

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {steps : List (Step input)} {events remaining : List Event} {final : State input}
variable {slot bound : Nat}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

def rankAt (taskConfig : CampusTCPTwoTransferMonitor.Config) (state : State input) (steps : List (Step input)) (slot : Nat) : Nat :=
  R.rank (S.stateAt state steps slot) (W.monitorAt taskConfig .initial steps slot)

private theorem laws_at (point : At initial checks routing quantum allowance reverseLower reverseUpper steps slot)
    (budget : allowance ≤ 2) (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ index, index < steps.length → W.Allowed cfg (S.stateAt cut.report.final steps index)
      (W.monitorAt cfg .initial steps index) (S.eventAt steps index))
    (mode : (W.monitorAt cfg .initial steps slot).exchange.forward.mode = .originals) (inside : slot < steps.length) :
    rankAt cfg cut.report.final steps (slot + 1) ≤ rankAt cfg cut.report.final steps slot ∧
      (∀ demand, rankAt cfg cut.report.final steps (slot + 1) = rankAt cfg cut.report.final steps slot →
        W.pendingAt cfg cut.report.final .initial steps slot = some demand →
        W.pendingAt cfg cut.report.final .initial steps (slot + 1) = some demand) ∧
      (∀ demand, W.pendingAt cfg cut.report.final .initial steps slot = some demand →
        W.serves cfg demand (S.eventAt steps slot) = true →
        rankAt cfg cut.report.final steps (slot + 1) < rankAt cfg cut.report.final steps slot) := by
  obtain ⟨actual, found, before, event, after⟩ := CampusTCPSchedule.Trace.at trace slot inside
  have allowed : W.Allowed cfg point.current.report.final (W.monitorAt cfg .initial steps slot) actual.event := by
    rw [point.final, event]
    exact actions slot inside
  have observed : W.observe cfg (W.monitorAt cfg .initial steps slot) actual = W.monitorAt cfg .initial steps (slot + 1) :=
    (CampusTCPTwoTransferControlBound.monitorAt_next steps found).symm
  rcases point.evidence.step budget actual (before.trans point.final.symm) allowed with running | done
  · obtain ⟨advance⟩ := running
    have nonincrease := CampusTCPTwoTransferOriginalRankStep.nonincrease point.evidence advance.move allowed
    rw [advance.move.final, after, observed, point.final] at nonincrease
    refine ⟨nonincrease, ?_, ?_⟩
    · intro demand equal pending
      have same : R.rank advance.move.after.report.final (W.observe cfg (W.monitorAt cfg .initial steps slot) actual) =
          R.rank point.current.report.final (W.monitorAt cfg .initial steps slot) := by
        rw [advance.move.final, after, observed, point.final]
        exact equal
      have selected : W.nextDemand cfg point.current.report.final (W.monitorAt cfg .initial steps slot) = some demand := by
        rw [point.final]
        exact pending
      have retained := CampusTCPTwoTransferOriginalRankStep.persistent point.evidence mode advance.move allowed same demand selected
      rw [advance.move.final, after, observed] at retained
      exact retained
    · intro demand pending served
      have selected : W.nextDemand cfg point.current.report.final (W.monitorAt cfg .initial steps slot) = some demand := by
        rw [point.final]
        exact pending
      have strict := CampusTCPTwoTransferOriginalRankStep.served_strict point.evidence mode advance.move allowed demand selected
        (by rw [event]; exact served)
      rw [advance.move.final, after, observed, point.final] at strict
      exact strict
  · obtain ⟨read⟩ := done
    have impossible := read.value.needRead
    rw [mode] at impossible
    cases impossible

structure Exited (initial : TwoWriteInitial cut sender gateway lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (routing : Routing cut gateway)
    (quantum allowance : Nat) (reverseLower reverseUpper : List UInt8) (steps : List (Step input)) (slot : Nat) where
  point : At initial checks routing quantum allowance reverseLower reverseUpper steps slot
  nonoriginal : (W.monitorAt (config initial checks routing quantum allowance reverseLower reverseUpper) .initial steps slot).exchange.forward.mode ≠ .originals

def Exited.finished (value : Exited initial checks routing quantum allowance reverseLower reverseUpper steps slot) :
    Finished initial checks routing quantum allowance reverseLower reverseUpper steps slot :=
  ⟨value.point, value.point.evidence.nonoriginal_finished value.nonoriginal⟩

theorem Exited.standby_location (value : Exited initial checks routing quantum allowance reverseLower reverseUpper steps slot) :
    value.point.location = .standby := value.finished.standby_location

theorem Exited.standby_routing (value : Exited initial checks routing quantum allowance reverseLower reverseUpper steps slot) :
    Routing value.point.current .standby := value.finished.standby_routing

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

def boundSlots (bound : Nat) : Nat := 24 * bound

theorem exits_by (entry : At initial checks routing quantum allowance reverseLower reverseUpper steps 0)
    (budget : allowance ≤ 2) (trace : Trace input cut.report.final events steps final remaining)
    (actions : ∀ index, index < steps.length → W.Allowed cfg (S.stateAt cut.report.final steps index)
      (W.monitorAt cfg .initial steps index) (S.eventAt steps index))
    (service : W.Serviced cfg cut.report.final .initial steps bound) (enough : boundSlots bound ≤ steps.length) :
    ∃ slot, slot ≤ boundSlots bound ∧ Nonempty (Exited initial checks routing quantum allowance reverseLower reverseUpper steps slot) := by
  classical
  let deadline := boundSlots bound
  by_cases found : ∃ slot, slot ≤ deadline ∧ (W.monitorAt cfg .initial steps slot).exchange.forward.mode ≠ .originals
  · obtain ⟨slot, within, nonoriginal, first⟩ := first_within found
    have stopped : ∀ prior, 0 ≤ prior → prior < slot → (W.monitorAt cfg .initial steps prior).exchange.forward.mode = .originals := by
      intro prior _ before
      exact Classical.byContradiction (fun different => first prior before different)
    obtain ⟨point⟩ := CampusTCPTwoTransferEvidenceTrace.original_prefix entry budget trace actions (Nat.zero_le _) (by omega) stopped
    exact ⟨slot, within, ⟨⟨point, nonoriginal⟩⟩⟩
  · have originals : ∀ slot, slot ≤ deadline → (W.monitorAt cfg .initial steps slot).exchange.forward.mode = .originals := by
      intro slot inside
      exact Classical.byContradiction (fun different => found ⟨slot, inside, different⟩)
    have points : ∀ slot, slot ≤ deadline → Nonempty (At initial checks routing quantum allowance reverseLower reverseUpper steps slot) := by
      intro slot inside
      exact CampusTCPTwoTransferEvidenceTrace.original_prefix entry budget trace actions (Nat.zero_le _) (by omega)
        (fun prior _ before => originals prior (by omega))
    have restricted := Theory.BoundedServiceRestriction.prefix_service (count := deadline) service enough
    have nonincrease : ∀ slot, slot < deadline → rankAt cfg cut.report.final steps (slot + 1) ≤ rankAt cfg cut.report.final steps slot := by
      intro slot inside
      obtain ⟨point⟩ := points slot (by omega)
      exact (laws_at point budget trace actions (originals slot (by omega)) (by omega)).1
    have demand : ∀ slot, slot ≤ deadline → 0 < rankAt cfg cut.report.final steps slot →
        ∃ value, W.pendingAt cfg cut.report.final .initial steps slot = some value := by
      intro slot inside _
      obtain ⟨point⟩ := points slot inside
      obtain ⟨value, pending⟩ := R.pending point.evidence (originals slot inside)
      rw [point.final] at pending
      exact ⟨value, pending⟩
    have persistent : ∀ slot, slot < deadline → 0 < rankAt cfg cut.report.final steps slot → ∀ value,
        rankAt cfg cut.report.final steps (slot + 1) = rankAt cfg cut.report.final steps slot →
        W.pendingAt cfg cut.report.final .initial steps slot = some value →
        W.pendingAt cfg cut.report.final .initial steps (slot + 1) = some value := by
      intro slot inside _ value equal pending
      obtain ⟨point⟩ := points slot (by omega)
      exact (laws_at point budget trace actions (originals slot (by omega)) (by omega)).2.1 value equal pending
    have strict : ∀ slot, slot < deadline → 0 < rankAt cfg cut.report.final steps slot → ∀ value,
        W.pendingAt cfg cut.report.final .initial steps slot = some value →
        W.serves cfg value (S.eventAt steps slot) = true →
        rankAt cfg cut.report.final steps (slot + 1) < rankAt cfg cut.report.final steps slot := by
      intro slot inside _ value pending served
      obtain ⟨point⟩ := points slot (by omega)
      exact (laws_at point budget trace actions (originals slot (by omega)) (by omega)).2.2 value pending served
    have initialRank : rankAt cfg cut.report.final steps 0 = 24 := by
      simp only [rankAt, CampusTCPSchedule.stateAt_zero, CampusTCPTwoTransferMonitor.monitorAt_zero, R.initial_rank]
    have window : 0 + rankAt cfg cut.report.final steps 0 * bound ≤ deadline := by
      simp only [initialRank, Nat.zero_add, deadline, boundSlots, Nat.le_refl]
    have zero := Theory.BoundedServiceRank.zero_by_at restricted nonincrease demand persistent strict 0 window
    have finalZero : rankAt cfg cut.report.final steps deadline = 0 := by
      simpa only [initialRank, Nat.zero_add, deadline, boundSlots] using zero
    obtain ⟨point⟩ := points deadline (Nat.le_refl _)
    have positive := R.positive point.evidence (originals deadline (Nat.le_refl _))
    rw [point.final] at positive
    change 0 < rankAt cfg cut.report.final steps deadline at positive
    omega

theorem exits_by_checked (entry : At initial checks routing quantum allowance reverseLower reverseUpper steps 0)
    (budget : allowance ≤ 2) (trace : Trace input cut.report.final events steps final remaining)
    (actions : W.actions cfg cut.report.final .initial steps = true)
    (service : W.check cfg cut.report.final .initial steps bound = true) (enough : boundSlots bound ≤ steps.length) :
    ∃ slot, slot ≤ boundSlots bound ∧ Nonempty (Exited initial checks routing quantum allowance reverseLower reverseUpper steps slot) :=
  exits_by entry budget trace ((CampusTCPTwoTransferMonitor.actions_correct _ _ _ _).mp actions)
    ((CampusTCPTwoTransferMonitor.check_correct _ _ _ _ _).mp service) enough

theorem initial_exits_by
    (initial : TwoWriteInitial cut sender .primary lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (routing : Routing cut .primary)
    (quantum allowance : Nat) (reverseLower reverseUpper : List UInt8)
    (primaryEmpty : cut.report.final.outstanding .primary = 0)
    (targetEmpty : cut.report.final.standby.transport = Checkpoint.Gateway.initial)
    (targetNS : cut.report.final.standby.guard.source.ns = (input.deployment .standby).executionNS)
    (budget : allowance ≤ 2) (trace : Trace input cut.report.final events steps final remaining)
    (actions : W.actions (config initial checks routing quantum allowance reverseLower reverseUpper) cut.report.final .initial steps = true)
    (service : W.check (config initial checks routing quantum allowance reverseLower reverseUpper) cut.report.final .initial steps bound = true)
    (enough : boundSlots bound ≤ steps.length) :
    ∃ slot, slot ≤ boundSlots bound ∧ Nonempty (Exited initial checks routing quantum allowance reverseLower reverseUpper steps slot) := by
  let entry : At initial checks routing quantum allowance reverseLower reverseUpper steps 0 := {
    current := cut
    location := .primary
    evidence := by
      simpa only [CampusTCPTwoTransferMonitor.monitorAt_zero] using
        CampusTCPTwoTransferEvidence.Evidence.ofInitial initial checks routing quantum allowance reverseLower reverseUpper
          primaryEmpty targetEmpty targetNS
    final := (CampusTCPSchedule.stateAt_zero _ _).symm
    history := by simp only [List.take_zero, List.append_nil] }
  exact exits_by_checked entry budget trace actions service enough

end Netlib.Check.CampusTCPTwoTransferOriginalBounded
