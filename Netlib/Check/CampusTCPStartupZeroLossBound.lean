import Netlib.Check.CampusTCPStartupDriveUntilComplete
import Netlib.Check.CampusTCPStartupCriticalStep
import Netlib.Check.CampusTCPStartupCriticalBounds
import Netlib.Check.CampusTCPStartupLossInterval
import Netlib.Theory.BoundedServiceRankAfter
import Netlib.Theory.BoundedServiceRestriction

/-!
# A zero-additional-loss startup extension

The interval retains the whole report's actual slots, demands, and service.
Its current clock bound supplies the rank budget at the starting slot.
-/

namespace Netlib.Check.CampusTCPStartupZeroLossBound

open Packet Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupServiceEnabled (PathsAligned)
open CampusTCPRecoveryStartupReceiveFields (PassiveTarget)

namespace E
export CampusTCPStartupTransferExecution (initial monitorAt pendingAt actions Serviced nextDemand)
end E
namespace P
export CampusTCPStartupMonitor (Monitor observe nextDemand)
end P
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S
namespace U
export CampusTCPStartupDriveUntilComplete (Completed)
end U
namespace R
export CampusTCPStartupCriticalRank (rank)
end R
namespace L
export CampusTCPStartupLossInterval (lossAt)
end L

variable {input : Input} {events : List CampusTCPModel.Event} {whole : Report input events}
variable {config : CampusTCPStartupTransferMonitor.Config}

def capacity (quantum slot : Nat) : Nat := CampusTCPRecoveryRoundMonitor.waitSlots quantum (1000 + quantum * slot) + 10

def extension (quantum bound start : Nat) : Nat := capacity quantum start * bound

noncomputable def score (config : CampusTCPStartupTransferMonitor.Config) (whole : Report input events) (slot : Nat) : Nat := by
  classical
  exact if U.Completed whole slot then 0 else
    match E.monitorAt config (E.initial config) whole.steps slot with
    | .startup monitor => R.rank config.transfer.quantum (S.stateAt input.initial whole.steps slot) monitor.protection
    | _ => 0

private theorem score_current (unfinished : ¬U.Completed whole slot)
    (ending : E.monitorAt config (E.initial config) whole.steps slot = .startup monitor) :
    score config whole slot = R.rank config.transfer.quantum (S.stateAt input.initial whole.steps slot) monitor.protection := by
  classical
  simp only [score, unfinished, ite_false, ending]

private structure SlotLaw (config : CampusTCPStartupTransferMonitor.Config) (whole : Report input events) (slot : Nat) where
  monitor : P.Monitor
  actual : Step input
  before : actual.before = S.stateAt input.initial whole.steps slot
  event : actual.event = S.eventAt whole.steps slot
  after : actual.result.state = S.stateAt input.initial whole.steps (slot + 1)
  current : E.monitorAt config (E.initial config) whole.steps slot = .startup monitor
  drive : monitor.mode = .drive
  next : E.monitorAt config (E.initial config) whole.steps (slot + 1) = .startup (P.observe config monitor actual)
  nextMode : (P.observe config monitor actual).mode = .drive
  protection : (P.observe config monitor actual).protection = CampusTCPStartupMonitor.advanceProtection config monitor actual
  law : CampusTCPStartupCriticalStep.Law config monitor actual

private theorem SlotLaw.score_before (value : SlotLaw config whole slot) (unfinished : ¬U.Completed whole slot) :
    score config whole slot = R.rank config.transfer.quantum value.actual.before value.monitor.protection := by
  rw [score_current unfinished value.current, ← value.before]

private theorem SlotLaw.score_after (value : SlotLaw config whole slot) (unfinished : ¬U.Completed whole (slot + 1)) :
    score config whole (slot + 1) = R.rank config.transfer.quantum value.actual.result.state
      (CampusTCPStartupMonitor.advanceProtection config value.monitor value.actual) := by
  rw [score_current unfinished value.next, value.protection, ← value.after]

private theorem SlotLaw.pending_before (value : SlotLaw config whole slot) :
    E.pendingAt config input.initial (E.initial config) whole.steps slot =
      (CampusTCPStartupSelection.demand config value.actual.before value.monitor.protection).map
        CampusTCPStartupTransferMonitor.Demand.startup := by
  simp only [E.pendingAt, value.current, E.nextDemand, P.nextDemand, value.drive]
  rw [← value.before]

private theorem SlotLaw.pending_after (value : SlotLaw config whole slot) :
    E.pendingAt config input.initial (E.initial config) whole.steps (slot + 1) =
      (CampusTCPStartupSelection.demand config value.actual.result.state
        (CampusTCPStartupMonitor.advanceProtection config value.monitor value.actual)).map
        CampusTCPStartupTransferMonitor.Demand.startup := by
  simp only [E.pendingAt, value.next, E.nextDemand, P.nextDemand, value.nextMode, value.protection]
  rw [← value.after]

private theorem SlotLaw.pending_case (value : SlotLaw config whole slot)
    (pending : E.pendingAt config input.initial (E.initial config) whole.steps slot = some demand) :
    ∃ event, CampusTCPStartupSelection.demand config value.actual.before value.monitor.protection = some event ∧
      demand = CampusTCPStartupTransferMonitor.Demand.startup event := by
  rw [value.pending_before] at pending
  cases selected : CampusTCPStartupSelection.demand config value.actual.before value.monitor.protection with
  | none => rw [selected] at pending; cases pending
  | some event => exact ⟨event, rfl, (Option.some.inj (by simpa only [selected, Option.map_some] using pending)).symm⟩

variable (profile : CampusTCPStartupNative.Profile (input.contextFor .primary)
  (beforeService input (S.stateAt input.initial whole.steps config.startup.preparation.length) .primary)
  input.zone (Handshake.outbound input.active config.startup.remote))

private theorem slot_law (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (paths : PathsAligned config profile) (valid : input.passive.Valid) (target : PassiveTarget profile.entry input.passive)
    (positive : 0 < config.transfer.quantum) (startMonitor : P.Monitor)
    (starting : E.monitorAt config (E.initial config) whole.steps start = .startup startMonitor) (startMode : startMonitor.mode = .drive)
    (within : last ≤ whole.steps.length) (equalLoss : L.lossAt whole start = L.lossAt whole last)
    (early : start ≤ slot) (late : slot < last) (unfinished : ¬U.Completed whole slot) :
    Nonempty (SlotLaw config whole slot) := by
  obtain ⟨monitor, current, drive⟩ := CampusTCPStartupDriveUntilComplete.drive_at profile prep actions paths valid target
    start startMonitor starting startMode early (by omega) unfinished
  obtain ⟨actual, found, before, event, after⟩ := CampusTCPSchedule.Trace.at whole.trace slot (by omega)
  have phases := CampusTCPStartupDriveUntilComplete.phases profile prep actions (by omega) monitor current drive unfinished
  have beforePhases : CampusTCPStartupSelection.phaseRank actual.before = 1 ∨
      CampusTCPStartupSelection.phaseRank actual.before = 2 ∨ CampusTCPStartupSelection.phaseRank actual.before = 3 := by
    simpa only [before] using phases
  have nodrop := CampusTCPStartupLossInterval.found_no_drop whole (by omega : start ≤ last) within equalLoss early late actual found
  have law := CampusTCPStartupCriticalStep.at_slot profile prep actions (by omega) current drive paths valid target actual found beforePhases positive nodrop
  obtain ⟨supported, passed, next, nextMode, protection⟩ := CampusTCPStartupDriveUntilComplete.step profile prep actions paths valid target
    (by omega : slot < whole.steps.length) monitor current drive (CampusTCPStartupDriveUntilComplete.incomplete unfinished (Nat.le_refl slot)) actual found
  exact ⟨⟨monitor, actual, before, event, after, current, drive, next, nextMode, protection, law⟩⟩

theorem complete (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (paths : PathsAligned config profile) (valid : input.passive.Valid) (target : PassiveTarget profile.entry input.passive)
    (positive : 0 < config.transfer.quantum)
    (service : E.Serviced config input.initial (E.initial config) whole.steps bound)
    (startMonitor : P.Monitor)
    (starting : E.monitorAt config (E.initial config) whole.steps start = .startup startMonitor) (startMode : startMonitor.mode = .drive)
    (within : start + extension config.transfer.quantum bound start ≤ whole.steps.length)
    (equalLoss : L.lossAt whole start = L.lossAt whole (start + extension config.transfer.quantum bound start)) :
    U.Completed whole (start + extension config.transfer.quantum bound start) := by
  classical
  let duration := extension config.transfer.quantum bound start
  let last := start + duration
  by_cases completed : U.Completed whole last
  · exact completed
  exfalso
  have unfinishedAt (slot : Nat) (inside : slot ≤ last) : ¬U.Completed whole slot :=
    fun earlier => completed (earlier.mono inside)
  have laws : ∀ inner, inner < duration → Nonempty (SlotLaw config whole (start + inner)) := by
    intro inner inside
    exact slot_law profile prep actions paths valid target positive startMonitor starting startMode
      within equalLoss (by omega) (by omega) (unfinishedAt _ (by omega))
  have restricted : Theory.BoundedServiceCheck.Serviced duration
      (fun inner => E.pendingAt config input.initial (E.initial config) whole.steps (start + inner))
      (fun inner => S.eventAt whole.steps (start + inner)) (CampusTCPStartupTransferMonitor.serves config) bound :=
    Theory.BoundedServiceRestriction.subinterval service within
  have nonincrease : ∀ inner, inner < duration → score config whole (start + (inner + 1)) ≤ score config whole (start + inner) := by
    intro inner inside
    obtain ⟨value⟩ := laws inner inside
    have beforeScore := value.score_before (unfinishedAt _ (by omega))
    have afterScore : score config whole (start + (inner + 1)) =
        R.rank config.transfer.quantum value.actual.result.state
          (CampusTCPStartupMonitor.advanceProtection config value.monitor value.actual) := by
      simpa only [Nat.add_assoc] using value.score_after (unfinishedAt _ (by omega))
    rw [beforeScore, afterScore]
    exact value.law.nonincrease
  have demand : ∀ inner, inner ≤ duration → 0 < score config whole (start + inner) →
      ∃ value, E.pendingAt config input.initial (E.initial config) whole.steps (start + inner) = some value := by
    intro inner inside active
    obtain ⟨monitor, ending, drive⟩ := CampusTCPStartupDriveUntilComplete.drive_at profile prep actions paths valid target
      start startMonitor starting startMode (count := start + inner) (by omega) (by omega) (unfinishedAt _ (by omega))
    obtain ⟨located⟩ := CampusTCPStartupCurrentAt.at_drive profile prep actions (by omega) ending drive
    have currentScore := score_current (slot := start + inner) (unfinishedAt _ (by omega)) ending
    have rankPositive : 0 < R.rank config.transfer.quantum (CampusTCPSchedule.Report.cut whole (start + inner) (by omega)).final monitor.protection := by
      rw [currentScore] at active
      exact active
    obtain ⟨event, selected⟩ := CampusTCPStartupCriticalDemandAt.at_pending located actions ending drive prep rankPositive
    change P.nextDemand config (S.stateAt input.initial whole.steps (start + inner)) monitor = some event at selected
    exact ⟨.startup event, by simp only [E.pendingAt, ending, E.nextDemand, selected, Option.map_some]⟩
  have persistent : ∀ inner, inner < duration → 0 < score config whole (start + inner) → ∀ value,
      score config whole (start + (inner + 1)) = score config whole (start + inner) →
      E.pendingAt config input.initial (E.initial config) whole.steps (start + inner) = some value →
      E.pendingAt config input.initial (E.initial config) whole.steps (start + (inner + 1)) = some value := by
    intro inner inside active demand equal pending
    obtain ⟨value⟩ := laws inner inside
    have beforeScore := value.score_before (unfinishedAt _ (by omega))
    have afterScore : score config whole (start + (inner + 1)) =
        R.rank config.transfer.quantum value.actual.result.state
          (CampusTCPStartupMonitor.advanceProtection config value.monitor value.actual) := by
      simpa only [Nat.add_assoc] using value.score_after (unfinishedAt _ (by omega))
    rw [beforeScore, afterScore] at equal
    obtain ⟨event, selected, rfl⟩ := value.pending_case pending
    have same := value.law.persistent equal
    have nextPending := value.pending_after
    rw [same, selected] at nextPending
    simpa only [Nat.add_assoc, Option.map_some] using nextPending
  have strict : ∀ inner, inner < duration → 0 < score config whole (start + inner) → ∀ value,
      E.pendingAt config input.initial (E.initial config) whole.steps (start + inner) = some value →
      CampusTCPStartupTransferMonitor.serves config value (S.eventAt whole.steps (start + inner)) = true →
      score config whole (start + (inner + 1)) < score config whole (start + inner) := by
    intro inner inside active demand pending served
    obtain ⟨value⟩ := laws inner inside
    obtain ⟨event, selected, rfl⟩ := value.pending_case pending
    have same : event = value.actual.event := (of_decide_eq_true served).trans value.event.symm
    have reduced := value.law.served (selected.trans (congrArg some same))
    have beforeScore := value.score_before (unfinishedAt _ (by omega))
    have afterScore : score config whole (start + (inner + 1)) =
        R.rank config.transfer.quantum value.actual.result.state
          (CampusTCPStartupMonitor.advanceProtection config value.monitor value.actual) := by
      simpa only [Nat.add_assoc] using value.score_after (unfinishedAt _ (by omega))
    rw [beforeScore, afterScore]
    exact reduced
  obtain ⟨startAt⟩ := CampusTCPStartupCurrentAt.at_drive profile prep actions (by omega) starting startMode
  have initialBound : score config whole start ≤ capacity config.transfer.quantum start := by
    rw [score_current (unfinishedAt _ (by omega)) starting]
    exact CampusTCPStartupCriticalBounds.Report.rank_at whole prep actions (by omega) startAt.value.connected startMonitor.protection
  have zero := Theory.BoundedServiceRank.zero_after (rank := fun inner => score config whole (start + inner)) restricted nonincrease demand persistent strict duration
    (by simpa only [Nat.add_zero, duration, extension] using Nat.mul_le_mul_right bound initialBound) (Nat.le_refl duration)
  obtain ⟨endMonitor, ending, drive⟩ := CampusTCPStartupDriveUntilComplete.drive_at profile prep actions paths valid target
    start startMonitor starting startMode (count := last) (by omega : start ≤ last) within completed
  have positiveEnd := CampusTCPStartupDriveUntilComplete.positive_rank profile prep actions within endMonitor ending drive completed
  have endScore := score_current completed ending
  change score config whole last = 0 at zero
  rw [endScore] at zero
  exact (Nat.ne_of_gt positiveEnd) zero

end Netlib.Check.CampusTCPStartupZeroLossBound
