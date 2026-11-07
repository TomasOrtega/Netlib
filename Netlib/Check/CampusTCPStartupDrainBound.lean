import Netlib.Check.CampusTCPStartupDrainPrefix
import Netlib.Check.CampusTCPRecoveredTransferFrames
import Netlib.Theory.BoundedServiceRank
import Netlib.Theory.BoundedServiceRestriction

/-!
# A finite drain bound in the same whole report

Completed startup jobs decrease their actual queue potential.
The whole service condition also supplies the final finish event.
-/

namespace Netlib.Check.CampusTCPStartupDrainBound

open Packet Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupServiceEnabled (PathsAligned)
open CampusTCPRecoveryStartupReceiveFields (PassiveTarget)
open CampusTCPStartupDrainPrefix (DriveAt FinishedSince)

namespace E
export CampusTCPStartupTransferExecution (initial monitorAt actions actions_correct allowed observe nextDemand pendingAt Serviced)
end E
namespace M
export CampusTCPStartupMonitor (Monitor allowed observe nextDemand advanceProtection)
end M
namespace P
export CampusTCPStartupSelection (phaseRank demand allowed)
end P
namespace J
export CampusTCPStartupJobs (potential)
end J
namespace D
export CampusTCPStartupTransferMonitor (Demand serves)
end D
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

variable {input : Input} {events : List CampusTCPModel.Event} {whole : Report input events}
variable {config : CampusTCPStartupTransferMonitor.Config} {slot start : Nat}

def potentialAt (whole : Report input events) (slot : Nat) : Nat :=
  J.potential (S.stateAt input.initial whole.steps slot)

private theorem pending_eq (prior : DriveAt whole config slot) :
    E.pendingAt config input.initial (E.initial config) whole.steps slot =
      (P.demand config (S.stateAt input.initial whole.steps slot) prior.monitor.protection).map CampusTCPStartupTransferMonitor.Demand.startup := by
  simp only [E.pendingAt, E.nextDemand, prior.ending, M.nextDemand, prior.drive]

private theorem pending_exists (prior : DriveAt whole config slot) :
    ∃ demand, E.pendingAt config input.initial (E.initial config) whole.steps slot = some demand := by
  by_cases zero : potentialAt whole slot = 0
  · have selected := CampusTCPStartupDrainSelection.zero_demand (config := config)
      (held := prior.monitor.protection) prior.complete zero
    exact ⟨.startup .finishStartup, by rw [pending_eq prior, selected]; rfl⟩
  · obtain ⟨job, _, selected⟩ := CampusTCPStartupDrainSelection.positive_demand (config := config)
      (held := prior.monitor.protection) prior.complete (by change 0 < potentialAt whole slot; omega)
    exact ⟨.startup (CampusTCPStartupSelection.Job.event config job), by rw [pending_eq prior, selected]; rfl⟩

private structure StepLaw (whole : Report input events) (config : CampusTCPStartupTransferMonitor.Config) (slot : Nat) : Prop where
  nonincrease : potentialAt whole (slot + 1) ≤ potentialAt whole slot
  persistent : potentialAt whole (slot + 1) = potentialAt whole slot →
    E.pendingAt config input.initial (E.initial config) whole.steps (slot + 1) =
      E.pendingAt config input.initial (E.initial config) whole.steps slot
  strict : ∀ demand, E.pendingAt config input.initial (E.initial config) whole.steps slot = some demand →
    D.serves config demand (S.eventAt whole.steps slot) = true → potentialAt whole (slot + 1) < potentialAt whole slot

variable (profile : CampusTCPStartupNative.Profile (input.contextFor .primary)
  (beforeService input (S.stateAt input.initial whole.steps config.startup.preparation.length) .primary)
  input.zone (Handshake.outbound input.active config.startup.remote))

private theorem step_laws (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (paths : PathsAligned config profile) (valid : input.passive.Valid) (target : PassiveTarget profile.entry input.passive)
    (prior : DriveAt whole config slot) (inside : slot < whole.steps.length)
    (actual : Step input) (found : whole.steps[slot]? = some actual) (unfinished : actual.event ≠ .finishStartup) :
    StepLaw whole config slot := by
  obtain ⟨head, selected, before, eventAt, after⟩ := CampusTCPSchedule.Trace.at whole.trace slot inside
  have same : head = actual := Option.some.inj (selected.symm.trans found)
  subst head
  have within : slot ≤ whole.steps.length := Nat.le_of_lt inside
  let report := CampusTCPSchedule.Report.cut whole slot within
  obtain ⟨located⟩ := CampusTCPStartupCurrentAt.at_drive profile prep actions within prior.ending prior.drive
  have connected := located.value.connected
  obtain ⟨complete, client, server, phase⟩ :=
    CampusTCPStartupCriticalDemandAt.complete_of_four connected prior.complete
  have connectedBefore : actual.before.connection = .recovering located.current := by rw [before]; exact connected
  have later := CampusTCPStartupDrainStep.Step.complete_phaseRank actual connectedBefore phase unfinished
  have cold := CampusTCPStartupProfileFacts.Report.cut_cold_profile whole prep actions within prior.ending (by rw [prior.drive]; trivial)
  have packets := CampusTCPRecoveredTransferFrames.Report.packet_recovery report cold
  have tickets := CampusTCPRecoveredTransferFrames.Report.pending_recovery report cold
  have permitted := (E.actions_correct _ _ _ _).mp actions slot inside
  rw [prior.ending] at permitted
  have allowed : M.allowed config actual.before prior.monitor actual.event = true := by
    simpa only [E.allowed, ← before, ← eventAt] using permitted
  have permittedDrive : P.allowed config actual.before prior.monitor.protection actual.event = true := by
    simpa only [M.allowed, prior.drive] using allowed
  obtain ⟨supported, passed⟩ := CampusTCPStartupDriveStepEnabled.supported_passed profile prep actions within
    prior.ending prior.drive paths valid target actual before allowed
  have cutBefore : actual.before = report.final := before
  have nonincrease := CampusTCPStartupDrainStep.Step.allowed_nonincrease actual report cutBefore connected phase packets tickets permittedDrive
  have monitorNext : M.observe config prior.monitor actual = ⟨.drive, M.advanceProtection config prior.monitor actual⟩ := by
    simp only [M.observe, supported, passed, allowed, Bool.and_self, ↓reduceIte, prior.drive, unfinished]
  have next := CampusTCPStartupEntry.monitorAt_next config (E.initial config) whole.steps found
  rw [prior.ending] at next
  have nextMonitor : E.monitorAt config (E.initial config) whole.steps (slot + 1) =
      .startup ⟨.drive, M.advanceProtection config prior.monitor actual⟩ := by
    simpa only [E.observe, monitorNext, reduceCtorEq, ↓reduceIte] using next
  have oldPending : E.pendingAt config input.initial (E.initial config) whole.steps slot =
      (P.demand config actual.before prior.monitor.protection).map CampusTCPStartupTransferMonitor.Demand.startup := by
    rw [pending_eq prior, ← before]
  have newPending : E.pendingAt config input.initial (E.initial config) whole.steps (slot + 1) =
      (P.demand config actual.result.state (M.advanceProtection config prior.monitor actual)).map CampusTCPStartupTransferMonitor.Demand.startup := by
    simp only [E.pendingAt, nextMonitor, E.nextDemand, M.nextDemand]
    rw [← after]
  refine ⟨by simpa only [potentialAt, before, after] using nonincrease, ?_, ?_⟩
  · intro equal
    have samePotential : J.potential actual.result.state = J.potential actual.before := by
      simpa only [potentialAt, ← before, ← after] using equal
    have pendingSame : P.demand config actual.result.state (M.advanceProtection config prior.monitor actual) =
        P.demand config actual.before prior.monitor.protection := by
      by_cases positive : 0 < J.potential actual.before
      · exact CampusTCPStartupDrainStep.Step.equal_pending actual report cutBefore connected phase packets tickets
          prior.monitor permittedDrive positive samePotential
      · have zero : J.potential actual.before = 0 := by omega
        have afterZero : J.potential actual.result.state = 0 := by omega
        rw [CampusTCPStartupDrainSelection.zero_demand later afterZero,
          CampusTCPStartupDrainSelection.zero_demand (show P.phaseRank actual.before = 4 from by rw [before]; exact prior.complete) zero]
    rw [oldPending, newPending, pendingSame]
  · intro demand selected served
    cases selectedDemand : P.demand config actual.before prior.monitor.protection with
    | none => rw [oldPending, selectedDemand] at selected; cases selected
    | some event =>
      have same : CampusTCPStartupTransferMonitor.Demand.startup event = demand := by
        simpa only [oldPending, selectedDemand, Option.map_some, Option.some.injEq] using selected
      subst demand
      have eventEq : event = actual.event := of_decide_eq_true (by simpa only [D.serves, ← eventAt] using served)
      have selectedActual : P.demand config actual.before prior.monitor.protection = some actual.event :=
        selectedDemand.trans (congrArg some eventEq)
      by_cases positive : 0 < J.potential actual.before
      · have strict := CampusTCPStartupDrainStep.Step.demand_strict actual report cutBefore connected phase packets tickets
          positive selectedActual supported
        simpa only [potentialAt, before, after] using strict
      · have zero : J.potential actual.before = 0 := by omega
        have finish := CampusTCPStartupDrainSelection.zero_demand (config := config)
          (held := prior.monitor.protection) (show P.phaseRank actual.before = 4 from by rw [before]; exact prior.complete) zero
        have event : actual.event = .finishStartup := Option.some.inj (selectedActual.symm.trans finish)
        exact False.elim (unfinished event)

private theorem closed_by (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (service : E.Serviced config input.initial (E.initial config) whole.steps bound)
    (paths : PathsAligned config profile) (valid : input.passive.Valid) (target : PassiveTarget profile.entry input.passive)
    (initial : DriveAt whole config start)
    (available : start + (potentialAt whole start + 1) * bound ≤ whole.steps.length) :
    FinishedSince whole start (start + (potentialAt whole start + 1) * bound) := by
  classical
  apply Classical.byContradiction
  intro unfinished
  let length := (potentialAt whole start + 1) * bound
  let rank : Nat → Nat := fun offset => potentialAt whole (start + offset) + 1
  have live (offset : Nat) (inside : offset ≤ length) : Nonempty (DriveAt whole config (start + offset)) := by
    apply DriveAt.until_finish profile prep actions paths valid target initial (by omega) (by omega)
    intro closed
    exact unfinished (closed.mono (by omega))
  have laws (offset : Nat) (inside : offset < length) : StepLaw whole config (start + offset) := by
    obtain ⟨prior⟩ := live offset (by omega)
    obtain ⟨actual, found, _, _, _⟩ := CampusTCPSchedule.Trace.at whole.trace (start + offset) (by omega)
    apply step_laws profile prep actions paths valid target prior (by omega) actual found
    intro event
    exact unfinished ⟨start + offset, by omega, by omega, actual, found, event⟩
  have serviced : Theory.BoundedServiceCheck.Serviced length
      (fun offset => E.pendingAt config input.initial (E.initial config) whole.steps (start + offset))
      (fun offset => S.eventAt whole.steps (start + offset)) (D.serves config) bound :=
    Theory.BoundedServiceRestriction.subinterval service available
  have nonincrease : ∀ offset, offset < length → rank (offset + 1) ≤ rank offset := by
    intro offset inside
    have decrease := (laws offset inside).nonincrease
    simpa only [rank, Nat.add_assoc] using Nat.add_le_add_right decrease 1
  have demand : ∀ offset, offset ≤ length → 0 < rank offset →
      ∃ value, E.pendingAt config input.initial (E.initial config) whole.steps (start + offset) = some value := by
    intro offset inside _
    obtain ⟨prior⟩ := live offset inside
    exact pending_exists prior
  have persistent : ∀ offset, offset < length → 0 < rank offset → ∀ value,
      rank (offset + 1) = rank offset →
      E.pendingAt config input.initial (E.initial config) whole.steps (start + offset) = some value →
      E.pendingAt config input.initial (E.initial config) whole.steps (start + (offset + 1)) = some value := by
    intro offset inside _ value equal selected
    have equalPotential : potentialAt whole (start + offset + 1) = potentialAt whole (start + offset) := by
      simp only [rank, Nat.add_assoc] at equal ⊢
      omega
    have pending := (laws offset inside).persistent equalPotential
    simpa only [Nat.add_assoc] using pending.trans selected
  have strict : ∀ offset, offset < length → 0 < rank offset → ∀ value,
      E.pendingAt config input.initial (E.initial config) whole.steps (start + offset) = some value →
      D.serves config value (S.eventAt whole.steps (start + offset)) = true → rank (offset + 1) < rank offset := by
    intro offset inside _ value selected served
    have decrease := (laws offset inside).strict value selected served
    simpa only [rank, Nat.add_assoc] using Nat.add_lt_add_right decrease 1
  have within : rank 0 * bound ≤ length := by simp only [rank, length, Nat.add_zero, Nat.le_refl]
  have zero := Theory.BoundedServiceRank.zero_by serviced nonincrease demand persistent strict within
  have positive : 0 < rank (rank 0 * bound) := by dsimp only [rank]; omega
  omega

structure Finish (config : CampusTCPStartupTransferMonitor.Config) (whole : Report input events)
    (start deadline : Nat) where
  slot : Nat
  early : start ≤ slot
  bound : slot < deadline
  within : slot < whole.steps.length
  actual : Step input
  selected : whole.steps[slot]? = some actual
  event : actual.event = .finishStartup
  before : actual.before = S.stateAt input.initial whole.steps slot
  after : actual.result.state = S.stateAt input.initial whole.steps (slot + 1)
  monitor : M.Monitor
  ending : E.monitorAt config (E.initial config) whole.steps slot = .startup monitor
  drive : monitor.mode = .drive
  phase : P.phaseRank (S.stateAt input.initial whole.steps slot) = 4
  supported : actual.result.supported = true
  passed : actual.result.passed = true
  setup : E.monitorAt config (E.initial config) whole.steps (slot + 1) =
    .startup ⟨.setup .clientRecovery, none⟩

def Finish.weaken (value : Finish config whole start first) (order : first ≤ last) :
    Finish config whole start last :=
  ⟨value.slot, value.early, Nat.lt_of_lt_of_le value.bound order, value.within, value.actual, value.selected,
    value.event, value.before, value.after, value.monitor, value.ending, value.drive, value.phase,
    value.supported, value.passed, value.setup⟩

private theorem finish_of_closed (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (paths : PathsAligned config profile) (valid : input.passive.Valid) (target : PassiveTarget profile.entry input.passive)
    (initial : DriveAt whole config start) (within : deadline ≤ whole.steps.length)
    (closed : FinishedSince whole start deadline) : Nonempty (Finish config whole start deadline) := by
  classical
  have search : ∀ last, last ≤ whole.steps.length → FinishedSince whole start last →
      Nonempty (Finish config whole start last) := by
    intro last
    induction last with
    | zero =>
      rintro _ ⟨slot, _, late, _⟩
      omega
    | succ last ih =>
      intro available finished
      by_cases previous : FinishedSince whole start last
      · obtain ⟨found⟩ := ih (by omega) previous
        exact ⟨found.weaken (Nat.le_succ _)⟩
      · obtain ⟨slot, early, late, actual, found, event⟩ := finished
        have sameSlot : slot = last := by
          by_cases same : slot = last
          · exact same
          · exact False.elim (previous ⟨slot, early, by omega, actual, found, event⟩)
        subst slot
        obtain ⟨prior⟩ := DriveAt.until_finish profile prep actions paths valid target initial early (by omega) previous
        obtain ⟨head, selected, before, eventAt, after⟩ := CampusTCPSchedule.Trace.at whole.trace last (by omega)
        have same : head = actual := Option.some.inj (selected.symm.trans found)
        subst head
        have permitted := (E.actions_correct _ _ _ _).mp actions last (by omega)
        rw [prior.ending] at permitted
        have allowed : M.allowed config actual.before prior.monitor actual.event = true := by
          simpa only [E.allowed, ← before, ← eventAt] using permitted
        obtain ⟨supported, passed⟩ := CampusTCPStartupDriveStepEnabled.supported_passed profile prep actions (by omega)
          prior.ending prior.drive paths valid target actual before allowed
        have observed : M.observe config prior.monitor actual = ⟨.setup .clientRecovery, none⟩ := by
          simp only [M.observe, supported, passed, allowed, Bool.and_self, ↓reduceIte, prior.drive]
          rw [event]
          rfl
        have next := CampusTCPStartupEntry.monitorAt_next config (E.initial config) whole.steps found
        rw [prior.ending] at next
        refine ⟨⟨last, early, Nat.lt_succ_self _, by omega, actual, found, event, before, after,
          prior.monitor, prior.ending, prior.drive, prior.complete, supported, passed, ?_⟩⟩
        simpa only [E.observe, observed, reduceCtorEq, ↓reduceIte] using next
  exact search deadline within closed

theorem finish_by (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (service : E.Serviced config input.initial (E.initial config) whole.steps bound)
    (paths : PathsAligned config profile) (valid : input.passive.Valid) (target : PassiveTarget profile.entry input.passive)
    (initialMonitor : M.Monitor)
    (starting : E.monitorAt config (E.initial config) whole.steps start = .startup initialMonitor)
    (startMode : initialMonitor.mode = .drive)
    (complete : P.phaseRank (S.stateAt input.initial whole.steps start) = 4)
    (available : start + (potentialAt whole start + 1) * bound ≤ whole.steps.length) :
    Nonempty (Finish config whole start (start + (potentialAt whole start + 1) * bound)) := by
  let initial : DriveAt whole config start := ⟨initialMonitor, starting, startMode, complete⟩
  exact finish_of_closed profile prep actions paths valid target initial available
    (closed_by profile prep actions service paths valid target initial available)

theorem finish_by_budget (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (service : E.Serviced config input.initial (E.initial config) whole.steps bound)
    (paths : PathsAligned config profile) (valid : input.passive.Valid) (target : PassiveTarget profile.entry input.passive)
    (initialMonitor : M.Monitor)
    (starting : E.monitorAt config (E.initial config) whole.steps start = .startup initialMonitor)
    (startMode : initialMonitor.mode = .drive)
    (complete : P.phaseRank (S.stateAt input.initial whole.steps start) = 4)
    (queue : potentialAt whole start ≤ budget)
    (available : start + (budget + 1) * bound ≤ whole.steps.length) :
    Nonempty (Finish config whole start (start + (budget + 1) * bound)) := by
  have order : start + (potentialAt whole start + 1) * bound ≤ start + (budget + 1) * bound :=
    Nat.add_le_add_left (Nat.mul_le_mul_right bound (Nat.add_le_add_right queue 1)) start
  obtain ⟨found⟩ := finish_by profile prep actions service paths valid target initialMonitor starting startMode complete
    (Nat.le_trans order available)
  exact ⟨found.weaken order⟩

end Netlib.Check.CampusTCPStartupDrainBound
