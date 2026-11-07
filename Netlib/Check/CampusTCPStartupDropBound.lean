import Netlib.Check.CampusTCPStartupProfileFacts
import Netlib.Check.CampusTCPReportLoss

/-!
# Startup losses spend the whole allowance

Every permitted startup drop checks the current custody count.
The bound uses actual drop records and does not count timer expirations.
-/

namespace Netlib.Check.CampusTCPStartupDropBound

open CampusTCPModel CampusTCPStartupProfile

namespace M
export CampusTCPStartupTransferMonitor (Config)
end M
namespace P
export CampusTCPStartupMonitor (Monitor allowed nextDemand)
end P
namespace E
export CampusTCPStartupTransferExecution (Monitor initial monitorAt actions actions_correct)
end E
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

variable {input : Input} {config : M.Config} {state : State input} {startup : P.Monitor} {id : Nat} {event : Event}

theorem allowed_drop (prep : Prep config.startup) (permitted : P.allowed config state startup (.dropPacket id) = true) :
    state.custody.dropped < config.transfer.lossAllowance := by
  cases mode : startup.mode with
  | preparation index => exact False.elim (preparation_allowed prep mode permitted)
  | opening => simp only [P.allowed, mode, P.nextDemand, Option.some.injEq, reduceCtorEq, decide_false, Bool.false_eq_true] at permitted
  | drive =>
    have guarded := permitted
    simp only [P.allowed, mode, CampusTCPStartupSelection.allowed, CampusTCPStartupSelection.dropAllowed,
      Bool.and_eq_true] at guarded
    exact of_decide_eq_true guarded.1
  | setup stage =>
    cases stage <;> simp only [P.allowed, mode, P.nextDemand, CampusTCPStartupMonitor.Setup.event,
      Option.some.injEq, reduceCtorEq, decide_false, Bool.false_eq_true] at permitted
  | data | invalid => simp only [P.allowed, mode, Bool.false_eq_true] at permitted

private theorem drop_event (selected : CampusTCPCustodyFacts.dropEvent event = true) :
    ∃ id, event = .dropPacket id := by
  cases event <;> simp only [CampusTCPCustodyFacts.dropEvent, Bool.false_eq_true] at selected
  exact ⟨_, rfl⟩

theorem Step.drop_bound (actual : Step input) (prep : Prep config.startup)
    (before : actual.before.custody.dropped ≤ config.transfer.lossAllowance)
    (permitted : P.allowed config actual.before startup actual.event = true) :
    actual.result.state.custody.dropped ≤ config.transfer.lossAllowance := by
  have count := CampusTCPCustodyFacts.Step.drop_count actual
  by_cases dropped : CampusTCPCustodyFacts.dropEvent actual.event = true
  · obtain ⟨id, event⟩ := drop_event dropped
    have strict := allowed_drop prep (by simpa only [event] using permitted)
    simp [dropped] at count
    omega
  · have quiet : CampusTCPCustodyFacts.dropEvent actual.event = false := by
      cases selected : CampusTCPCustodyFacts.dropEvent actual.event with
      | false => rfl
      | true => exact False.elim (dropped selected)
    simp [quiet] at count
    omega

variable {initial final : State input} {events remaining : List Event} {steps : List (Step input)}
variable {monitor : E.Monitor input} {count : Nat} {current : P.Monitor}

theorem Trace.drop_bound (trace : Trace input initial events steps final remaining) (prep : Prep config.startup)
    (actions : E.actions config initial monitor steps = true)
    (start : initial.custody.dropped ≤ config.transfer.lossAllowance)
    (within : count ≤ steps.length) (ending : E.monitorAt config monitor steps count = .startup current) :
    (S.stateAt initial steps count).custody.dropped ≤ config.transfer.lossAllowance := by
  induction count generalizing current with
  | zero => simpa only [CampusTCPSchedule.stateAt_zero] using start
  | succ count ih =>
    obtain ⟨prior, previous⟩ := CampusTCPStartupProfileFacts.monitorAt_startup_past ending (Nat.le_succ count)
    have bounded := ih (current := prior) (by omega) previous
    obtain ⟨actual, found, before, event, after⟩ := CampusTCPSchedule.Trace.at trace count (by omega)
    have permitted := (E.actions_correct _ _ _ _).mp actions count (by omega)
    rw [previous] at permitted
    have next := Step.drop_bound actual prep (by simpa only [before] using bounded)
      (by simpa only [CampusTCPStartupTransferExecution.allowed, ← before, ← event] using permitted)
    simpa only [after] using next

theorem Report.cut_drop_bound (report : Report input events) (prep : Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) report.steps = true)
    (within : count ≤ report.steps.length)
    (ending : E.monitorAt config (E.initial config) report.steps count = .startup current) :
    (CampusTCPSchedule.Report.cut report count within).final.custody.dropped ≤ config.transfer.lossAllowance := by
  apply Trace.drop_bound report.trace prep actions _ within ending
  change 0 ≤ config.transfer.lossAllowance
  exact Nat.zero_le _

theorem Report.cut_drop_count (report : Report input events) (prep : Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) report.steps = true)
    (within : count ≤ report.steps.length)
    (ending : E.monitorAt config (E.initial config) report.steps count = .startup current) :
    CampusTCPReportLoss.drops (report.steps.take count) ≤ config.transfer.lossAllowance := by
  have actual := Report.cut_drop_bound report prep actions within ending
  rw [CampusTCPReportLoss.Report.drop_count] at actual
  exact actual

theorem Report.cut_drop_ids (report : Report input events) (prep : Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) report.steps = true)
    (within : count ≤ report.steps.length)
    (ending : E.monitorAt config (E.initial config) report.steps count = .startup current) :
    (CampusTCPReportLoss.dropIDs (report.steps.take count)).length ≤ config.transfer.lossAllowance := by
  rw [CampusTCPReportLoss.dropIDs_length]
  exact Report.cut_drop_count report prep actions within ending

end Netlib.Check.CampusTCPStartupDropBound
