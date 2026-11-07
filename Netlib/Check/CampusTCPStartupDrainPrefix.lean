import Netlib.Check.CampusTCPStartupDriveStepEnabled
import Netlib.Check.CampusTCPStartupDrainStep
import Netlib.Check.CampusTCPStartupCriticalDemandAt

/-!
# Actual drive prefixes after the handshake completes

Closure records a real finish event in the same report.
Before that event, the observed drive mode and complete phase persist.
-/

namespace Netlib.Check.CampusTCPStartupDrainPrefix

open Packet Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupServiceEnabled (PathsAligned)
open CampusTCPRecoveryStartupReceiveFields (PassiveTarget)

namespace E
export CampusTCPStartupTransferExecution (initial monitorAt actions actions_correct allowed observe)
end E
namespace M
export CampusTCPStartupMonitor (Monitor allowed observe)
end M
namespace P
export CampusTCPStartupSelection (phaseRank)
end P
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

variable {input : Input} {events : List CampusTCPModel.Event}

def FinishedSince (whole : Report input events) (start last : Nat) : Prop :=
  ∃ slot, start ≤ slot ∧ slot < last ∧ ∃ actual, whole.steps[slot]? = some actual ∧ actual.event = .finishStartup

theorem FinishedSince.mono (finished : FinishedSince whole start first) (order : first ≤ last) :
    FinishedSince whole start last := by
  obtain ⟨slot, early, late, actual, found, event⟩ := finished
  exact ⟨slot, early, by omega, actual, found, event⟩

theorem FinishedSince.not_start (whole : Report input events) : ¬FinishedSince whole start start := by
  rintro ⟨slot, early, late, _⟩
  omega

structure DriveAt (whole : Report input events) (config : CampusTCPStartupTransferMonitor.Config) (slot : Nat) where
  monitor : M.Monitor
  ending : E.monitorAt config (E.initial config) whole.steps slot = .startup monitor
  drive : monitor.mode = .drive
  complete : P.phaseRank (S.stateAt input.initial whole.steps slot) = 4

variable {whole : Report input events} {config : CampusTCPStartupTransferMonitor.Config} {slot start last : Nat}

variable (profile : CampusTCPStartupNative.Profile (input.contextFor .primary)
  (beforeService input (S.stateAt input.initial whole.steps config.startup.preparation.length) .primary)
  input.zone (Handshake.outbound input.active config.startup.remote))

theorem DriveAt.successor (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (paths : PathsAligned config profile) (valid : input.passive.Valid) (target : PassiveTarget profile.entry input.passive)
    (prior : DriveAt whole config slot) (inside : slot < whole.steps.length)
    (actual : Step input) (found : whole.steps[slot]? = some actual) (unfinished : actual.event ≠ .finishStartup) :
    Nonempty (DriveAt whole config (slot + 1)) := by
  obtain ⟨head, selected, before, eventAt, after⟩ := CampusTCPSchedule.Trace.at whole.trace slot inside
  have same : head = actual := Option.some.inj (selected.symm.trans found)
  subst head
  have within : slot ≤ whole.steps.length := Nat.le_of_lt inside
  obtain ⟨located⟩ := CampusTCPStartupCurrentAt.at_drive profile prep actions within prior.ending prior.drive
  have connected : actual.before.connection = .recovering located.current := by
    rw [before]
    exact located.value.connected
  have four : P.phaseRank (CampusTCPSchedule.Report.cut whole slot within).final = 4 := prior.complete
  obtain ⟨complete, client, server, phase⟩ :=
    CampusTCPStartupCriticalDemandAt.complete_of_four located.value.connected four
  have later := CampusTCPStartupDrainStep.Step.complete_phaseRank actual connected phase unfinished
  have permitted := (E.actions_correct _ _ _ _).mp actions slot inside
  rw [prior.ending] at permitted
  have allowed : M.allowed config actual.before prior.monitor actual.event = true := by
    simpa only [E.allowed, ← before, ← eventAt] using permitted
  obtain ⟨_, _, observed, mode⟩ := CampusTCPStartupDriveStepEnabled.nonfinish profile prep actions within
    prior.ending prior.drive paths valid target actual before allowed unfinished
  have next := CampusTCPStartupEntry.monitorAt_next config (E.initial config) whole.steps found
  rw [prior.ending, observed] at next
  exact ⟨⟨M.observe config prior.monitor actual, next, mode, by rw [← after]; exact later⟩⟩

theorem DriveAt.until_finish (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (paths : PathsAligned config profile) (valid : input.passive.Valid) (target : PassiveTarget profile.entry input.passive)
    (initial : DriveAt whole config start) (order : start ≤ last) (within : last ≤ whole.steps.length)
    (unfinished : ¬FinishedSince whole start last) : Nonempty (DriveAt whole config last) := by
  obtain ⟨count, rfl⟩ := Nat.exists_eq_add_of_le order
  induction count with
  | zero => simpa only [Nat.add_zero] using Nonempty.intro initial
  | succ count ih =>
    have priorWithin : start + count ≤ whole.steps.length := by omega
    have priorUnfinished : ¬FinishedSince whole start (start + count) := by
      intro closed
      exact unfinished (closed.mono (by omega))
    obtain ⟨prior⟩ := ih (by omega) priorWithin priorUnfinished
    obtain ⟨actual, found, _, _, _⟩ := CampusTCPSchedule.Trace.at whole.trace (start + count) (by omega)
    have notFinish : actual.event ≠ .finishStartup := by
      intro event
      exact unfinished ⟨start + count, by omega, by omega, actual, found, event⟩
    simpa only [Nat.add_assoc] using DriveAt.successor profile prep actions paths valid target prior (by omega) actual found notFinish

end Netlib.Check.CampusTCPStartupDrainPrefix
