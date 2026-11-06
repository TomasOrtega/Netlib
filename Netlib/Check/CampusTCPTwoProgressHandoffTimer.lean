import Netlib.Check.CampusTCPTwoProgressHandoffRTO

/-!
# Timer bounds at the same actual handoff cut

The retained deadline and clocked head bound the current wait.
No timer bound is asserted after all sender records retire.
-/

namespace Netlib.Check.CampusTCPTwoProgressHandoffTimer

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressPhaseBase
open CampusTCPTwoProgressSetup (config)
open CampusTCPTwoProgressEvidence (Evidence)
open CampusTCPTwoProgressHandoffRTO (PendingRTO cap)

namespace T
export CampusTCPTwoProgressTimer (remaining slots waitSlots)
end T

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : CampusTCPTwoProgressMonitor.Monitor}

def PendingTimer (initial : TwoWriteInitial cut sender gateway lower upper) (current : Cut input complete)
    (quantum retries span : Nat) : Prop :=
  ∀ recovery, (endpoint current.endpoints sender).recovery = some recovery → recovery.outstanding ≠ [] →
    (∀ target, CampusTCPTwoProgressMonitor.timerTarget recovery = some target →
      target ≤ recovery.now + 2 ^ retries * cap initial span) ∧
    T.remaining recovery ≤ 2 ^ retries * cap initial span ∧
    T.slots quantum recovery ≤ T.waitSlots quantum (2 ^ retries * cap initial span)

private theorem core_pending_timer {sent : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
    (core : Core initial native quantum allowance current monitor sent received) {retries span : Nat}
    (rto : PendingRTO initial current retries span) : PendingTimer initial current quantum retries span := by
  intro recovery runtime pending
  have bound := rto recovery runtime pending
  have same : recovery = core.live.senderFlight.recovery := Option.some.inj (runtime.symm.trans core.live.senderFlight.runtime)
  subst recovery
  refine ⟨?_, Nat.le_trans (CampusTCPTwoProgressTimerInvariant.remaining_le core) bound, ?_⟩
  · intro target selected
    exact Nat.le_trans (CampusTCPTwoProgressTimerInvariant.target_le core target selected) (Nat.add_le_add_left bound _)
  · exact Nat.le_trans (CampusTCPTwoProgressTimerInvariant.slots_le core) (CampusTCPRecoveryRoundMonitor.waitSlots_mono bound)

theorem evidence_pending_timer (value : Evidence initial native quantum allowance current monitor) {retries span : Nat}
    (rto : PendingRTO initial current retries span) : PendingTimer initial current quantum retries span := by
  cases value with
  | written value _ => exact core_pending_timer value.core rto
  | upper _ value _ => exact core_pending_timer value.core rto
  | active core _ => exact core_pending_timer core rto
  | ready core _ => exact core_pending_timer core rto
  | done value =>
    intro recovery runtime pending
    have same : recovery = value.completed.senderFlight.recovery :=
      Option.some.inj (runtime.symm.trans value.completed.senderFlight.runtime)
    have ledger := value.completed.senderFlight.ledger
    rw [← same] at ledger
    exact False.elim (pending ledger)

variable {suffix remaining : List Event} {steps : List (Step input)} {final : State input} {bound : Nat}

theorem trace_at (budget : allowance ≤ 2) (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : CampusTCPTwoProgressProgress.Actions initial native quantum allowance steps)
    (slot : Nat) (within : slot ≤ steps.length) :
    ∃ current : Cut input complete,
      ∃ _value : Evidence initial native quantum allowance current
        (CampusTCPTwoProgressMonitor.monitorAt (config initial native quantum allowance) .initial steps slot),
        current.report.final = CampusTCPSchedule.stateAt cut.report.final steps slot ∧
          PendingTimer initial current quantum allowance (slot * quantum) := by
  obtain ⟨current, value, same, rto⟩ := CampusTCPTwoProgressHandoffRTO.trace_at_allowance budget trace actions slot within
  exact ⟨current, value, same, evidence_pending_timer value rto⟩

theorem handoff_by (budget : allowance ≤ 2) (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : CampusTCPTwoProgressProgress.Actions initial native quantum allowance steps)
    (service : CampusTCPTwoProgressMonitor.Serviced (config initial native quantum allowance) cut.report.final .initial steps bound)
    (enough : 16 * bound ≤ steps.length) :
    ∃ current : Cut input complete,
      ∃ _value : Evidence initial native quantum allowance current
        (CampusTCPTwoProgressMonitor.monitorAt (config initial native quantum allowance) .initial steps (16 * bound)),
        current.report.final = CampusTCPSchedule.stateAt cut.report.final steps (16 * bound) ∧
          (CampusTCPTwoProgressMonitor.monitorAt (config initial native quantum allowance) .initial steps (16 * bound)).mode ≠ .originals ∧
          PendingTimer initial current quantum allowance ((16 * bound) * quantum) := by
  obtain ⟨current, value, same, mode, _, rto⟩ := CampusTCPTwoProgressHandoffRTO.handoff_by budget trace actions service enough
  exact ⟨current, value, same, mode, evidence_pending_timer value rto⟩

theorem handoff_by_checked (budget : allowance ≤ 2) (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : CampusTCPTwoProgressMonitor.actions (config initial native quantum allowance) cut.report.final .initial steps = true)
    (service : CampusTCPTwoProgressMonitor.check (config initial native quantum allowance) cut.report.final .initial steps bound = true)
    (enough : 16 * bound ≤ steps.length) :
    ∃ current : Cut input complete,
      ∃ _value : Evidence initial native quantum allowance current
        (CampusTCPTwoProgressMonitor.monitorAt (config initial native quantum allowance) .initial steps (16 * bound)),
        current.report.final = CampusTCPSchedule.stateAt cut.report.final steps (16 * bound) ∧
          (CampusTCPTwoProgressMonitor.monitorAt (config initial native quantum allowance) .initial steps (16 * bound)).mode ≠ .originals ∧
          PendingTimer initial current quantum allowance ((16 * bound) * quantum) :=
  handoff_by budget trace ((CampusTCPTwoProgressMonitor.actions_correct _ _ _ _).mp actions)
    ((CampusTCPTwoProgressMonitor.check_correct _ _ _ _ _).mp service) enough

end Netlib.Check.CampusTCPTwoProgressHandoffTimer
