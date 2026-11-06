import Netlib.Check.CampusTCPTwoProgressTimerInvariant
import Netlib.Check.CampusTCPTwoProgressSuffixAge
import Netlib.Check.CampusTCPTwoProgressOriginalTimed

/-!
# RTO bounds at the actual original-phase handoff

Actual suffix clocks bound the age in the retained RTO envelope.
The bound applies only while a sender record remains outstanding.
-/

namespace Netlib.Check.CampusTCPTwoProgressHandoffRTO

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressPhaseBase
open CampusTCPTwoProgressSetup (config)
open CampusTCPTwoProgressEvidence (Evidence)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : CampusTCPTwoProgressMonitor.Monitor}

def cap (initial : TwoWriteInitial cut sender gateway lower upper) (span : Nat) : Nat :=
  max initial.senderState.idle.recovery.rto (RTO.sampleCap initial.senderState.idle.recovery.estimator span)

def PendingRTO (initial : TwoWriteInitial cut sender gateway lower upper) (current : Cut input complete)
    (retries span : Nat) : Prop :=
  ∀ recovery, (endpoint current.endpoints sender).recovery = some recovery → recovery.outstanding ≠ [] →
    recovery.rto ≤ 2 ^ retries * cap initial span

theorem PendingRTO.retry_mono {first last span : Nat} (prior : PendingRTO initial current first span) (counts : first ≤ last) :
    PendingRTO initial current last span := by
  intro recovery runtime pending
  exact Nat.le_trans (prior recovery runtime pending)
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_of_le (by decide) counts))

private theorem core_pending_rto {sent : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
    (core : Core initial native quantum allowance current monitor sent received) (span : Nat)
    (clock : (endpoint current.endpoints sender).now ≤ (endpoint cut.endpoints sender).now + span) :
    PendingRTO initial current monitor.retries span := by
  intro recovery runtime pending
  have same : recovery = core.live.senderFlight.recovery := Option.some.inj (runtime.symm.trans core.live.senderFlight.runtime)
  subst recovery
  have ledger : sent.ledger ≠ [] := by rw [← core.live.senderFlight.ledger]; exact pending
  have bound := core.rtoPending ledger
  have now : core.live.senderFlight.recovery.now = (endpoint current.endpoints sender).now := by
    simp only [Endpoint.State.now, core.live.senderFlight.runtime, Option.map_some, Option.getD_some]
  have age : core.live.senderFlight.recovery.now - (endpoint cut.endpoints sender).now ≤ span := by omega
  exact Nat.le_trans bound (Nat.mul_le_mul_left _ (RTOEnvelope.cap_mono _ _ _ _ age))

theorem evidence_pending_rto (value : Evidence initial native quantum allowance current monitor) (span : Nat)
    (clock : (endpoint current.endpoints sender).now ≤ (endpoint cut.endpoints sender).now + span) :
    PendingRTO initial current monitor.retries span := by
  cases value with
  | written value _ => exact core_pending_rto value.core span clock
  | upper _ value _ => exact core_pending_rto value.core span clock
  | active core _ => exact core_pending_rto core span clock
  | ready core _ => exact core_pending_rto core span clock
  | done value =>
    intro recovery runtime pending
    have same : recovery = value.completed.senderFlight.recovery :=
      Option.some.inj (runtime.symm.trans value.completed.senderFlight.runtime)
    have ledger := value.completed.senderFlight.ledger
    rw [← same] at ledger
    exact False.elim (pending ledger)

theorem evidence_retry_bound (value : Evidence initial native quantum allowance current monitor) : monitor.retries ≤ allowance := by
  cases value with
  | written value _ => exact Nat.le_trans value.core.losses.count value.core.lossBound
  | upper _ value _ => exact Nat.le_trans value.core.losses.count value.core.lossBound
  | active core _ => exact Nat.le_trans core.losses.count core.lossBound
  | ready core _ => exact Nat.le_trans core.losses.count core.lossBound
  | done value => exact Nat.le_trans value.losses.count value.lossBound

variable {suffix remaining : List Event} {steps : List (Step input)} {final : State input} {bound : Nat}

theorem trace_at (budget : allowance ≤ 2) (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : CampusTCPTwoProgressProgress.Actions initial native quantum allowance steps)
    (slot : Nat) (within : slot ≤ steps.length) :
    ∃ current : Cut input complete,
      ∃ _value : Evidence initial native quantum allowance current
        (CampusTCPTwoProgressMonitor.monitorAt (config initial native quantum allowance) .initial steps slot),
        current.report.final = CampusTCPSchedule.stateAt cut.report.final steps slot ∧
          PendingRTO initial current
            (CampusTCPTwoProgressMonitor.monitorAt (config initial native quantum allowance) .initial steps slot).retries (slot * quantum) ∧
          (CampusTCPTwoProgressMonitor.monitorAt (config initial native quantum allowance) .initial steps slot).retries ≤ allowance := by
  obtain ⟨current, same, ⟨value⟩, clocks⟩ := CampusTCPTwoProgressSuffixAge.trace_cut_now trace actions budget slot within
  exact ⟨current, value, same, evidence_pending_rto value _ (clocks sender), evidence_retry_bound value⟩

theorem trace_at_allowance (budget : allowance ≤ 2) (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : CampusTCPTwoProgressProgress.Actions initial native quantum allowance steps)
    (slot : Nat) (within : slot ≤ steps.length) :
    ∃ current : Cut input complete,
      ∃ _value : Evidence initial native quantum allowance current
        (CampusTCPTwoProgressMonitor.monitorAt (config initial native quantum allowance) .initial steps slot),
        current.report.final = CampusTCPSchedule.stateAt cut.report.final steps slot ∧ PendingRTO initial current allowance (slot * quantum) := by
  obtain ⟨current, value, same, pending, retries⟩ := trace_at budget trace actions slot within
  exact ⟨current, value, same, pending.retry_mono retries⟩

theorem handoff_by (budget : allowance ≤ 2) (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : CampusTCPTwoProgressProgress.Actions initial native quantum allowance steps)
    (service : CampusTCPTwoProgressMonitor.Serviced (config initial native quantum allowance) cut.report.final .initial steps bound)
    (enough : 16 * bound ≤ steps.length) :
    ∃ current : Cut input complete,
      ∃ _value : Evidence initial native quantum allowance current
        (CampusTCPTwoProgressMonitor.monitorAt (config initial native quantum allowance) .initial steps (16 * bound)),
        current.report.final = CampusTCPSchedule.stateAt cut.report.final steps (16 * bound) ∧
          (CampusTCPTwoProgressMonitor.monitorAt (config initial native quantum allowance) .initial steps (16 * bound)).mode ≠ .originals ∧
          PendingRTO initial current
            (CampusTCPTwoProgressMonitor.monitorAt (config initial native quantum allowance) .initial steps (16 * bound)).retries ((16 * bound) * quantum) ∧
          PendingRTO initial current allowance ((16 * bound) * quantum) := by
  obtain ⟨current, same, ⟨value⟩, mode, clocks⟩ := CampusTCPTwoProgressOriginalTimed.handoff_by budget trace actions service enough
  have pending := evidence_pending_rto value _ (clocks sender)
  exact ⟨current, value, same, mode, pending, pending.retry_mono (evidence_retry_bound value)⟩

theorem handoff_by_checked (budget : allowance ≤ 2) (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : CampusTCPTwoProgressMonitor.actions (config initial native quantum allowance) cut.report.final .initial steps = true)
    (service : CampusTCPTwoProgressMonitor.check (config initial native quantum allowance) cut.report.final .initial steps bound = true)
    (enough : 16 * bound ≤ steps.length) :
    ∃ current : Cut input complete,
      ∃ _value : Evidence initial native quantum allowance current
        (CampusTCPTwoProgressMonitor.monitorAt (config initial native quantum allowance) .initial steps (16 * bound)),
        current.report.final = CampusTCPSchedule.stateAt cut.report.final steps (16 * bound) ∧
          (CampusTCPTwoProgressMonitor.monitorAt (config initial native quantum allowance) .initial steps (16 * bound)).mode ≠ .originals ∧
          PendingRTO initial current
            (CampusTCPTwoProgressMonitor.monitorAt (config initial native quantum allowance) .initial steps (16 * bound)).retries ((16 * bound) * quantum) ∧
          PendingRTO initial current allowance ((16 * bound) * quantum) :=
  handoff_by budget trace ((CampusTCPTwoProgressMonitor.actions_correct _ _ _ _).mp actions)
    ((CampusTCPTwoProgressMonitor.check_correct _ _ _ _ _).mp service) enough

end Netlib.Check.CampusTCPTwoProgressHandoffRTO
