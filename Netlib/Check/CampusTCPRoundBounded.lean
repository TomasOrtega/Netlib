import Netlib.Check.CampusTCPRoundProgress
import Netlib.Check.CampusTCPRoundServiceBound
import Netlib.Check.CampusTCPRoundMonitorRead

/-!
# Bounded completion on one actual campus suffix

The bound counts evaluated operation slots.
The action and service checks read the same stored steps as the monitor.
This first suffix permits clock slots and the selected packet actions.
-/

namespace Netlib.Check.CampusTCPRoundBounded

open CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRound (Cut)
namespace P
export CampusTCPRoundProgress (Invariant Completed adapter initial_invariant Completion)
end P
namespace R
export CampusTCPRoundMonitor (Monitor Action Allowed stateAt monitorAt nextAction)
end R
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S
namespace C
export CampusTCPRoundServiceBound (Serviced check actions pendingAt check_correct actions_correct)
end C

variable {input : Input} {events : List Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}
variable {initial : Initial report complete request} {native : NativeEnv initial}
variable {suffix remaining : List Event} {steps : List (Step input)} {final : State input} {bound : Nat}

def Actions (initial : Initial report complete request) (native : NativeEnv initial) (steps : List (Step input)) : Prop :=
  ∀ slot, slot < steps.length → R.Allowed (CampusTCPRoundPhaseBase.config initial native)
    (S.stateAt initial.state steps slot)
    (R.monitorAt (CampusTCPRoundPhaseBase.config initial native) CampusTCPRoundMonitor.Monitor.initial steps slot)
    (S.eventAt steps slot)

def execution (trace : Trace input initial.state suffix steps final remaining) (allowed : Actions initial native steps) :
    Theory.BoundedProgress.Prefix (P.adapter initial native).system :=
  CampusTCPRoundMonitor.Trace.guardedPrefix trace (CampusTCPRoundPhaseBase.config initial native)
    CampusTCPRoundMonitor.Monitor.initial allowed

theorem serviced (trace : Trace input initial.state suffix steps final remaining) (allowed : Actions initial native steps)
    (service : C.Serviced (CampusTCPRoundPhaseBase.config initial native) initial.state
      CampusTCPRoundMonitor.Monitor.initial steps bound) :
    Theory.BoundedProgress.Prefix.ServiceBound (adapter := P.adapter initial native) (execution trace allowed) bound := by
  intro start _ within demand pending persistent
  exact service start within demand pending persistent

theorem checked_service (trace : Trace input initial.state suffix steps final remaining) (allowed : Actions initial native steps)
    (checked : C.check (CampusTCPRoundPhaseBase.config initial native) initial.state
      CampusTCPRoundMonitor.Monitor.initial steps bound = true) :
    Theory.BoundedProgress.Prefix.ServiceBound (adapter := P.adapter initial native) (execution trace allowed) bound :=
  serviced trace allowed ((C.check_correct _ _ _ _ _).mp checked)

private theorem execution_initial (trace : Trace input initial.state suffix steps final remaining)
    (allowed : Actions initial native steps) :
    (P.adapter initial native).invariant ((execution trace allowed).state 0) := by
  change P.Invariant initial native
    (S.stateAt initial.state steps 0,
      R.monitorAt (CampusTCPRoundPhaseBase.config initial native) CampusTCPRoundMonitor.Monitor.initial steps 0)
  simpa only [CampusTCPSchedule.stateAt_zero, CampusTCPRoundMonitor.monitorAt_zero] using
    P.initial_invariant initial native

private theorem execution_rank (trace : Trace input initial.state suffix steps final remaining)
    (allowed : Actions initial native steps) : (P.adapter initial native).rank ((execution trace allowed).state 0) = 9 := by
  change (R.monitorAt (CampusTCPRoundPhaseBase.config initial native) CampusTCPRoundMonitor.Monitor.initial steps 0).rank = 9
  rw [CampusTCPRoundMonitor.monitorAt_zero]
  rfl

theorem completes_by (trace : Trace input initial.state suffix steps final remaining) (allowed : Actions initial native steps)
    (service : C.Serviced (CampusTCPRoundPhaseBase.config initial native) initial.state
      CampusTCPRoundMonitor.Monitor.initial steps bound) (enough : 9 * bound ≤ steps.length) :
    P.Completed initial native
      (R.stateAt (CampusTCPRoundPhaseBase.config initial native) initial.state CampusTCPRoundMonitor.Monitor.initial steps
        (9 * bound)) := by
  have rank := execution_rank trace allowed
  have within : 0 + (P.adapter initial native).rank ((execution trace allowed).state 0) * bound ≤
      (execution trace allowed).length := by
    rw [rank, Nat.zero_add]
    exact enough
  have done := Theory.BoundedProgress.Prefix.completes_by (adapter := P.adapter initial native)
    (execution trace allowed) (execution_initial trace allowed) (serviced trace allowed service) 0 (Nat.zero_le _) within
  rw [rank, Nat.zero_add] at done
  exact done

theorem completes_final (trace : Trace input initial.state suffix steps final remaining) (allowed : Actions initial native steps)
    (service : C.Serviced (CampusTCPRoundPhaseBase.config initial native) initial.state
      CampusTCPRoundMonitor.Monitor.initial steps bound) (enough : 9 * bound ≤ steps.length) :
    P.Completed initial native
      (final, steps.foldl (CampusTCPRoundMonitor.observe (CampusTCPRoundPhaseBase.config initial native))
        CampusTCPRoundMonitor.Monitor.initial) := by
  have rank := execution_rank trace allowed
  have later : 0 + (P.adapter initial native).rank ((execution trace allowed).state 0) * bound ≤ steps.length := by
    simpa only [rank, Nat.zero_add] using enough
  have done := Theory.BoundedProgress.Prefix.completes_after (adapter := P.adapter initial native)
    (execution trace allowed) (execution_initial trace allowed) (serviced trace allowed service) 0 (Nat.zero_le _)
    steps.length later (Nat.le_refl _)
  change P.Completed initial native
    (R.stateAt (CampusTCPRoundPhaseBase.config initial native) initial.state CampusTCPRoundMonitor.Monitor.initial steps steps.length) at done
  simpa only [CampusTCPRoundMonitor.stateAt, CampusTCPSchedule.Trace.last_state trace,
    CampusTCPRoundMonitor.monitorAt_length] using done

theorem completes_by_checked (trace : Trace input initial.state suffix steps final remaining)
    (allowed : C.actions (CampusTCPRoundPhaseBase.config initial native) initial.state
      CampusTCPRoundMonitor.Monitor.initial steps = true)
    (service : C.check (CampusTCPRoundPhaseBase.config initial native) initial.state
      CampusTCPRoundMonitor.Monitor.initial steps bound = true) (enough : 9 * bound ≤ steps.length) :
    P.Completed initial native
      (R.stateAt (CampusTCPRoundPhaseBase.config initial native) initial.state CampusTCPRoundMonitor.Monitor.initial steps
        (9 * bound)) :=
  completes_by trace ((C.actions_correct _ _ _ _).mp allowed) ((C.check_correct _ _ _ _ _).mp service) enough

theorem completes_final_checked (trace : Trace input initial.state suffix steps final remaining)
    (allowed : C.actions (CampusTCPRoundPhaseBase.config initial native) initial.state
      CampusTCPRoundMonitor.Monitor.initial steps = true)
    (service : C.check (CampusTCPRoundPhaseBase.config initial native) initial.state
      CampusTCPRoundMonitor.Monitor.initial steps bound = true) (enough : 9 * bound ≤ steps.length) :
    P.Completed initial native
      (final, steps.foldl (CampusTCPRoundMonitor.observe (CampusTCPRoundPhaseBase.config initial native))
        CampusTCPRoundMonitor.Monitor.initial) :=
  completes_final trace ((C.actions_correct _ _ _ _).mp allowed) ((C.check_correct _ _ _ _ _).mp service) enough

theorem completed_read {state : State input × R.Monitor} (completed : P.Completed initial native state) :
    ∃ current : Cut input complete, current.report.final = state.1 ∧
      ∃ actual ∈ current.report.steps,
        actual.event = .read .server request.bytes.length ∧ actual.result.read = request.bytes ∧
        (endpoint current.endpoints .client).core.sent = [] ∧
        ∃ recovery, (endpoint current.endpoints .client).recovery = some recovery ∧
          recovery.outstanding = [] ∧ recovery.deadline = none ∧ recovery.timeoutCount = 0 := by
  obtain ⟨current, final, ⟨done⟩⟩ := completed
  obtain ⟨empty, recovery, runtime, outstanding, deadline, count⟩ := done.retirement
  exact ⟨current, final, done.read.hop.actual, done.read_member, done.read_event, done.read_bytes,
    empty, recovery, runtime, outstanding, deadline, count⟩

theorem completed_retirement {state : State input × R.Monitor} (completed : P.Completed initial native state) :
    ∃ endpoints : Applications complete, state.1.connection = .application complete endpoints ∧
      (endpoint endpoints .client).core.sent = [] ∧
      ∃ recovery, (endpoint endpoints .client).recovery = some recovery ∧
        recovery.outstanding = [] ∧ recovery.deadline = none ∧ recovery.timeoutCount = 0 := by
  obtain ⟨current, final, ⟨done⟩⟩ := completed
  obtain ⟨empty, recovery, runtime, outstanding, deadline, count⟩ := done.retirement
  refine ⟨current.endpoints, ?_, empty, recovery, runtime, outstanding, deadline, count⟩
  rw [← final]
  exact current.connection

theorem completed_monitor {state : State input × R.Monitor} (completed : P.Completed initial native state) :
    state.2.phase = .done := by
  obtain ⟨current, final, ⟨done⟩⟩ := completed
  rw [done.placement.monitorEq]
  exact done.read.anchor.phaseEq

theorem read_by (trace : Trace input initial.state suffix steps final remaining) (allowed : Actions initial native steps)
    (service : C.Serviced (CampusTCPRoundPhaseBase.config initial native) initial.state
      CampusTCPRoundMonitor.Monitor.initial steps bound) (enough : 9 * bound ≤ steps.length) :
    ∃ actual ∈ steps.take (9 * bound), actual.event = .read .server request.bytes.length ∧
      actual.result.read = request.bytes := by
  have done := completed_monitor (completes_by trace allowed service enough)
  exact CampusTCPRoundMonitorRead.monitorAt_done_read (CampusTCPRoundPhaseBase.config initial native) steps (9 * bound) done

theorem read_by_checked (trace : Trace input initial.state suffix steps final remaining)
    (allowed : C.actions (CampusTCPRoundPhaseBase.config initial native) initial.state
      CampusTCPRoundMonitor.Monitor.initial steps = true)
    (service : C.check (CampusTCPRoundPhaseBase.config initial native) initial.state
      CampusTCPRoundMonitor.Monitor.initial steps bound = true) (enough : 9 * bound ≤ steps.length) :
    ∃ actual ∈ steps.take (9 * bound), actual.event = .read .server request.bytes.length ∧
      actual.result.read = request.bytes :=
  read_by trace ((C.actions_correct _ _ _ _).mp allowed) ((C.check_correct _ _ _ _ _).mp service) enough

theorem read_and_retirement_by (trace : Trace input initial.state suffix steps final remaining)
    (allowed : Actions initial native steps)
    (service : C.Serviced (CampusTCPRoundPhaseBase.config initial native) initial.state
      CampusTCPRoundMonitor.Monitor.initial steps bound) (enough : 9 * bound ≤ steps.length) :
    (∃ actual ∈ steps.take (9 * bound), actual.event = .read .server request.bytes.length ∧
      actual.result.read = request.bytes) ∧
    ∃ endpoints : Applications complete,
      (S.stateAt initial.state steps (9 * bound)).connection = .application complete endpoints ∧
      (endpoint endpoints .client).core.sent = [] ∧
      ∃ recovery, (endpoint endpoints .client).recovery = some recovery ∧
        recovery.outstanding = [] ∧ recovery.deadline = none ∧ recovery.timeoutCount = 0 :=
  ⟨read_by trace allowed service enough, completed_retirement (completes_by trace allowed service enough)⟩

end Netlib.Check.CampusTCPRoundBounded
