import Netlib.Check.CampusTCPRecoveryRoundProgress
import Netlib.Check.CampusTCPRecoveryRoundServiceBound
import Netlib.Check.CampusTCPRecoveryRoundMonitorRead

/-!
# Bounded completion on one actual recovery suffix

The bound counts evaluated slots, including clocks, drops, and retries.
The read witness belongs to the supplied prefix of those same stored steps.
-/

namespace Netlib.Check.CampusTCPRecoveryRoundBounded

open CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRound (Cut)
namespace P
export CampusTCPRecoveryRoundProgress (Invariant Completed SuffixPassed adapter initial_invariant)
end P
namespace R
export CampusTCPRecoveryRoundMonitor (Monitor Allowed stateAt monitorAt observe waitSlots)
end R
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S
namespace C
export CampusTCPRecoveryRoundServiceBound (Serviced check actions pendingAt check_correct actions_correct)
end C

variable {input : Input} {events : List Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}
variable {initial : Initial report complete request} {native : NativeEnv initial} {quantum : Nat}
variable {suffix remaining : List Event} {steps : List (Step input)} {final : State input} {bound : Nat}

def initialRank (quantum : Nat) : Nat := 25 + R.waitSlots quantum 1000 + R.waitSlots quantum 2000

def boundSlots (quantum bound : Nat) : Nat := initialRank quantum * bound

theorem initialRank_ten : initialRank 10 = 325 := rfl

theorem boundSlots_ten_two : boundSlots 10 2 = 650 := rfl

def Actions (initial : Initial report complete request) (native : NativeEnv initial) (quantum : Nat)
    (steps : List (Step input)) : Prop :=
  ∀ slot, slot < steps.length → R.Allowed (CampusTCPRecoveryRoundPhaseBase.config initial native quantum)
    (S.stateAt initial.state steps slot)
    (R.monitorAt (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) CampusTCPRecoveryRoundMonitor.Monitor.initial steps slot)
    (S.eventAt steps slot)

def execution (positive : 0 < quantum) (trace : Trace input initial.state suffix steps final remaining)
    (allowed : Actions initial native quantum steps) :
    Theory.BoundedProgress.Prefix (P.adapter initial native quantum positive).system :=
  CampusTCPRecoveryRoundMonitor.Trace.guardedPrefix trace (CampusTCPRecoveryRoundPhaseBase.config initial native quantum)
    CampusTCPRecoveryRoundMonitor.Monitor.initial allowed

theorem serviced (positive : 0 < quantum) (trace : Trace input initial.state suffix steps final remaining)
    (allowed : Actions initial native quantum steps)
    (service : C.Serviced (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) initial.state
      CampusTCPRecoveryRoundMonitor.Monitor.initial steps bound) :
    Theory.BoundedProgress.Prefix.ServiceBound (adapter := P.adapter initial native quantum positive)
      (execution positive trace allowed) bound := by
  intro start _ within demand pending persistent
  exact service start within demand pending persistent

theorem check_service (positive : 0 < quantum) (trace : Trace input initial.state suffix steps final remaining)
    (allowed : Actions initial native quantum steps)
    (checked : C.check (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) initial.state
      CampusTCPRecoveryRoundMonitor.Monitor.initial steps bound = true) :
    Theory.BoundedProgress.Prefix.ServiceBound (adapter := P.adapter initial native quantum positive)
      (execution positive trace allowed) bound :=
  serviced positive trace allowed ((C.check_correct _ _ _ _ _).mp checked)

private theorem execution_initial (positive : 0 < quantum)
    (trace : Trace input initial.state suffix steps final remaining) (allowed : Actions initial native quantum steps) :
    (P.adapter initial native quantum positive).invariant ((execution positive trace allowed).state 0) := by
  change P.Invariant initial native quantum
    (S.stateAt initial.state steps 0,
      R.monitorAt (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) CampusTCPRecoveryRoundMonitor.Monitor.initial steps 0)
  simpa only [CampusTCPSchedule.stateAt_zero, CampusTCPRecoveryRoundMonitor.monitorAt_zero] using P.initial_invariant initial native quantum

theorem execution_rank (positive : 0 < quantum) (trace : Trace input initial.state suffix steps final remaining)
    (allowed : Actions initial native quantum steps) :
    (P.adapter initial native quantum positive).rank ((execution positive trace allowed).state 0) = initialRank quantum := by
  change (R.monitorAt (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) CampusTCPRecoveryRoundMonitor.Monitor.initial steps 0).rank
    (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) (S.stateAt initial.state steps 0) = initialRank quantum
  rw [CampusTCPRecoveryRoundMonitor.monitorAt_zero, CampusTCPRecoveryRoundMonitor.initial_rank]
  rfl

theorem completes_by (positive : 0 < quantum) (trace : Trace input initial.state suffix steps final remaining)
    (allowed : Actions initial native quantum steps)
    (service : C.Serviced (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) initial.state
      CampusTCPRecoveryRoundMonitor.Monitor.initial steps bound) (enough : boundSlots quantum bound ≤ steps.length) :
    P.Completed initial native quantum
      (R.stateAt (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) initial.state CampusTCPRecoveryRoundMonitor.Monitor.initial steps
        (boundSlots quantum bound)) := by
  have rank := execution_rank positive trace allowed
  have within : 0 + (P.adapter initial native quantum positive).rank ((execution positive trace allowed).state 0) * bound ≤
      (execution positive trace allowed).length := by
    rw [rank, Nat.zero_add]
    exact enough
  have done := Theory.BoundedProgress.Prefix.completes_by (adapter := P.adapter initial native quantum positive)
    (execution positive trace allowed) (execution_initial positive trace allowed)
    (serviced positive trace allowed service) 0 (Nat.zero_le _) within
  rw [rank, Nat.zero_add] at done
  exact done

theorem completes_final (positive : 0 < quantum) (trace : Trace input initial.state suffix steps final remaining)
    (allowed : Actions initial native quantum steps)
    (service : C.Serviced (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) initial.state
      CampusTCPRecoveryRoundMonitor.Monitor.initial steps bound) (enough : boundSlots quantum bound ≤ steps.length) :
    P.Completed initial native quantum
      (final, steps.foldl (R.observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum)) CampusTCPRecoveryRoundMonitor.Monitor.initial) := by
  have rank := execution_rank positive trace allowed
  have later : 0 + (P.adapter initial native quantum positive).rank ((execution positive trace allowed).state 0) * bound ≤
      steps.length := by
    simpa only [rank, Nat.zero_add, boundSlots] using enough
  have done := Theory.BoundedProgress.Prefix.completes_after (adapter := P.adapter initial native quantum positive)
    (execution positive trace allowed) (execution_initial positive trace allowed)
    (serviced positive trace allowed service) 0 (Nat.zero_le _) steps.length later (Nat.le_refl _)
  change P.Completed initial native quantum
    (R.stateAt (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) initial.state CampusTCPRecoveryRoundMonitor.Monitor.initial steps steps.length) at done
  simpa only [R.stateAt, CampusTCPSchedule.Trace.last_state trace, CampusTCPRecoveryRoundMonitor.monitorAt_length] using done

theorem completes_by_checked (positive : 0 < quantum)
    (trace : Trace input initial.state suffix steps final remaining)
    (allowed : C.actions (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) initial.state CampusTCPRecoveryRoundMonitor.Monitor.initial steps = true)
    (service : C.check (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) initial.state CampusTCPRecoveryRoundMonitor.Monitor.initial steps bound = true)
    (enough : boundSlots quantum bound ≤ steps.length) :
    P.Completed initial native quantum
      (R.stateAt (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) initial.state CampusTCPRecoveryRoundMonitor.Monitor.initial steps
        (boundSlots quantum bound)) :=
  completes_by positive trace ((C.actions_correct _ _ _ _).mp allowed) ((C.check_correct _ _ _ _ _).mp service) enough

theorem completes_final_checked (positive : 0 < quantum)
    (trace : Trace input initial.state suffix steps final remaining)
    (allowed : C.actions (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) initial.state CampusTCPRecoveryRoundMonitor.Monitor.initial steps = true)
    (service : C.check (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) initial.state CampusTCPRecoveryRoundMonitor.Monitor.initial steps bound = true)
    (enough : boundSlots quantum bound ≤ steps.length) :
    P.Completed initial native quantum
      (final, steps.foldl (R.observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum)) CampusTCPRecoveryRoundMonitor.Monitor.initial) :=
  completes_final positive trace ((C.actions_correct _ _ _ _).mp allowed) ((C.check_correct _ _ _ _ _).mp service) enough

theorem completed_done {state : State input × R.Monitor} (completed : P.Completed initial native quantum state) :
    ∃ current : Cut input complete, current.report.final = state.1 ∧ P.SuffixPassed initial current ∧
      ∃ retries, Nonempty (CampusTCPRecoveryRoundEvidence.Done initial current state.2 retries) := completed

theorem completed_read {state : State input × R.Monitor} (completed : P.Completed initial native quantum state) :
    ∃ current : Cut input complete, current.report.final = state.1 ∧ P.SuffixPassed initial current ∧
      ∃ actual ∈ current.report.steps,
        actual.event = .read .server request.bytes.length ∧ actual.result.read = request.bytes ∧
        (endpoint current.endpoints .client).core.sent = [] ∧
        ∃ recovery, (endpoint current.endpoints .client).recovery = some recovery ∧
          recovery.outstanding = [] ∧ recovery.deadline = none ∧ recovery.timeoutCount = 0 := by
  obtain ⟨current, final, passed, retries, ⟨done⟩⟩ := completed
  have retired := done.completed.retirement
  exact ⟨current, final, passed, done.completed.reader, done.completed.member, done.completed.event, done.completed.bytes,
    retired.sent, retired.recovery, retired.runtime, retired.outstanding, retired.deadline, retired.timeoutCount⟩

theorem completed_retirement {state : State input × R.Monitor} (completed : P.Completed initial native quantum state) :
    ∃ endpoints : Applications complete, state.1.connection = .application complete endpoints ∧
      (endpoint endpoints .client).core.sent = [] ∧
      ∃ recovery, (endpoint endpoints .client).recovery = some recovery ∧
        recovery.outstanding = [] ∧ recovery.deadline = none ∧ recovery.timeoutCount = 0 := by
  obtain ⟨current, final, _, retries, ⟨done⟩⟩ := completed
  have retired := done.completed.retirement
  refine ⟨current.endpoints, ?_, retired.sent, retired.recovery, retired.runtime,
    retired.outstanding, retired.deadline, retired.timeoutCount⟩
  rw [← final]
  exact current.connection

theorem completed_history {state : State input × R.Monitor} (completed : P.Completed initial native quantum state) :
    ∃ current : Cut input complete, current.report.final = state.1 ∧ P.SuffixPassed initial current ∧
      ∃ retries, ∃ done : CampusTCPRecoveryRoundEvidence.Done initial current state.2 retries,
        (applicationSteps current.endpoints .server).flatMap Protocol.TCP.ApplicationTrace.Step.releasedPayload = request.bytes ∧
        (applicationSteps current.endpoints .server).flatMap Protocol.TCP.ApplicationTrace.Step.readBytes = request.bytes ∧
        (applicationSteps current.endpoints .server).filter CampusTCPRoundPhaseHistory.nonemptyRead = [done.completed.operation] ∧
        ∃ operation ∈ applicationSteps current.endpoints .server,
          (applicationSteps current.endpoints .server).filter CampusTCPRecoveryRoundHistory.nonemptyRelease = [operation] ∧
          operation.releasedPayload = request.bytes := by
  obtain ⟨current, final, passed, retries, ⟨done⟩⟩ := completed
  exact ⟨current, final, passed, retries, done, done.completed.history.releaseStream, done.completed.history.readStream,
    done.completed.history.reads, done.completed.history.exact_release⟩

theorem completed_monitor {state : State input × R.Monitor} (completed : P.Completed initial native quantum state) :
    state.2.round.phase = .done := by
  obtain ⟨_, _, _, retries, ⟨done⟩⟩ := completed
  exact done.phaseEq

theorem read_by (positive : 0 < quantum) (trace : Trace input initial.state suffix steps final remaining)
    (allowed : Actions initial native quantum steps)
    (service : C.Serviced (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) initial.state
      CampusTCPRecoveryRoundMonitor.Monitor.initial steps bound) (enough : boundSlots quantum bound ≤ steps.length) :
    ∃ actual ∈ steps.take (boundSlots quantum bound), actual.event = .read .server request.bytes.length ∧
      actual.result.read = request.bytes := by
  have done := completed_monitor (completes_by positive trace allowed service enough)
  exact CampusTCPRecoveryRoundMonitorRead.monitorAt_done_read
    (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) steps (boundSlots quantum bound) done

theorem read_by_checked (positive : 0 < quantum) (trace : Trace input initial.state suffix steps final remaining)
    (allowed : C.actions (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) initial.state CampusTCPRecoveryRoundMonitor.Monitor.initial steps = true)
    (service : C.check (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) initial.state CampusTCPRecoveryRoundMonitor.Monitor.initial steps bound = true)
    (enough : boundSlots quantum bound ≤ steps.length) :
    ∃ actual ∈ steps.take (boundSlots quantum bound), actual.event = .read .server request.bytes.length ∧
      actual.result.read = request.bytes :=
  read_by positive trace ((C.actions_correct _ _ _ _).mp allowed) ((C.check_correct _ _ _ _ _).mp service) enough

theorem read_and_retirement_by (positive : 0 < quantum) (trace : Trace input initial.state suffix steps final remaining)
    (allowed : Actions initial native quantum steps)
    (service : C.Serviced (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) initial.state
      CampusTCPRecoveryRoundMonitor.Monitor.initial steps bound) (enough : boundSlots quantum bound ≤ steps.length) :
    (∃ actual ∈ steps.take (boundSlots quantum bound), actual.event = .read .server request.bytes.length ∧
      actual.result.read = request.bytes) ∧
    ∃ endpoints : Applications complete,
      (S.stateAt initial.state steps (boundSlots quantum bound)).connection = .application complete endpoints ∧
      (endpoint endpoints .client).core.sent = [] ∧
      ∃ recovery, (endpoint endpoints .client).recovery = some recovery ∧
        recovery.outstanding = [] ∧ recovery.deadline = none ∧ recovery.timeoutCount = 0 :=
  ⟨read_by positive trace allowed service enough,
    completed_retirement (completes_by positive trace allowed service enough)⟩

theorem completes_by_done (positive : 0 < quantum) (trace : Trace input initial.state suffix steps final remaining)
    (allowed : Actions initial native quantum steps)
    (service : C.Serviced (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) initial.state
      CampusTCPRecoveryRoundMonitor.Monitor.initial steps bound) (enough : boundSlots quantum bound ≤ steps.length) :
    ∃ current : Cut input complete, current.report.final = S.stateAt initial.state steps (boundSlots quantum bound) ∧
      P.SuffixPassed initial current ∧ ∃ retries,
        Nonempty (CampusTCPRecoveryRoundEvidence.Done initial current
          (R.monitorAt (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) CampusTCPRecoveryRoundMonitor.Monitor.initial steps
            (boundSlots quantum bound)) retries) :=
  completed_done (completes_by positive trace allowed service enough)

end Netlib.Check.CampusTCPRecoveryRoundBounded
