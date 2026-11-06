import Netlib.Check.CampusTCPGapProgressProgress
import Netlib.Check.CampusTCPGapProgressServiceBound
import Netlib.Check.CampusTCPGapProgressMonitorRead

/-!
# Bounded completion on the actual held-gap suffix

The bound counts evaluated slots, including clocks, drops, and retries.
The read occurs in the supplied prefix of those same stored steps.
-/

namespace Netlib.Check.CampusTCPGapProgressBounded

open CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPGapProgressStart (GapInitial NativeEnv)
open CampusTCPGapProgressSetup (config initialMonitor)
namespace P
export CampusTCPGapProgressProgress (Invariant Completed SuffixPassed adapter initial_invariant)
end P
namespace M
export CampusTCPGapProgressMonitor (Monitor Allowed stateAt monitorAt observe initialRank boundSlots)
end M
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S
namespace C
export CampusTCPGapProgressServiceBound (Serviced check actions check_correct actions_correct)
end C

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut : Cut input complete} {sender : Actor} {lower upper : List UInt8}
variable {initial : GapInitial cut sender lower upper} {native : NativeEnv cut initial.gateway.seed.entry}
variable {quantum allowance : Nat}
variable {suffix remaining : List Event} {steps : List (Step input)} {final : State input} {bound : Nat}

structure Basis (initial : GapInitial cut sender lower upper) (quantum allowance : Nat) where
  receiver : CampusTCPGapProgressReceiver.Geometry initial
  wire : CampusTCPGapProgressWire.Geometry initial
  positive : 0 < quantum
  budget : allowance ≤ 2

variable (basis : Basis initial quantum allowance)

def Actions (initial : GapInitial cut sender lower upper)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum allowance : Nat)
    (steps : List (Step input)) : Prop :=
  ∀ slot, slot < steps.length → M.Allowed (config initial native quantum allowance)
    (S.stateAt cut.report.final steps slot)
    (M.monitorAt (config initial native quantum allowance) (initialMonitor initial) steps slot)
    (S.eventAt steps slot)

def execution (trace : Trace input cut.report.final suffix steps final remaining)
    (allowed : Actions initial native quantum allowance steps) :
    Theory.BoundedProgress.Prefix (P.adapter initial native quantum allowance basis.wire basis.positive basis.budget).system :=
  CampusTCPGapProgressMonitor.Trace.guardedPrefix trace (config initial native quantum allowance) (initialMonitor initial) allowed

theorem serviced (trace : Trace input cut.report.final suffix steps final remaining)
    (allowed : Actions initial native quantum allowance steps)
    (service : C.Serviced (config initial native quantum allowance) cut.report.final (initialMonitor initial) steps bound) :
    Theory.BoundedProgress.Prefix.ServiceBound
      (adapter := P.adapter initial native quantum allowance basis.wire basis.positive basis.budget)
      (execution basis trace allowed) bound := by
  intro start _ within demand pending persistent
  exact service start within demand pending persistent

theorem check_service (trace : Trace input cut.report.final suffix steps final remaining)
    (allowed : Actions initial native quantum allowance steps)
    (checked : C.check (config initial native quantum allowance) cut.report.final (initialMonitor initial) steps bound = true) :
    Theory.BoundedProgress.Prefix.ServiceBound
      (adapter := P.adapter initial native quantum allowance basis.wire basis.positive basis.budget)
      (execution basis trace allowed) bound :=
  serviced basis trace allowed ((C.check_correct _ _ _ _ _).mp checked)

private theorem execution_initial (trace : Trace input cut.report.final suffix steps final remaining)
    (allowed : Actions initial native quantum allowance steps) :
    (P.adapter initial native quantum allowance basis.wire basis.positive basis.budget).invariant
      ((execution basis trace allowed).state 0) := by
  change P.Invariant initial native allowance
    (S.stateAt cut.report.final steps 0,
      M.monitorAt (config initial native quantum allowance) (initialMonitor initial) steps 0)
  simpa only [CampusTCPSchedule.stateAt_zero, CampusTCPGapProgressMonitor.monitorAt_zero] using
    P.initial_invariant initial native allowance basis.receiver basis.wire

theorem execution_rank (trace : Trace input cut.report.final suffix steps final remaining)
    (allowed : Actions initial native quantum allowance steps) :
    (P.adapter initial native quantum allowance basis.wire basis.positive basis.budget).rank
      ((execution basis trace allowed).state 0) = M.initialRank (config initial native quantum allowance) := by
  change (M.monitorAt (config initial native quantum allowance) (initialMonitor initial) steps 0).rank
    (config initial native quantum allowance) (S.stateAt cut.report.final steps 0) = _
  rw [CampusTCPGapProgressMonitor.monitorAt_zero]
  rfl

include basis in
theorem completes_by (trace : Trace input cut.report.final suffix steps final remaining)
    (allowed : Actions initial native quantum allowance steps)
    (service : C.Serviced (config initial native quantum allowance) cut.report.final (initialMonitor initial) steps bound)
    (enough : M.boundSlots (config initial native quantum allowance) bound ≤ steps.length) :
    P.Completed initial native allowance
      (M.stateAt (config initial native quantum allowance) cut.report.final (initialMonitor initial) steps
        (M.boundSlots (config initial native quantum allowance) bound)) := by
  have rank := execution_rank basis trace allowed
  have within : 0 + (P.adapter initial native quantum allowance basis.wire basis.positive basis.budget).rank
      ((execution basis trace allowed).state 0) * bound ≤ (execution basis trace allowed).length := by
    rw [rank, Nat.zero_add]
    exact enough
  have done := Theory.BoundedProgress.Prefix.completes_by
    (adapter := P.adapter initial native quantum allowance basis.wire basis.positive basis.budget)
    (execution basis trace allowed) (execution_initial basis trace allowed)
    (serviced basis trace allowed service) 0 (Nat.zero_le _) within
  rw [rank, Nat.zero_add] at done
  exact done

include basis in
theorem completes_final (trace : Trace input cut.report.final suffix steps final remaining)
    (allowed : Actions initial native quantum allowance steps)
    (service : C.Serviced (config initial native quantum allowance) cut.report.final (initialMonitor initial) steps bound)
    (enough : M.boundSlots (config initial native quantum allowance) bound ≤ steps.length) :
    P.Completed initial native allowance
      (final, steps.foldl (M.observe (config initial native quantum allowance)) (initialMonitor initial)) := by
  have rank := execution_rank basis trace allowed
  have later : 0 + (P.adapter initial native quantum allowance basis.wire basis.positive basis.budget).rank
      ((execution basis trace allowed).state 0) * bound ≤ steps.length := by
    simpa only [rank, Nat.zero_add, CampusTCPGapProgressMonitor.boundSlots] using enough
  have done := Theory.BoundedProgress.Prefix.completes_after
    (adapter := P.adapter initial native quantum allowance basis.wire basis.positive basis.budget)
    (execution basis trace allowed) (execution_initial basis trace allowed)
    (serviced basis trace allowed service) 0 (Nat.zero_le _) steps.length later (Nat.le_refl _)
  change P.Completed initial native allowance
    (M.stateAt (config initial native quantum allowance) cut.report.final (initialMonitor initial) steps steps.length) at done
  simpa only [M.stateAt, CampusTCPSchedule.Trace.last_state trace, CampusTCPGapProgressMonitor.monitorAt_length] using done

include basis in
theorem completes_by_checked (trace : Trace input cut.report.final suffix steps final remaining)
    (allowed : C.actions (config initial native quantum allowance) cut.report.final (initialMonitor initial) steps = true)
    (service : C.check (config initial native quantum allowance) cut.report.final (initialMonitor initial) steps bound = true)
    (enough : M.boundSlots (config initial native quantum allowance) bound ≤ steps.length) :
    P.Completed initial native allowance
      (M.stateAt (config initial native quantum allowance) cut.report.final (initialMonitor initial) steps
        (M.boundSlots (config initial native quantum allowance) bound)) :=
  completes_by basis trace ((C.actions_correct _ _ _ _).mp allowed) ((C.check_correct _ _ _ _ _).mp service) enough

include basis in
theorem completes_final_checked (trace : Trace input cut.report.final suffix steps final remaining)
    (allowed : C.actions (config initial native quantum allowance) cut.report.final (initialMonitor initial) steps = true)
    (service : C.check (config initial native quantum allowance) cut.report.final (initialMonitor initial) steps bound = true)
    (enough : M.boundSlots (config initial native quantum allowance) bound ≤ steps.length) :
    P.Completed initial native allowance
      (final, steps.foldl (M.observe (config initial native quantum allowance)) (initialMonitor initial)) :=
  completes_final basis trace ((C.actions_correct _ _ _ _).mp allowed) ((C.check_correct _ _ _ _ _).mp service) enough

theorem completed_done {state : State input × M.Monitor} (completed : P.Completed initial native allowance state) :
    ∃ current : Cut input complete, current.report.final = state.1 ∧ P.SuffixPassed cut current ∧
      ∃ retries, Nonempty (CampusTCPGapProgressEvidence.Done initial allowance current state.2 retries) :=
  CampusTCPGapProgressProgress.completed_done completed

theorem completed_retirement {state : State input × M.Monitor} (completed : P.Completed initial native allowance state) :
    ∃ endpoints : Applications complete, state.1.connection = .application complete endpoints ∧
      (endpoint endpoints sender).core.sent = [] ∧
      ∃ recovery, (endpoint endpoints sender).recovery = some recovery ∧
        recovery.outstanding = [] ∧ recovery.deadline = none ∧ recovery.timeoutCount = 0 := by
  obtain ⟨current, final, _, retries, ⟨done⟩⟩ := completed_done completed
  have retired := done.completed.retirement
  refine ⟨current.endpoints, ?_, retired.sent, retired.recovery, retired.runtime,
    retired.outstanding, retired.deadline, retired.timeoutCount⟩
  rw [← final]
  exact current.connection

theorem completed_history {state : State input × M.Monitor} (completed : P.Completed initial native allowance state) :
    ∃ current : Cut input complete, current.report.final = state.1 ∧ P.SuffixPassed cut current ∧
      ∃ retries, ∃ done : CampusTCPGapProgressEvidence.Done initial allowance current state.2 retries,
        done.completed.history.operations.flatMap Protocol.TCP.ApplicationTrace.Step.releasedPayload = lower ++ upper ∧
        done.completed.history.operations.flatMap Protocol.TCP.ApplicationTrace.Step.readBytes = lower ++ upper ∧
        done.completed.history.operations.filter CampusTCPRoundPhaseHistory.nonemptyRead = [done.completed.operation] ∧
        ∃ operation ∈ applicationSteps current.endpoints sender.other,
          done.completed.history.operations.filter CampusTCPRecoveryRoundHistory.nonemptyRelease = [operation] ∧
          operation.releasedPayload = lower ++ upper := by
  obtain ⟨current, final, passed, retries, ⟨done⟩⟩ := completed_done completed
  exact ⟨current, final, passed, retries, done, done.completed.history.streams.releaseStream,
    done.completed.history.streams.readStream, done.completed.history.streams.reads, done.completed.history.exact_release⟩

theorem completed_monitor {state : State input × M.Monitor} (completed : P.Completed initial native allowance state) :
    state.2.phase = .done := by
  obtain ⟨_, _, _, retries, ⟨done⟩⟩ := completed_done completed
  exact done.phaseEq

def SelectedReads (initial : GapInitial cut sender lower upper) (allowance : Nat)
    (state : State input × M.Monitor) : Prop :=
  ∃ current : Cut input complete, current.report.final = state.1 ∧ P.SuffixPassed cut current ∧
    ∃ retries, ∃ done : CampusTCPGapProgressEvidence.Done initial allowance current state.2 retries,
      ∀ index byte, (lower ++ upper)[index]? = some byte →
        Nonempty (CampusTCPGapProgressOrigins.SelectedReadOrigin initial current done.completed.operation index byte)

theorem completed_read_origins {state : State input × M.Monitor}
    (completed : P.Completed initial native allowance state) : SelectedReads initial allowance state := by
  obtain ⟨current, final, passed, sources, retries, ⟨done⟩⟩ := CampusTCPGapProgressProgress.completed_sources completed
  exact ⟨current, final, passed, retries, done, fun index byte selected =>
    CampusTCPGapProgressOrigins.Done.read_origin_selected done sources index byte selected⟩

theorem completed_read_permissions {state : State input × M.Monitor}
    (completed : P.Completed initial native allowance state) (prior : cut.report.compliant = true)
    (index : Nat) (byte : UInt8) (selected : (lower ++ upper)[index]? = some byte) :
    ∃ current : Cut input complete, current.report.final = state.1 ∧
      ∃ retries, ∃ done : CampusTCPGapProgressEvidence.Done initial allowance current state.2 retries,
        ∃ origin : CampusTCPGapProgressOrigins.SelectedReadOrigin initial current done.completed.operation index byte,
          CampusTCPRoundOrigins.ServicePermissions origin.read.delivery.service.joint.step
            origin.read.delivery.receive.receipt.served := by
  obtain ⟨current, final, ⟨suffix, history, passed⟩, sources, retries, ⟨done⟩⟩ :=
    CampusTCPGapProgressProgress.completed_sources completed
  obtain ⟨origin⟩ := CampusTCPGapProgressOrigins.Done.read_origin_selected done sources index byte selected
  have compliant := CampusTCPGapProgressOrigins.Completed.compliant done.completed prior suffix history passed
  refine ⟨current, final, retries, done, origin, ?_⟩
  exact CampusTCPRoundOrigins.service_permissions current.report compliant
    origin.read.delivery.service.joint.step origin.read.delivery.service.joint.member
    origin.read.delivery.receive.receipt.served origin.read.delivery.service.present
    origin.read.delivery.receive.receipt.emission origin.read.delivery.receive.receipt.emitted

include basis in
theorem read_by (trace : Trace input cut.report.final suffix steps final remaining)
    (allowed : Actions initial native quantum allowance steps)
    (service : C.Serviced (config initial native quantum allowance) cut.report.final (initialMonitor initial) steps bound)
    (enough : M.boundSlots (config initial native quantum allowance) bound ≤ steps.length) :
    ∃ actual ∈ steps.take (M.boundSlots (config initial native quantum allowance) bound),
      actual.event = .read sender.other (lower ++ upper).length ∧ actual.result.read = lower ++ upper := by
  have done := completed_monitor (completes_by basis trace allowed service enough)
  exact CampusTCPGapProgressMonitorRead.monitorAt_done_read
    (config initial native quantum allowance) steps (M.boundSlots (config initial native quantum allowance) bound)
    initial.lowerSource.index initial.selected.serviceIndex initial.selected.packetID done

include basis in
theorem read_by_checked (trace : Trace input cut.report.final suffix steps final remaining)
    (allowed : C.actions (config initial native quantum allowance) cut.report.final (initialMonitor initial) steps = true)
    (service : C.check (config initial native quantum allowance) cut.report.final (initialMonitor initial) steps bound = true)
    (enough : M.boundSlots (config initial native quantum allowance) bound ≤ steps.length) :
    ∃ actual ∈ steps.take (M.boundSlots (config initial native quantum allowance) bound),
      actual.event = .read sender.other (lower ++ upper).length ∧ actual.result.read = lower ++ upper :=
  read_by basis trace ((C.actions_correct _ _ _ _).mp allowed) ((C.check_correct _ _ _ _ _).mp service) enough

include basis in
theorem read_and_retirement_by (trace : Trace input cut.report.final suffix steps final remaining)
    (allowed : Actions initial native quantum allowance steps)
    (service : C.Serviced (config initial native quantum allowance) cut.report.final (initialMonitor initial) steps bound)
    (enough : M.boundSlots (config initial native quantum allowance) bound ≤ steps.length) :
    (∃ actual ∈ steps.take (M.boundSlots (config initial native quantum allowance) bound),
      actual.event = .read sender.other (lower ++ upper).length ∧ actual.result.read = lower ++ upper) ∧
    ∃ endpoints : Applications complete,
      (S.stateAt cut.report.final steps (M.boundSlots (config initial native quantum allowance) bound)).connection = .application complete endpoints ∧
      (endpoint endpoints sender).core.sent = [] ∧
      ∃ recovery, (endpoint endpoints sender).recovery = some recovery ∧
        recovery.outstanding = [] ∧ recovery.deadline = none ∧ recovery.timeoutCount = 0 :=
  ⟨read_by basis trace allowed service enough, completed_retirement (completes_by basis trace allowed service enough)⟩

end Netlib.Check.CampusTCPGapProgressBounded
