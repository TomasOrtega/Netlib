import Netlib.Check.CampusTCPTwoProgressEvidenceTrace

/-!
# Actual-cut invariant for two-record execution

The abstract state has a witness in the same campus report.
Completion retains the actual read, sources and loss history.
-/

namespace Netlib.Check.CampusTCPTwoProgressInvariant

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressEvidence (Evidence Complete)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {state : State input × CampusTCPTwoProgressMonitor.Monitor}

def Invariant (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (quantum allowance : Nat)
    (state : State input × CampusTCPTwoProgressMonitor.Monitor) : Prop :=
  ∃ current : Cut input complete, current.report.final = state.1 ∧ Nonempty (Evidence initial native quantum allowance current state.2)

def Completed (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (quantum allowance : Nat)
    (state : State input × CampusTCPTwoProgressMonitor.Monitor) : Prop :=
  ∃ current : Cut input complete, current.report.final = state.1 ∧ Nonempty (Complete initial native quantum allowance current state.2)

theorem initial_invariant (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (quantum allowance : Nat) :
    Invariant initial native quantum allowance (cut.report.final, .initial) :=
  ⟨cut, rfl, ⟨Evidence.ofInitial initial native quantum allowance⟩⟩

theorem Invariant.healthy (invariant : Invariant initial native quantum allowance state) : state.2.mode ≠ .invalid := by
  obtain ⟨current, _, ⟨evidence⟩⟩ := invariant
  exact evidence.healthy

theorem Invariant.compliant (invariant : Invariant initial native quantum allowance state)
    (prior : cut.report.compliant = true) :
    ∃ current : Cut input complete, current.report.final = state.1 ∧ current.report.compliant = true := by
  obtain ⟨current, same, ⟨evidence⟩⟩ := invariant
  exact ⟨current, same, evidence.compliant prior⟩

theorem done_evidence (evidence : Evidence initial native quantum allowance current monitor)
    (done : monitor.mode = .done) : Nonempty (Complete initial native quantum allowance current monitor) := by
  cases evidence with
  | written value _ => rw [value.mode] at done; cases done
  | upper _ value _ => rw [value.mode] at done; cases done
  | active core value => rcases value.mode with mode | mode <;> rw [mode] at done <;> cases done
  | ready core value => rw [value.mode] at done; cases done
  | done value => exact ⟨value⟩

theorem Invariant.finished (invariant : Invariant initial native quantum allowance state) (done : state.2.mode = .done) :
    Completed initial native quantum allowance state := by
  obtain ⟨current, same, ⟨evidence⟩⟩ := invariant
  exact ⟨current, same, done_evidence evidence done⟩

theorem Completed.invariant (done : Completed initial native quantum allowance state) : Invariant initial native quantum allowance state := by
  obtain ⟨current, same, ⟨value⟩⟩ := done
  exact ⟨current, same, ⟨.done value⟩⟩

theorem Completed.retry_bound (done : Completed initial native quantum allowance state) : state.2.retries ≤ allowance := by
  obtain ⟨current, _, ⟨value⟩⟩ := done
  rw [← value.retryCount]
  exact value.retry_bound

end Netlib.Check.CampusTCPTwoProgressInvariant
