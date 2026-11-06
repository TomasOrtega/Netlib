import Netlib.Check.CampusTCPTwoProgressRecoveryCap
import Netlib.Check.CampusTCPTwoProgressEvidenceHop
import Netlib.Check.CampusTCPTwoProgressPhaseRetryState

/-!
# Fixed recovery caps through clocks and timeouts

Clock steps retain the current RTO.
An actual timeout doubles the RTO and advances the retry count.
-/

namespace Netlib.Check.CampusTCPTwoProgressRecoveryCap

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (Core)
open CampusTCPTwoProgressPhaseState (Active)
open CampusTCPTwoProgressSetup (config)
open CampusTCPTwoProgressEvidence (Evidence Complete Hop)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance capacity : Nat}
variable {monitor : M.Monitor} {sent : S.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
variable {actual : Step input} {actor : Actor} {millis : Nat}
variable {core : Core initial native quantum allowance current monitor sent received}

theorem complete_cap (value : Complete initial native quantum allowance current monitor) :
    PendingCap (config initial native quantum allowance) capacity current.report.final monitor := by
  intro recovery runtime pending
  have selected : (endpoint current.endpoints sender).recovery = some recovery := by
    simpa only [G.senderRecovery, current.connection, config] using runtime
  have same : recovery = value.completed.senderFlight.recovery :=
    Option.some.inj (selected.symm.trans value.completed.senderFlight.runtime)
  have ledger := value.completed.senderFlight.ledger
  rw [← same] at ledger
  exact False.elim (pending ledger)

theorem core_clock_cap (core : Core initial native quantum allowance current monitor sent received)
    (prior : PendingCap (config initial native quantum allowance) capacity current.report.final monitor)
    (clocked : CampusTCPTwoProgressClock.Clocked cut current (config initial native quantum allowance) monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance)
      current.report.final monitor (.advanceClock actor millis)) :
    PendingCap (config initial native quantum allowance) capacity clocked.move.after.report.final monitor := by
  apply of_core (core.clock clocked allowed)
  intro pending
  rw [CampusTCPTwoProgressPhaseState.clock_sender_recovery core clocked allowed]
  exact at_core core prior pending

theorem clock_cap (value : Evidence initial native quantum allowance current monitor)
    (prior : PendingCap (config initial native quantum allowance) capacity current.report.final monitor)
    (clocked : CampusTCPTwoProgressClock.Clocked cut current (config initial native quantum allowance) monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance)
      current.report.final monitor (.advanceClock actor millis)) :
    PendingCap (config initial native quantum allowance) capacity clocked.move.after.report.final monitor := by
  cases value with
  | written value _ => exact core_clock_cap value.core prior clocked allowed
  | upper _ value _ => exact core_clock_cap value.core prior clocked allowed
  | active core _ => exact core_clock_cap core prior clocked allowed
  | ready core _ => exact core_clock_cap core prior clocked allowed
  | done value => exact complete_cap (value.clock clocked allowed)

theorem clock_hop_cap (value : Evidence initial native quantum allowance current monitor)
    (prior : PendingCap (config initial native quantum allowance) capacity current.report.final monitor)
    (actor : Actor) (millis : Nat)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance)
      current.report.final monitor (.advanceClock actor millis)) :
    ∃ hop : Hop initial native quantum allowance current monitor (.advanceClock actor millis),
      PendingCap (config initial native quantum allowance) capacity hop.move.after.report.final
        (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor hop.actual) := by
  obtain ⟨actual, ⟨clocked⟩⟩ := CampusTCPTwoProgressClock.clock_at value.anchor
    (config initial native quantum allowance) monitor actor millis allowed
  refine ⟨⟨actual, clocked.move, clocked.event, clocked.observed.symm ▸ value.clock clocked allowed⟩, ?_⟩
  change PendingCap _ _ clocked.move.after.report.final (CampusTCPTwoProgressMonitor.observe _ monitor actual)
  rw [clocked.observed]
  exact clock_cap value prior clocked allowed

theorem retried_cap {part : CampusTCPTwoProgressSender.Part} {head : Recovery.Outstanding}
    {rest : List Recovery.Outstanding} {position : Nat}
    (value : CampusTCPTwoProgressPhaseRetry.Retried core part head rest position actual)
    (prior : PendingCap (config initial native quantum allowance) capacity current.report.final monitor) :
    PendingCap (config initial native quantum allowance) capacity value.value.move.after.report.final
      (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual) := by
  apply of_core value.next
  intro _
  have pending : sent.ledger ≠ [] := by rw [value.value.selection.ledger]; simp
  have beforeBound := at_core core prior pending
  have runtime : value.next.live.senderFlight.recovery = Recovery.timeoutState core.live.senderFlight.recovery head rest := by
    apply Option.some.inj
    exact value.next.live.senderFlight.runtime.symm.trans (by rw [value.value.endpointsEq]; exact value.value.facts.runtime)
  rw [runtime, value.retries]
  change 2 * core.live.senderFlight.recovery.rto ≤ 2 ^ (monitor.retries + 1) * capacity
  calc
    _ ≤ 2 * (2 ^ monitor.retries * capacity) := Nat.mul_le_mul_left _ beforeBound
    _ = _ := by rw [Nat.pow_succ]; simp only [Nat.mul_assoc, Nat.mul_left_comm]

theorem timeout_hop_cap (active : Active core)
    (prior : PendingCap (config initial native quantum allowance) capacity current.report.final monitor)
    (waiting : monitor.waiting = true) (budget : allowance ≤ 2)
    (selected : CampusTCPTwoProgressMonitor.nextDemand (config initial native quantum allowance) current.report.final monitor =
      some (.single (.timeout sender))) :
    ∃ hop : Hop initial native quantum allowance current monitor (.timeout sender true),
      PendingCap (config initial native quantum allowance) capacity hop.move.after.report.final
        (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor hop.actual) := by
  have mode := active.waiting_mode waiting
  have ack := (active.waiting waiting).1
  have demand : CampusTCPTwoProgressMonitor.timerDemand (config initial native quantum allowance) current.report.final =
      some (.timeout sender) := by
    simp only [CampusTCPTwoProgressMonitor.nextDemand, mode, ack, waiting, ite_true] at selected
    cases found : CampusTCPTwoProgressMonitor.timerDemand (config initial native quantum allowance) current.report.final with
    | none => rw [found] at selected; cases selected
    | some demand =>
      have same : CampusTCPTwoProgressMonitor.Demand.single demand = .single (.timeout sender) := by
        simpa only [found, Option.map_some, Option.some.injEq] using selected
      rw [CampusTCPTwoProgressMonitor.Demand.single.inj same]
  obtain ⟨recovery, head, rest, deadline, runtime, ledger, timer, deadlineDue, elapsed, _⟩ :=
    CampusTCPTwoProgressTimer.timerDemand_timeout demand
  have same : recovery = core.live.senderFlight.recovery :=
    Option.some.inj (runtime.symm.trans (CampusTCPTwoProgressPhaseNormalize.sender_runtime core))
  subst recovery
  have target := CampusTCPTwoProgressTimer.target_of_fields ledger timer
  have due := Nat.max_le.mpr (And.intro deadlineDue elapsed)
  cases sent with
  | written | lower => cases active.preparing
  | retired => exact False.elim (active.nonempty rfl)
  | both first second head =>
    obtain ⟨value⟩ := CampusTCPTwoProgressPhaseRetryState.lower_at active waiting budget target due
    exact ⟨⟨value.actual, value.move, value.event, value.evidence⟩, retried_cap value.value prior⟩
  | tail first second head =>
    obtain ⟨value⟩ := CampusTCPTwoProgressPhaseRetryState.upper_at active waiting budget target due
    exact ⟨⟨value.actual, value.move, value.event, value.evidence⟩, retried_cap value.value prior⟩

end Netlib.Check.CampusTCPTwoProgressRecoveryCap
