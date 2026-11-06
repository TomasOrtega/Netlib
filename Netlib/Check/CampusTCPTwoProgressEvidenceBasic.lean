import Netlib.Check.CampusTCPTwoProgressEvidenceTrace
import Netlib.Check.CampusTCPTwoProgressPhaseClock

/-!
# Actual preparation, read and clock transitions

These transitions retain the same suffix source ledger.
Clock transitions also preserve an already completed read.
-/

namespace Netlib.Check.CampusTCPTwoProgressEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressSetup (config)
open CampusTCPTwoProgressPhaseBase (Core)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : CampusTCPTwoProgressMonitor.Monitor} {actual : Step input} {actor : Actor} {millis : Nat}

theorem Evidence.anchor (value : Evidence initial native quantum allowance current monitor) : CampusTCPGapProgressPhaseBase.Anchor cut current := by
  cases value with
  | written value _ => exact value.core.live.anchor
  | upper _ value _ => exact value.core.live.anchor
  | active core _ => exact core.live.anchor
  | ready core _ => exact core.live.anchor
  | done value => exact value.completed.anchor

def Complete.clock (value : Complete initial native quantum allowance current monitor)
    (clocked : CampusTCPTwoProgressClock.Clocked cut current (config initial native quantum allowance) monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor
      (.advanceClock actor millis)) : Complete initial native quantum allowance clocked.move.after monitor := by
  have folded : (clocked.move.after.report.steps.drop current.report.steps.length).foldl
      (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance)) monitor = monitor := by
    rw [clocked.move.history, List.drop_append_length]
    simpa only [List.foldl_cons, List.foldl_nil] using clocked.observed
  exact {
    first := value.first, second := value.second, timeouts := value.timeouts
    completed := value.completed.clock clocked.placement
      (CampusTCPTwoProgressNetworkState.clock_time clocked value.completed.anchor.guards allowed sender)
      (CampusTCPTwoProgressNetworkState.clock_time clocked value.completed.anchor.guards allowed sender.other)
    retryCount := value.retryCount
    losses := value.losses.clock clocked.placement folded
    lossBound := value.lossBound
    sources := value.sources.clock clocked
    mode := value.mode, stamp := value.stamp, bytes := value.bytes
    originals := value.originals.clock clocked.placement
    originalTimes := value.originalTimes
    writer := value.writer.clock clocked.placement
    senderDuplicate := value.senderDuplicate
    gatewayComplete := value.gatewayComplete.same_service _ (clocked.placement.frame.beforeService gateway) }

def Evidence.clock (value : Evidence initial native quantum allowance current monitor)
    (clocked : CampusTCPTwoProgressClock.Clocked cut current (config initial native quantum allowance) monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor
      (.advanceClock actor millis)) : Evidence initial native quantum allowance clocked.move.after monitor := by
  cases value with
  | written value sources => exact .written (value.clock clocked allowed) (sources.clock clocked)
  | upper first value sources => exact .upper first (value.clock clocked allowed) (sources.clock clocked)
  | active core value => exact .active (core.clock clocked allowed) (value.clock clocked allowed)
  | ready core value =>
    exact .ready (core.clock clocked allowed) {
      mode := value.mode, retired := value.retired, preparing := value.preparing
      sources := value.sources.clock clocked
      senderDuplicate := by
        rw [CampusTCPTwoProgressPhaseState.clock_sender_recovery core clocked allowed]
        exact value.senderDuplicate
      mainAck := value.mainAck }
  | done value => exact .done (value.clock clocked allowed)

theorem Evidence.clock_at (value : Evidence initial native quantum allowance current monitor) (actor : Actor) (millis : Nat)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor
      (.advanceClock actor millis)) :
    ∃ actual, ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance move.after
      (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual)) := by
  obtain ⟨actual, ⟨clocked⟩⟩ := CampusTCPTwoProgressClock.clock_at value.anchor (config initial native quantum allowance) monitor actor millis allowed
  exact ⟨actual, clocked.move, ⟨clocked.observed.symm ▸ value.clock clocked allowed⟩⟩

theorem written_send_at (before : CampusTCPTwoProgressPreparation.Written initial native quantum allowance current monitor)
    (sources : CampusTCPTwoProgressReceiptSources.History initial current) :
    ∃ actual, ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance move.after
      (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual)) := by
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoProgressPreparation.first_at before
  exact ⟨actual, value.value.value.facts.move, ⟨.upper value.value.value.original value.next
    (sources.non_delivery value.value.value.facts.move (by rw [value.value.value.facts.event]; trivial))⟩⟩

theorem upper_send_at {first : CampusTCPTwoProgressSender.Original initial .lower}
    (before : CampusTCPTwoProgressPreparation.PendingUpper initial native quantum allowance current monitor first)
    (sources : CampusTCPTwoProgressReceiptSources.History initial current) :
    ∃ actual, ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance move.after
      (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual)) := by
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoProgressPreparation.second_at before
  exact ⟨actual, value.value.value.facts.move, ⟨.active value.value.next (CampusTCPTwoProgressPhaseState.Active.ofBoth value sources)⟩⟩

theorem upper_lower_drop_at {first : CampusTCPTwoProgressSender.Original initial .lower}
    (before : CampusTCPTwoProgressPreparation.PendingUpper initial native quantum allowance current monitor first)
    (sources : CampusTCPTwoProgressReceiptSources.History initial current) (pending : monitor.lower.phase = .dataIngress)
    (budget : monitor.drops.length < allowance) :
    ∃ actual, ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance move.after
      (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual)) := by
  obtain ⟨actual, ⟨value⟩⟩ := before.lower_drop_at pending budget
  exact ⟨actual, value.selected.appended.move, ⟨.upper first value.next
    (sources.non_delivery value.selected.appended.move (by rw [value.selected.appended.facts.event]; trivial))⟩⟩

theorem ready_read_at {sent : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
    {core : Core initial native quantum allowance current monitor sent received} (value : Ready core) :
    ∃ actual, ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance move.after
      (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual)) := by
  obtain ⟨actual, move, ⟨done⟩⟩ := value.read_at
  exact ⟨actual, move, ⟨.done done⟩⟩

end Netlib.Check.CampusTCPTwoProgressEvidence
