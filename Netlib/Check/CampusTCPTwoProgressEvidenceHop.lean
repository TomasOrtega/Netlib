import Netlib.Check.CampusTCPTwoProgressEvidenceBasic

/-!
# Same-event transitions on the current evidence

The witness keeps the chosen event and actual step together.
Determinism then identifies that step with the supplied trace step.
-/

namespace Netlib.Check.CampusTCPTwoProgressEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressSetup (config)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : CampusTCPTwoProgressMonitor.Monitor} {event : Event}

structure Hop (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (quantum allowance : Nat)
    (current : Cut input complete) (monitor : CampusTCPTwoProgressMonitor.Monitor) (event : Event) where
  actual : Step input
  move : Move current actual
  selected : actual.event = event
  next : Evidence initial native quantum allowance move.after
    (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual)

theorem Hop.for_step (hop : Hop initial native quantum allowance current monitor event)
    (actual : Step input) (before : actual.before = current.report.final) (selected : actual.event = event) :
    ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance move.after
      (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual)) := by
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event hop.actual actual
    (hop.move.beforeEq.trans before.symm) (hop.selected.trans selected.symm)
  cases same
  exact ⟨hop.move, ⟨hop.next⟩⟩

theorem Evidence.clock_hop (value : Evidence initial native quantum allowance current monitor) (actor : Actor) (millis : Nat)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor
      (.advanceClock actor millis)) : Nonempty (Hop initial native quantum allowance current monitor (.advanceClock actor millis)) := by
  obtain ⟨actual, ⟨clocked⟩⟩ := CampusTCPTwoProgressClock.clock_at value.anchor (config initial native quantum allowance) monitor actor millis allowed
  exact ⟨⟨actual, clocked.move, clocked.event, clocked.observed.symm ▸ value.clock clocked allowed⟩⟩

theorem written_send_hop (before : CampusTCPTwoProgressPreparation.Written initial native quantum allowance current monitor)
    (sources : CampusTCPTwoProgressReceiptSources.History initial current) :
    Nonempty (Hop initial native quantum allowance current monitor (.send sender lower.length true)) := by
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoProgressPreparation.first_at before
  exact ⟨⟨actual, value.value.value.facts.move, value.value.value.facts.event,
    .upper value.value.value.original value.next
      (sources.non_delivery value.value.value.facts.move (by rw [value.value.value.facts.event]; trivial))⟩⟩

theorem upper_send_hop {first : CampusTCPTwoProgressSender.Original initial .lower}
    (before : CampusTCPTwoProgressPreparation.PendingUpper initial native quantum allowance current monitor first)
    (sources : CampusTCPTwoProgressReceiptSources.History initial current) :
    Nonempty (Hop initial native quantum allowance current monitor (.send sender upper.length true)) := by
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoProgressPreparation.second_at before
  exact ⟨⟨actual, value.value.value.facts.move, value.value.value.facts.event,
    .active value.value.next (CampusTCPTwoProgressPhaseState.Active.ofBoth value sources)⟩⟩

theorem upper_lower_drop_hop {first : CampusTCPTwoProgressSender.Original initial .lower}
    (before : CampusTCPTwoProgressPreparation.PendingUpper initial native quantum allowance current monitor first)
    (sources : CampusTCPTwoProgressReceiptSources.History initial current) (id : Nat)
    (pending : monitor.lower.phase = .dataIngress) (budget : monitor.drops.length < allowance)
    (selected : CampusTCPTwoProgressMonitor.dropTarget (config initial native quantum allowance) current.report.final monitor id = some .lower) :
    Nonempty (Hop initial native quantum allowance current monitor (.dropPacket id)) := by
  obtain ⟨actual, ⟨value⟩⟩ := before.lower_drop_at pending budget
  have first := CampusTCPTwoProgressMonitorFacts.dropTarget_packet _ _ _ _ selected
  have second := CampusTCPTwoProgressMonitorFacts.dropTarget_packet _ _ _ _ value.selected.selected
  have same : value.item.id = id := Option.some.inj (second.symm.trans first)
  exact ⟨⟨actual, value.selected.appended.move, by rw [value.selected.appended.facts.event, same],
    .upper _ value.next
      (sources.non_delivery value.selected.appended.move (by rw [value.selected.appended.facts.event]; trivial))⟩⟩

theorem ready_read_hop {first : CampusTCPTwoProgressSender.Original initial .lower}
    {second : CampusTCPTwoProgressSender.Original initial .upper}
    {core : CampusTCPTwoProgressPhaseBase.Core initial native quantum allowance current monitor (.retired first second) .allReleased}
    (ready : Ready core) : Nonempty (Hop initial native quantum allowance current monitor (.read sender.other (lower ++ upper).length)) := by
  obtain ⟨actual, ⟨record⟩⟩ := CampusTCPTwoProgressPhaseRead.read_at core ready.mode
  let done : Complete initial native quantum allowance record.value.move.after
      (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual) := {
    first, second, timeouts := monitor.retries
    completed := record.completed
    retryCount := record.retries.symm
    losses := record.losses
    lossBound := record.lossBound
    sources := ready.sources.non_delivery record.value.move (by rw [record.value.event]; trivial)
    mode := record.mode
    stamp := by rw [record.completed_operation]; exact record.stamp
    bytes := record.bytes
    originals := record.originals
    originalTimes := record.originalTimes
    writer := record.writer
    senderDuplicate := ready.read_duplicate record
    gatewayComplete := ready.read_gateway record }
  exact ⟨⟨actual, record.value.move, record.value.event, .done done⟩⟩

end Netlib.Check.CampusTCPTwoProgressEvidence
