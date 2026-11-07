import Netlib.Check.CampusTCPRecoveryReceipts
import Netlib.Check.TCPHandshakeRecoveryOutputShapeFacts
import Netlib.Check.TCPHandshakeRecoveryPacketInventoryFacts

/-!
# Actual producers of stored startup services

A service retains its earlier assignment and endpoint output even when no
packet leaves the gateway. The occurrence stamp remains separate from its
campus output index.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupSources

open Protocol.TCP CampusTCPModel

variable {input : Input} {events : List Event} {report : Report input events}

structure ServiceSource (report : Report input events) (served : Served input) where
  serviceStep : Step input
  serviceMember : serviceStep ∈ report.steps
  recorded : serviceStep.result.service = some served
  serviceTime : served.time = serviceStep.before.time
  producer : Step input
  producerMember : producer ∈ report.steps
  produced : producer.result.output = some served.ticket.value.produced
  assignment : Step input
  assignmentMember : assignment ∈ report.steps
  outputIndex : Nat
  ingress : I.InterfaceRef
  assigned : assignment.event = .assign outputIndex ingress
  lookup : assignment.before.outputs[outputIndex]? = some served.ticket.value.produced
  sourceEarlier : producer.before.time < assignment.before.time
  assignmentEarlier : assignment.before.time < serviceStep.before.time

theorem Report.service_source (report : Report input events) (served : Served input)
    (member : served ∈ report.final.services) : Nonempty (ServiceSource report served) := by
  obtain ⟨serviceStep, serviceMember, recorded, serviceTime, _⟩ :=
    CampusTCPOrigins.Report.services_origin report served member
  obtain ⟨id, observed, completed, _, _, ticket, _, _⟩ := CampusTCPOrigins.service_origin serviceStep served recorded
  obtain ⟨prior, later, history, preceding, _, _⟩ := CampusTCPFacts.step_origin report serviceStep serviceMember
  let beforeReport : Report input (prior.map (·.event)) := ⟨serviceStep.before, prior, [], preceding⟩
  obtain ⟨assignment, index, ingress, produced, assignedMember, assigned, lookup, exactTicket, assignmentEarlier⟩ :=
    CampusTCPOrigins.Report.pending_origin beforeReport completed.item completed.member
  have production : served.ticket.value.produced = produced := by
    rw [ticket, exactTicket]
    rfl
  obtain ⟨producerPrior, producerLater, assignedHistory, beforeAssignment, _, _⟩ :=
    CampusTCPFacts.step_origin beforeReport assignment assignedMember
  have selected := CampusTCPOrigins.Trace.outputs_origin beforeAssignment produced (List.mem_of_getElem? lookup)
  rcases selected with initial | ⟨producer, producerMember, output, _, sourceEarlier⟩
  · simp only [Input.initial, List.not_mem_nil] at initial
  · have assignmentFull : assignment ∈ report.steps := by
      rw [history]
      exact List.mem_append_left _ assignedMember
    have producerFull : producer ∈ report.steps := by
      rw [history]
      apply List.mem_append_left
      change producer ∈ beforeReport.steps
      rw [assignedHistory]
      exact List.mem_append_left _ producerMember
    exact ⟨⟨serviceStep, serviceMember, recorded, serviceTime, producer, producerFull,
      by rw [production]; exact output, assignment, assignmentFull, index, ingress, assigned,
      by rw [production]; exact lookup, sourceEarlier, assignmentEarlier⟩⟩

theorem ServiceSource.earlier (source : ServiceSource report served) : source.producer.before.time < served.time := by
  have first := source.sourceEarlier
  have second := source.assignmentEarlier
  have time := source.serviceTime
  omega

theorem ServiceSource.recovery_recorded (source : ServiceSource report served)
    (actual : C.Step input.active input.passive) (occurrence : C.Emission) (present : actual.result.output = some occurrence)
    (production : served.ticket.value.produced = .recovery actual occurrence present) :
    source.producer.result.recovery = some actual := by
  apply CampusTCPRecoveryReceipts.Step.recovery_output_recorded source.producer actual occurrence present
  rw [← production]
  exact source.produced

theorem ServiceSource.recovering_member (source : ServiceSource report served)
    (actual : C.Step input.active input.passive) (occurrence : C.Emission) (present : actual.result.output = some occurrence)
    (production : served.ticket.value.produced = .recovery actual occurrence present)
    (current : C.State input.active input.passive) (connection : report.final.connection = .recovering current) :
    occurrence ∈ current.emissions := by
  have recorded := source.recovery_recorded actual occurrence present production
  have trace := CampusTCPRecoveryStartupOrigins.Report.recovery_trace report connection
  rw [trace.emissions]
  exact List.mem_append_right _ (List.mem_filterMap.mpr
    ⟨actual, List.mem_filterMap.mpr ⟨source.producer, source.producerMember, recorded⟩, present⟩)

theorem ServiceSource.archive_member (source : ServiceSource report served)
    (actual : C.Step input.active input.passive) (occurrence : C.Emission) (present : actual.result.output = some occurrence)
    (production : served.ticket.value.produced = .recovery actual occurrence present)
    (archive : RecoveryArchive input.active input.passive) (archived : report.final.recoveryArchive = some archive) :
    occurrence ∈ archive.current.emissions := by
  have recorded := source.recovery_recorded actual occurrence present production
  have trace := CampusTCPRecoveryStartupOrigins.Report.archive_trace report archived
  rw [trace.emissions]
  exact List.mem_append_right _ (List.mem_filterMap.mpr
    ⟨actual, List.mem_filterMap.mpr ⟨source.producer, source.producerMember, recorded⟩, present⟩)

theorem ServiceSource.recovering_shape (source : ServiceSource report served)
    (actual : C.Step input.active input.passive) (occurrence : C.Emission) (present : actual.result.output = some occurrence)
    (production : served.ticket.value.produced = .recovery actual occurrence present)
    (current : C.State input.active input.passive) (connection : report.final.connection = .recovering current) :
    TCPHandshakeRecovery.PacketShape input.active input.passive occurrence.actor occurrence.kind served.ticket.value.source.asInput := by
  have member := source.recovering_member actual occurrence present production current connection
  have reachable := CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connection
  change TCPHandshakeRecovery.PacketShape input.active input.passive occurrence.actor occurrence.kind served.ticket.value.produced.output
  rw [production]
  exact reachable.output_shape member

theorem ServiceSource.archive_shape (source : ServiceSource report served)
    (actual : C.Step input.active input.passive) (occurrence : C.Emission) (present : actual.result.output = some occurrence)
    (production : served.ticket.value.produced = .recovery actual occurrence present)
    (archive : RecoveryArchive input.active input.passive) (archived : report.final.recoveryArchive = some archive) :
    TCPHandshakeRecovery.PacketShape input.active input.passive occurrence.actor occurrence.kind served.ticket.value.source.asInput := by
  have member := source.archive_member actual occurrence present production archive archived
  have reachable := CampusTCPRecoveryStartupOrigins.Report.archiveReachable report archived
  change TCPHandshakeRecovery.PacketShape input.active input.passive occurrence.actor occurrence.kind served.ticket.value.produced.output
  rw [production]
  exact reachable.output_shape member

theorem ServiceSource.archive_active_header (source : ServiceSource report served)
    (actual : C.Step input.active input.passive) (occurrence : C.Emission) (present : actual.result.output = some occurrence)
    (production : served.ticket.value.produced = .recovery actual occurrence present)
    (archive : RecoveryArchive input.active input.passive) (archived : report.final.recoveryArchive = some archive)
    (active : occurrence.actor = .active) :
    served.ticket.value.source.packet.header = Output.reverse archive.complete.certificate.activeSeed.core.inbound := by
  have member := source.archive_member actual occurrence present production archive archived
  have reachable := CampusTCPRecoveryStartupOrigins.Report.archiveReachable report archived
  change served.ticket.value.produced.output.packet.header = _
  rw [production]
  exact reachable.complete_active_header archive.phase member active

theorem ServiceSource.archive_passive_header (source : ServiceSource report served)
    (actual : C.Step input.active input.passive) (occurrence : C.Emission) (present : actual.result.output = some occurrence)
    (production : served.ticket.value.produced = .recovery actual occurrence present)
    (archive : RecoveryArchive input.active input.passive) (archived : report.final.recoveryArchive = some archive)
    (passive : occurrence.actor = .passive) :
    served.ticket.value.source.packet.header = Output.reverse archive.complete.certificate.passiveSeed.core.inbound := by
  have member := source.archive_member actual occurrence present production archive archived
  have reachable := CampusTCPRecoveryStartupOrigins.Report.archiveReachable report archived
  change served.ticket.value.produced.output.packet.header = _
  rw [production]
  exact reachable.complete_passive_header archive.phase member passive

end Netlib.Check.CampusTCPRecoveryStartupSources
