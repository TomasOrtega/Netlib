import Netlib.Check.CampusTCPStartupJobs
import Netlib.Check.CampusTCPRecoveryStartupSources
import Netlib.Check.CampusTCPCustodyFacts

/-!
# Actual producers of current startup jobs

Pending custody and work retain the same output occurrence.
The occurrence stamp is not an output, work, or custody index.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupCurrentSources

open Protocol.TCP CampusTCPModel

namespace J
export CampusTCPStartupJobs (Source Job)
end J

variable {input : Input} {events : List Event} {report : Report input events}
variable {current : C.State input.active input.passive}

structure ProducedAt (report : Report input events) (source : J.Source input) where
  producer : Step input
  member : producer ∈ report.steps
  produced : producer.result.output = some source.produced

theorem ProducedAt.recorded (source : ProducedAt report selected) :
    source.producer.result.recovery = some selected.actual :=
  CampusTCPRecoveryReceipts.Step.recovery_output_recorded source.producer selected.actual selected.occurrence selected.emitted source.produced

theorem ProducedAt.recovering_member (source : ProducedAt report selected)
    (connected : report.final.connection = .recovering current) : selected.occurrence ∈ current.emissions := by
  have trace := CampusTCPRecoveryStartupOrigins.Report.recovery_trace report connected
  rw [trace.emissions]
  exact List.mem_append_right _ (List.mem_filterMap.mpr
    ⟨selected.actual, List.mem_filterMap.mpr ⟨source.producer, source.member, source.recorded⟩, selected.emitted⟩)

theorem ProducedAt.shape (source : ProducedAt report selected) (connected : report.final.connection = .recovering current) :
    TCPHandshakeRecovery.OutputShape input.active input.passive selected.occurrence :=
  (CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connected).output_shape (source.recovering_member connected)

theorem ProducedAt.header (source : ProducedAt report selected) (connected : report.final.connection = .recovering current) :
    current.phase.sourceHeader selected.occurrence.actor = some selected.occurrence.packet.packet.header :=
  (CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connected).packet_inventory.headers _ (source.recovering_member connected)

theorem ProducedAt.same_control (first : ProducedAt report selected) (second : ProducedAt report other)
    (connected : report.final.connection = .recovering current) (control : TCPHandshakeRecovery.TemplateKind selected.occurrence.kind)
    (kind : selected.occurrence.kind = other.occurrence.kind) : selected.occurrence.packet = other.occurrence.packet :=
  (CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connected).same_control_template
    (first.recovering_member connected) (second.recovering_member connected) control kind

private theorem ticket_producer (report : Report input events) (item : Work.Item (Ticket input.active input.passive))
    (pending : item ∈ report.final.work.pending) :
    ∃ producer ∈ report.steps, producer.result.output = some item.value.produced := by
  obtain ⟨assignment, index, ingress, produced, assignmentMember, assigned, lookup, ticket, earlier⟩ :=
    CampusTCPOrigins.Report.pending_origin report item pending
  have production : item.value.produced = produced := by rw [ticket]; rfl
  obtain ⟨prior, later, history, beforeAssignment, _, _⟩ := CampusTCPFacts.step_origin report assignment assignmentMember
  rcases CampusTCPOrigins.Trace.outputs_origin beforeAssignment produced (List.mem_of_getElem? lookup) with initial | output
  · simp only [Input.initial, List.not_mem_nil] at initial
  · obtain ⟨producer, member, emitted, stamp, earlier⟩ := output
    have stored : producer ∈ report.steps := by
      rw [history]
      exact List.mem_append_left _ member
    exact ⟨producer, stored, by rw [production]; exact emitted⟩

theorem Job.source_at (report : Report input events) (job : J.Job input) (pending : job.Pending report.final) :
    Nonempty (ProducedAt report job.source) := by
  cases job with
  | ingress item index selected payload =>
    have source := CampusTCPCustodyFacts.Report.sources report item (List.mem_append_right _ pending)
    rw [payload] at source
    obtain ⟨producer, member, emitted, stamp, earlier⟩ := CampusTCPOrigins.Report.outputs_origin report selected.produced
      (List.mem_of_getElem? source)
    exact ⟨⟨producer, member, emitted⟩⟩
  | ticket item selected production =>
    obtain ⟨producer, member, emitted⟩ := ticket_producer report item pending
    exact ⟨⟨producer, member, by rw [production] at emitted; exact emitted⟩⟩
  | link item index served emission emitted selected production payload =>
    have source := CampusTCPCustodyFacts.Report.sources report item (List.mem_append_right _ pending)
    rw [payload] at source
    obtain ⟨origin⟩ := CampusTCPRecoveryStartupSources.Report.service_source report served (List.mem_of_getElem? source)
    have produced := origin.produced
    rw [production] at produced
    exact ⟨⟨origin.producer, origin.producerMember, produced⟩⟩

theorem Job.recovering_member (report : Report input events) (job : J.Job input) (pending : job.Pending report.final)
    (connected : report.final.connection = .recovering current) : job.source.occurrence ∈ current.emissions := by
  obtain ⟨source⟩ := Job.source_at report job pending
  exact source.recovering_member connected

theorem Job.shape (report : Report input events) (job : J.Job input) (pending : job.Pending report.final)
    (connected : report.final.connection = .recovering current) :
    TCPHandshakeRecovery.OutputShape input.active input.passive job.source.occurrence := by
  obtain ⟨source⟩ := Job.source_at report job pending
  exact source.shape connected

end Netlib.Check.CampusTCPRecoveryStartupCurrentSources
