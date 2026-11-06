import Netlib.Check.CampusTCPGapProgressNetwork

namespace Netlib.Check.CampusTCPGapProgressGateway

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPGapProgressStart
open CampusTCPRound (Cut)

private theorem map_fixed (function : α → α) (values : List α)
    (fixed : ∀ value ∈ values, function value = value) : values.map function = values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    rw [List.map_cons, fixed head List.mem_cons_self, ih (fun value member => fixed value (List.mem_cons_of_mem _ member))]

private theorem markReply_fixed (state : ConntrackLifecycle.State) (flow : FlowNAT.Entry)
    (confirmed : ∀ record ∈ state.records, record.entry.flow = flow → record.seenReply = true) :
    state.markReply flow = state := by
  have unchanged : state.records.map (ConntrackLifecycle.State.markRecord flow) = state.records := by
    apply map_fixed
    intro record member
    unfold ConntrackLifecycle.State.markRecord
    split
    · rename_i same
      have marked := confirmed record member same
      cases record
      simp_all only
    · rfl
  cases state
  exact congrArg ConntrackLifecycle.State.mk unchanged

variable {input : Input} {complete : H.Completed input.active input.passive}
  {anchor cut : Cut input complete} {basis : StartupBasis anchor} {start : GatewayStart anchor basis}
  {source : WireForwarding.Source}

theorem Current.processing_tracker (current : Current start cut)
    (processing : CampusTCPService.Processing context (beforeService input cut.report.final .standby) source zone) :
    processing.outcome.state = (beforeService input cut.report.final .standby).tracker := by
  have allowed : Admission.Allowed (.data current.session) processing.prepared.attachment
      source.packet.segment (beforeService input cut.report.final .standby).admission.observations := by
    simpa only [current.phase, WireForwarding.Source.asInput] using processing.admitted.admitted
  rw [processing.existing_state allowed.2.1]
  cases direction : processing.prepared.attachment.direction with
  | original =>
    obtain ⟨_, _, _, _, unchanged⟩ := ConntrackLifecycle.prepare_existing_original _ _ processing.prepared
      processing.attached allowed.2.1 direction
    exact unchanged
  | reply =>
    have changed := ConntrackLifecycle.prepare_reply _ _ processing.prepared processing.attached direction
    rw [changed.2.2, allowed.1]
    apply markReply_fixed
    intro record member same
    rw [current.confirmed_binding record member same]

end Netlib.Check.CampusTCPGapProgressGateway

namespace Netlib.Check.CampusTCPGapProgressState

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPGapProgressStart
open CampusTCPRound (Cut)
open CampusTCPGapProgressNetwork (ServiceMove)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {lower upper : List UInt8}
variable {initial : GapInitial cut sender lower upper} {retries : Nat} {released : Bool}
variable {item : Theory.Outstanding.Item (Ticket input.active input.passive)}
variable {hit : FlowNAT.Hit} {session : Admission.Session} {actual : Step input} {served : Served input}
variable {emission : WireForwarding.Emission served.ticket.value.source.packet} {emitted : served.evidence.output = some emission}

private def processingAt (processing : CampusTCPService.Processing context before source zone) (same : before = next) :
    CampusTCPService.Processing context next source zone := same ▸ processing

private theorem processingAt_outcome (processing : CampusTCPService.Processing context before source zone) (same : before = next) :
    (processingAt processing same).outcome = processing.outcome := by cases same; rfl

private theorem processingAt_admission (processing : CampusTCPService.Processing context before source zone) (same : before = next) :
    (processingAt processing same).nextAdmission = processing.nextAdmission := by cases same; rfl

private theorem processingAt_attachment (processing : CampusTCPService.Processing context before source zone) (same : before = next) :
    (processingAt processing same).prepared.attachment = processing.prepared.attachment := by cases same; rfl

private def gateway_after_processing (live : Live initial current retries released)
    (value : ServiceMove initial current item hit session actual served emission emitted)
    (processing : CampusTCPService.Processing (input.contextFor served.ticket.value.gateway)
      served.before served.ticket.value.source input.zone)
    (present : served.evidence.processing = some processing) (after : Admission.Session)
    (phase : processing.nextAdmission.phase = .data after) (shape : Shape initial.gateway.seed after)
    (ledger : (beforeService input current.report.final .standby).admission.observations <+: processing.nextAdmission.observations)
    (tracker : processing.outcome.state = (beforeService input current.report.final .standby).tracker) :
    CampusTCPGapProgressGateway.Current initial.gateway value.move.after where
  session := after
  phase := by rw [value.after_before processing present]; exact phase
  shape := shape
  observations := by
    rw [value.after_before processing present]
    exact live.gateway.observations.trans ledger
  trackerValid := by rw [value.after_before processing present]; exact processing.outcome.valid
  record := live.gateway.record
  member := by
    rw [value.after_before processing present]
    change live.gateway.record ∈ processing.outcome.state.records
    rw [tracker]
    exact live.gateway.member
  entry := live.gateway.entry.trans (live.gateway.shape.entry.trans shape.entry.symm)
  confirmed := live.gateway.confirmed

private def live_after_service (live : Live initial current retries released)
    (value : ServiceMove initial current item hit session actual served emission emitted)
    (gateway : CampusTCPGapProgressGateway.Current initial.gateway value.move.after) :
    Live initial value.move.after retries released := by
  refine ⟨value.anchor, ?_, ?_, gateway, ?_⟩
  · rw [value.endpoints]
    exact live.senderFlight
  · rw [value.endpoints]
    exact live.receiverFacts
  · exact live.history.same (by rw [value.endpoints])

theorem Live.lower_service (live : Live initial current retries released)
    (value : ServiceMove initial current item hit session actual served emission emitted)
    (direction : hit.direction = sender.direction)
    (sequence : served.ticket.value.source.packet.segment.sequence = (live.gateway.session.lane sender.direction).base)
    (payload : served.ticket.value.source.packet.segment.payload = lower) :
    Nonempty (Live initial value.move.after retries released) := by
  obtain ⟨processing, present, _, _, attachmentDirection, _⟩ := value.facts.processing
  have previous : served.before = beforeService input current.report.final .standby := by
    rw [value.facts.current, value.standby]
  let selected := processingAt processing previous
  have selectedDirection : selected.prepared.attachment.direction = sender.direction := by
    rw [processingAt_attachment]
    exact attachmentDirection.trans direction
  obtain ⟨after, phase, shape, observed⟩ := live.gateway.after_lower initial.lowerRange selected selectedDirection
    initial.lowerNonempty sequence payload
  have nextPhase : processing.nextAdmission.phase = .data after := by
    rw [← processingAt_admission processing previous]
    exact phase
  have ledger : (beforeService input current.report.final .standby).admission.observations <+: processing.nextAdmission.observations := by
    rw [← processingAt_admission processing previous]
    rw [observed]
    exact List.prefix_append _ _
  have tracker : processing.outcome.state = (beforeService input current.report.final .standby).tracker := by
    rw [← processingAt_outcome processing previous]
    exact live.gateway.processing_tracker selected
  let gateway := gateway_after_processing live value processing present after nextPhase shape ledger tracker
  exact ⟨live_after_service live value gateway⟩

theorem Live.ack_service_covered (live : Live initial current retries true)
    (value : ServiceMove initial current item hit session actual served emission emitted)
    (empty : served.ticket.value.source.packet.segment.payload = [])
    (ack : served.ticket.value.source.packet.segment.acknowledgment =
      (live.gateway.session.peer hit.direction).base.add (live.gateway.session.peer hit.direction).observed) :
    ∃ next : Live initial value.move.after retries true,
      (next.gateway.session.peer hit.direction).acknowledged = (next.gateway.session.peer hit.direction).observed := by
  obtain ⟨processing, present, _, _, attachmentDirection, _⟩ := value.facts.processing
  have previous : served.before = beforeService input current.report.final .standby := by
    rw [value.facts.current, value.standby]
  let selected := processingAt processing previous
  have selectedDirection : selected.prepared.attachment.direction = hit.direction := by
    rw [processingAt_attachment]
    exact attachmentDirection
  have acknowledgment : served.ticket.value.source.packet.segment.acknowledgment =
      (live.gateway.session.peer selected.prepared.attachment.direction).base.add
        (live.gateway.session.peer selected.prepared.attachment.direction).observed := by
    rw [selectedDirection]
    exact ack
  obtain ⟨after, phase, shape, covered, observed⟩ := live.gateway.after_ack selected empty acknowledgment
  have nextPhase : processing.nextAdmission.phase = .data after := by
    rw [← processingAt_admission processing previous]
    exact phase
  have ledger : (beforeService input current.report.final .standby).admission.observations <+: processing.nextAdmission.observations := by
    rw [← processingAt_admission processing previous]
    rw [observed]
    exact List.prefix_append _ _
  have tracker : processing.outcome.state = (beforeService input current.report.final .standby).tracker := by
    rw [← processingAt_outcome processing previous]
    exact live.gateway.processing_tracker selected
  let gateway := gateway_after_processing live value processing present after nextPhase shape ledger tracker
  refine ⟨live_after_service live value gateway, ?_⟩
  change (after.peer hit.direction).acknowledged = (after.peer hit.direction).observed
  simpa only [selectedDirection] using covered

theorem Live.ack_service (live : Live initial current retries true)
    (value : ServiceMove initial current item hit session actual served emission emitted)
    (empty : served.ticket.value.source.packet.segment.payload = [])
    (ack : served.ticket.value.source.packet.segment.acknowledgment =
      (live.gateway.session.peer hit.direction).base.add (live.gateway.session.peer hit.direction).observed) :
    Nonempty (Live initial value.move.after retries true) := by
  obtain ⟨next, _⟩ := live.ack_service_covered value empty ack
  exact ⟨next⟩

end Netlib.Check.CampusTCPGapProgressState
