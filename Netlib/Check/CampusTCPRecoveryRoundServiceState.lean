import Netlib.Check.CampusTCPRecoveryRoundState

/-!
# Current range state after actual gateway service

The same processing record supplies admission and tracker updates.
A covering ACK at the gateway does not retire the sender ledger.
-/

namespace Netlib.Check.CampusTCPRecoveryRoundState

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRound (Cut)
open CampusTCPRecoveryRoundNetwork (ServiceMove)

noncomputable section

variable {input : Input} {events : List CampusTCPModel.Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}
variable {initial : Initial report complete request} {current : Cut input complete}
variable {sentAt retries : Nat} {released : Bool}
variable {item : Theory.Outstanding.Item (Ticket input.active input.passive)}
variable {hit : FlowNAT.Hit} {session : Admission.Session} {actual : Step input} {served : Served input}
variable {emission : WireForwarding.Emission served.ticket.value.source.packet}
variable {emitted : served.evidence.output = some emission}

def afterProcessing (processing : CampusTCPService.Processing context before source zone) : CampusTCPService.Before :=
  { before with tracker := processing.outcome.state, admission := processing.nextAdmission }

private theorem before_eq (before after : CampusTCPService.Before)
    (environment : before.environment = after.environment) (tracker : before.tracker = after.tracker)
    (admission : before.admission = after.admission) : before = after := by
  cases before
  cases after
  simp only [CampusTCPService.Before.environment, CampusTCPService.Before.Environment.mk.injEq] at environment
  rcases environment with ⟨rfl, rfl, rfl, rfl, rfl⟩
  cases tracker
  cases admission
  rfl

theorem service_after_before (value : ServiceMove initial current item hit session actual served emission emitted)
    (processing : CampusTCPService.Processing (input.contextFor served.ticket.value.gateway)
      served.before served.ticket.value.source input.zone)
    (present : served.evidence.processing = some processing) (primary : item.value.gateway = .primary) :
    beforeService input value.move.after.report.final .primary = afterProcessing processing := by
  have previous : served.before = beforeService input current.report.final .primary := by
    rw [value.facts.current, primary]
  have environment := CampusTCPRoundEnvironment.service_environment _ _ value.environment .primary
  have transport := value.facts.transport
  rw [primary] at transport
  have states := CampusTCPRoundAdmission.Evidence.state_of_processing served.evidence processing present
  apply before_eq
  · exact environment.symm.trans (congrArg CampusTCPService.Before.environment previous).symm
  · rw [value.move.final]
    change (actual.result.state.resident .primary).transport.tracker = processing.outcome.state
    rw [transport]
    exact states.1
  · rw [value.move.final]
    change (actual.result.state.resident .primary).transport.admission = processing.nextAdmission
    rw [transport]
    exact states.2

theorem GatewayState.original_processed (gateway : GatewayState initial before)
    (processing : CampusTCPService.Processing context before source zone)
    (direction : processing.prepared.attachment.direction = .original)
    (fields : CampusTCPRoundPhaseBase.OriginalFields (complete := complete) (request := request) produced)
    (packet : source = produced.source) :
    Nonempty (GatewayState initial (afterProcessing processing) ×
      A.Observed initial.session request.bytes processing.nextAdmission) := by
  obtain ⟨seen⟩ := gateway.admission.original_processing initial processing direction
    (by simpa only [packet] using fields.profile) (by simpa only [packet] using fields.sequence)
    (by simpa only [packet] using fields.acknowledgment) (by simpa only [packet] using fields.payload)
  have records := CampusTCPRoundGateway.Processing.singleton_data_records processing gateway.admission.session
    gateway.admission.phase gateway.records
  exact ⟨⟨processing.outcome.valid, records, .observed seen⟩, seen⟩

theorem Live.original_service (live : Live initial current sentAt retries released)
    (value : ServiceMove initial current item ⟨initial.entry.flow, .original⟩ session actual served emission emitted)
    (primary : item.value.gateway = .primary)
    (fields : CampusTCPRoundPhaseBase.OriginalFields (complete := complete) (request := request) served.ticket.value.produced) :
    Nonempty (Live initial value.move.after sentAt retries released ×
      A.Observed initial.session request.bytes (beforeService input value.move.after.report.final .primary).admission) := by
  obtain ⟨processing, present, _, _, direction, _⟩ := value.facts.processing
  have previous : served.before = beforeService input current.report.final .primary := by
    rw [value.facts.current, primary]
  let old := live.gateway.frame previous.symm
  obtain ⟨gateway, seen⟩ := old.original_processed processing direction fields rfl
  have after := service_after_before value processing present primary
  let nextGateway := gateway.frame after.symm
  let nextSeen := seen.frame (congrArg CampusTCPService.Before.admission after.symm)
  refine ⟨⟨value.anchor, ?_, ?_, nextGateway, ?_, fun _ => ⟨nextSeen⟩⟩, nextSeen⟩
  · rw [value.endpoints]
    exact live.sender
  · rw [value.endpoints]
    exact live.receiver
  · exact live.history.network value.move (by rw [value.facts.event]; exact .serve _ _)

theorem Live.ack_service (live : Live initial current sentAt retries true)
    (value : ServiceMove initial current item ⟨initial.entry.flow, .reply⟩ session actual served emission emitted)
    (primary : item.value.gateway = .primary)
    (fields : CampusTCPRoundPhaseBase.AckFields (complete := complete) (request := request) served.ticket.value.produced) :
    Nonempty (Live initial value.move.after sentAt retries true) := by
  obtain ⟨processing, present, _, _, direction, _⟩ := value.facts.processing
  have previous : served.before = beforeService input current.report.final .primary := by
    rw [value.facts.current, primary]
  let old := live.gateway.frame previous.symm
  obtain ⟨seen⟩ := live.observed rfl
  let beforeSeen := seen.frame (congrArg CampusTCPService.Before.admission previous.symm)
  obtain ⟨nextSeen, _⟩ := beforeSeen.ack_processing processing direction fields.profile fields.payload
    (fields.sequence.trans initial.aligned.replyBase.symm)
    (by rw [initial.aligned.originalBase]; exact fields.acknowledgment)
  have records := CampusTCPRoundGateway.Processing.singleton_data_records processing old.admission.session
    old.admission.phase old.records
  let gateway : GatewayState initial (afterProcessing processing) :=
    ⟨processing.outcome.valid, records, .observed nextSeen⟩
  have after := service_after_before value processing present primary
  let currentSeen := nextSeen.frame (congrArg CampusTCPService.Before.admission after.symm)
  refine ⟨⟨value.anchor, ?_, ?_, gateway.frame after.symm, ?_, fun _ => ⟨currentSeen⟩⟩⟩
  · rw [value.endpoints]
    exact live.sender
  · rw [value.endpoints]
    exact live.receiver
  · exact live.history.network value.move (by rw [value.facts.event]; exact .serve _ _)

end

end Netlib.Check.CampusTCPRecoveryRoundState
