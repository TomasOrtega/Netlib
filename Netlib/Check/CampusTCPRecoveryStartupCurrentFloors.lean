import Netlib.Check.CampusTCPRecoveryStartupCurrentMilestones
import Netlib.Check.CampusTCPRecoveryStartupTransport
import Netlib.Check.TCPHandshakeRecoveryAvailabilityFacts

/-!
# Current gateway phases from actual startup receipts

Later endpoint controls require earlier real gateway services.
The bounds retain the stored services in their actual order.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupCurrentFloors

open Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupTransport (ServiceChain beforeTransport afterTransport phaseRank)
open CampusTCPRecoveryStartupCurrentMilestones (MilestoneService)

variable {input : Input} {events : List CampusTCPModel.Event} {report : Report input events}
variable {current : C.State input.active input.passive}

private theorem rank_of_entry (selected : phase.entry = some entry) : 1 ≤ phaseRank phase := by
  cases phase <;> first | (solve | cases selected) | (simp only [phaseRank]; decide)

theorem ServiceChain.after_rank (history : ServiceChain initial services final) (served : Served input)
    (member : served ∈ services) (bound : count ≤ phaseRank (afterTransport served).admission.phase) :
    count ≤ phaseRank final.admission.phase := by
  induction history with
  | nil => cases member
  | cons head primary before rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst served
      exact Nat.le_trans bound (CampusTCPRecoveryStartupTransport.ServiceChain.phase_rank rest)
    · exact ih later

private theorem admitted_synAck_rank (result : AdmissionExecution.Result mode before packet lifecycle prepared)
    (flags : packet.packet.segment.flags = 18) : 2 ≤ phaseRank (AdmissionExecution.Result.state result).phase := by
  cases phase : before.phase with
  | empty =>
    have allowed := AdmissionExecution.Result.legacy_empty result phase
    simp only [Admission.Allowed, phase] at allowed
    exact False.elim ((by decide : (18 : UInt8) ≠ 2) (flags.symm.trans allowed.2.2.1))
  | syn entry iss window mss =>
    obtain ⟨offer, read, after⟩ := AdmissionExecution.Result.learned_synAck_control result phase flags
    rw [after]
    change (2 : Nat) ≤ 2
    decide
  | synAck entry clientISS clientWindow serverISS serverWindow clientMSS serverMSS =>
    have before : 2 ≤ phaseRank before.phase := by simp only [phase, phaseRank]; decide
    exact Nat.le_trans before (CampusTCPRecoveryStartupTransport.admission_phase_rank result)
  | data session =>
    have before : 2 ≤ phaseRank before.phase := by simp only [phase, phaseRank]; decide
    exact Nat.le_trans before (CampusTCPRecoveryStartupTransport.admission_phase_rank result)

theorem MilestoneService.gateway_rank (value : MilestoneService report stamp template received actor kind)
    (primary : CampusTCPRecoveryStartupTransport.PrimaryServices report) :
    1 ≤ phaseRank report.final.primary.transport.admission.phase := by
  let served := value.actual.delivery.receipt.served
  obtain ⟨processing, selected, emitted⟩ := served.evidence.processed_of_output
    value.actual.delivery.receipt.emission value.actual.delivery.receipt.emitted
  have states := served.evidence.processing_states processing selected
  have committed := processing.output_committed value.actual.delivery.receipt.emission emitted
  have after : (afterTransport served).admission.phase.entry = some processing.prepared.attachment.entry := by
    change served.evidence.admission.phase.entry = _
    rw [states.2, committed]
    exact AdmissionExecution.Result.selected_entry processing.admitted
  apply ServiceChain.after_rank (CampusTCPRecoveryStartupTransport.Report.service_chain report primary) served
  · rw [← CampusTCPPrimaryTransport.Report.services report]
    exact value.actual.serviceMember
  · exact rank_of_entry after

theorem MilestoneService.gateway_synAck_rank (value : MilestoneService report stamp template received actor kind)
    (primary : CampusTCPRecoveryStartupTransport.PrimaryServices report) (flags : template.packet.segment.flags = 18) :
    2 ≤ phaseRank report.final.primary.transport.admission.phase := by
  let served := value.actual.delivery.receipt.served
  obtain ⟨processing, selected, emitted⟩ := served.evidence.processed_of_output
    value.actual.delivery.receipt.emission value.actual.delivery.receipt.emitted
  have states := served.evidence.processing_states processing selected
  have committed := processing.output_committed value.actual.delivery.receipt.emission emitted
  have sourceFlags : served.ticket.value.source.packet.segment.flags = 18 := by
    exact (congrArg (fun packet : Admission.Input => packet.packet.segment.flags) value.packet).trans flags
  have after : 2 ≤ phaseRank (afterTransport served).admission.phase := by
    change 2 ≤ phaseRank served.evidence.admission.phase
    rw [states.2, committed]
    exact admitted_synAck_rank processing.admitted sourceFlags
  apply ServiceChain.after_rank (CampusTCPRecoveryStartupTransport.Report.service_chain report primary) served
  · rw [← CampusTCPPrimaryTransport.Report.services report]
    exact value.actual.serviceMember
  · exact after

theorem Report.answered_gateway_rank (report : Report input events) (connected : report.final.connection = .recovering current)
    (primary : CampusTCPRecoveryStartupTransport.PrimaryServices report) (phase : current.phase = .answered answered) :
    1 ≤ phaseRank report.final.primary.transport.admission.phase := by
  obtain ⟨past⟩ := CampusTCPRecoveryStartupCurrentMilestones.Report.answered_syn report connected phase
  exact MilestoneService.gateway_rank past primary

theorem Report.acknowledged_gateway_rank (report : Report input events) (connected : report.final.connection = .recovering current)
    (primary : CampusTCPRecoveryStartupTransport.PrimaryServices report) (phase : current.phase = .acknowledged acknowledged client) :
    2 ≤ phaseRank report.final.primary.transport.admission.phase := by
  obtain ⟨past⟩ := CampusTCPRecoveryStartupCurrentMilestones.Report.acknowledged_synAck report connected phase
  exact MilestoneService.gateway_synAck_rank past primary acknowledged.answered.pending.output_fields.2.2.2.2.1

theorem Report.complete_gateway_rank (report : Report input events) (connected : report.final.connection = .recovering current)
    (primary : CampusTCPRecoveryStartupTransport.PrimaryServices report) (phase : current.phase = .complete complete client server) :
    2 ≤ phaseRank report.final.primary.transport.admission.phase := by
  have origins := (CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connected).advancing_origins
  have milestones : TCPHandshakeRecovery.CompleteMilestones current.receipts complete := by
    simpa only [TCPHandshakeRecovery.AdvancingOrigins, phase] using origins
  obtain ⟨past⟩ := CampusTCPRecoveryStartupCurrentMilestones.Report.milestone_service report connected milestones.2.1
  exact MilestoneService.gateway_synAck_rank past primary complete.certificate.passivePending.output_fields.2.2.2.2.1

def requiredLevel : TCPHandshakeRecovery.Kind → Nat
  | .syn => 0
  | .synAck | .synReplyAck => 1
  | .finalAck => 2

theorem Report.output_gateway_floor (report : Report input events) (connected : report.final.connection = .recovering current)
    (primary : CampusTCPRecoveryStartupTransport.PrimaryServices report) (member : output ∈ current.emissions) :
    requiredLevel output.kind ≤ phaseRank report.final.primary.transport.admission.phase := by
  have availability := (CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connected).output_phase member
  cases phase : current.phase with
  | idle =>
    cases kind : output.kind <;> simp only [kind, TCPHandshakeRecovery.Kind.phaseFloor, phase, TCPHandshakeRecovery.phaseLevel] at availability <;> omega
  | opened opened =>
    cases kind : output.kind <;> simp only [kind, TCPHandshakeRecovery.Kind.phaseFloor, phase, TCPHandshakeRecovery.phaseLevel] at availability
    · exact Nat.zero_le _
    all_goals omega
  | answered answered =>
    have bound := Report.answered_gateway_rank report connected primary phase
    cases kind : output.kind <;> simp only [requiredLevel]
    · exact Nat.zero_le _
    · exact bound
    · simp only [kind, TCPHandshakeRecovery.Kind.phaseFloor, phase, TCPHandshakeRecovery.phaseLevel] at availability
      omega
    · exact bound
  | acknowledged acknowledged client =>
    have bound := Report.acknowledged_gateway_rank report connected primary phase
    cases kind : output.kind <;> simp only [requiredLevel] <;> omega
  | complete complete client server =>
    have bound := Report.complete_gateway_rank report connected primary phase
    cases kind : output.kind <;> simp only [requiredLevel] <;> omega

end Netlib.Check.CampusTCPRecoveryStartupCurrentFloors
