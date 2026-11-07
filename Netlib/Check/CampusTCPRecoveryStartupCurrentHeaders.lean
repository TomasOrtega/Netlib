import Netlib.Check.CampusTCPRecoveryStartupCurrentEntry
import Netlib.Check.CampusTCPRecoveryStartupCurrentMilestones
import Netlib.Check.CampusTCPRecoveryStartupFold

/-!
# Current startup headers across the actual NAT service

The passive header comes from the real delivered SYN and its gateway output.
No equality between configured endpoint sockets is assumed.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupCurrentHeaders

open Packet Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupCurrentMilestones (MilestoneService)
open CampusTCPRecoveryStartupCurrentEntry (EntryMatches)
open CampusTCPRecoveryStartupTransport (PrimaryServices)

variable {input : Input} {events : List CampusTCPModel.Event} {report : Report input events}
variable {current : C.State input.active input.passive} {entry : NetfilterNAT.Entry}

private theorem Receipt.header (receipt : CampusTCPModel.Receipt input) :
    receipt.received.packet.header = receipt.emission.target := by
  have decoded := receipt.received.checked
  rw [receipt.bytes] at decoded
  have same := Except.ok.inj (decoded.symm.trans receipt.emission.decoded_eq)
  exact (congrArg DecodedIPv4.header same).trans receipt.emission.header

theorem MilestoneService.syn_input_header (value : MilestoneService report stamp template received .active .syn)
    (primary : PrimaryServices report) (matching : EntryMatches entry report.final.primary.transport.admission)
    (flags : template.packet.segment.flags = 2) : received.packet.header = entry.flow.output .original := by
  let served := value.actual.delivery.receipt.served
  have stored : served ∈ report.steps.filterMap (·.result.service) := by
    rw [← CampusTCPPrimaryTransport.Report.services report]
    exact value.actual.serviceMember
  obtain ⟨processing, selected, actualEntry⟩ := CampusTCPRecoveryStartupFold.ServiceChain.output_entry
    (CampusTCPRecoveryStartupTransport.Report.service_chain report primary) served stored
    value.actual.delivery.receipt.emission value.actual.delivery.receipt.emitted
  have entryEq := matching _ actualEntry
  have sourceFlags : served.ticket.value.source.packet.segment.flags = 2 :=
    (congrArg (fun packet : Admission.Input => packet.packet.segment.flags) value.packet).trans flags
  have direction := CampusTCPRecoveryStartupKeys.syn_original processing.admitted sourceFlags
  have target := processing.output_target value.actual.delivery.receipt.emission (by
    obtain ⟨_, _, emitted⟩ := served.evidence.processed_of_output
      value.actual.delivery.receipt.emission value.actual.delivery.receipt.emitted
    have same := Option.some.inj (selected.symm.trans (by assumption))
    cases same
    exact emitted)
  have inputEq := value.actual.delivery.sameInput
  rw [value.actual.receiptEq, value.receivedEq] at inputEq
  rw [← inputEq]
  exact (Receipt.header value.actual.delivery.receipt).trans (target.trans (by rw [entryEq, direction]))

private theorem passive_template_header (value : MilestoneService report stamp template received .active .syn)
    (primary : PrimaryServices report) (matching : EntryMatches entry report.final.primary.transport.admission)
    (flags : template.packet.segment.flags = 2) (pending : Handshake.SynReceived)
    (listened : Handshake.listenSyn localConfig received permission = .ok pending) :
    pending.output.packet.header = entry.flow.input .reply := by
  have inputEq := (Handshake.listenSyn_fields _ _ _ _ listened).2.1
  rw [pending.output_fields.1, inputEq, MilestoneService.syn_input_header value primary matching flags]
  exact FlowNAT.Entry.original_output_reverse entry.flow

theorem Report.passive_header (report : Report input events) (connected : report.final.connection = .recovering current)
    (primary : PrimaryServices report) (matching : EntryMatches entry report.final.primary.transport.admission)
    (member : output ∈ current.emissions) (actor : output.actor = .passive) :
    output.packet.packet.header = entry.flow.input .reply := by
  have header := (CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connected).packet_inventory.headers output member
  rw [actor] at header
  cases phase : current.phase with
  | idle | opened _ => simp only [phase, TCPHandshakeRecovery.Phase.sourceHeader] at header; cases header
  | answered answered =>
    obtain ⟨past⟩ := CampusTCPRecoveryStartupCurrentMilestones.Report.answered_syn report connected phase
    have expected := passive_template_header past primary matching answered.opened.pending.output_fields.2.2.2.2.1
      answered.pending answered.computed
    have same : answered.pending.output.packet.header = output.packet.packet.header := by
      simpa only [phase, TCPHandshakeRecovery.Phase.sourceHeader, Option.some.injEq] using header
    exact same.symm.trans expected
  | acknowledged acknowledged client =>
    obtain ⟨past⟩ := CampusTCPRecoveryStartupCurrentMilestones.Report.acknowledged_syn report connected phase
    have expected := passive_template_header past primary matching acknowledged.answered.opened.pending.output_fields.2.2.2.2.1
      acknowledged.answered.pending acknowledged.answered.computed
    have same : acknowledged.answered.pending.output.packet.header = output.packet.packet.header := by
      simpa only [phase, TCPHandshakeRecovery.Phase.sourceHeader, Option.some.injEq] using header
    exact same.symm.trans expected
  | complete complete client server =>
    have origins := (CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connected).advancing_origins
    have milestones : TCPHandshakeRecovery.CompleteMilestones current.receipts complete := by
      simpa only [TCPHandshakeRecovery.AdvancingOrigins, phase] using origins
    obtain ⟨past⟩ := CampusTCPRecoveryStartupCurrentMilestones.Report.milestone_service report connected milestones.1
    have expected := passive_template_header past primary matching complete.certificate.activePending.output_fields.2.2.2.2.1
      complete.certificate.passivePending complete.certificate.listened
    have same : complete.certificate.passivePending.output.packet.header = output.packet.packet.header := by
      simpa only [phase, TCPHandshakeRecovery.Phase.sourceHeader, Option.some.injEq] using header
    exact same.symm.trans expected

end Netlib.Check.CampusTCPRecoveryStartupCurrentHeaders
