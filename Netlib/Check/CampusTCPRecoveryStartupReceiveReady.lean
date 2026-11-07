import Netlib.Check.CampusTCPRecoveryStartupReceiveFields
import Netlib.Check.CampusTCPRecoveryStartupDuplicateInput
import Netlib.Check.CampusTCPRecoveryStartupReceiveIndex
import Netlib.Check.TCPHandshakeRecoveryAckInventoryFacts
import Netlib.Check.TCPHandshakeRecoveryPhaseOrderFacts

/-!
# Receive readiness from the actual current startup link

Past advancing receipts determine duplicate inputs. Current packet and ACK
inventories exclude source kinds that the reached phase cannot have emitted.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupReceiveReady

open Packet Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupCurrentNative (Current)
open CampusTCPRecoveryStartupReceiveFields (Fields PassiveTarget)
open CampusTCPRecoveryStartupDuplicateInput (StoredEmission)

namespace J
export CampusTCPStartupJobs (Source PacketItem)
end J
namespace R
export TCPHandshakeRecovery (ReceiveInput ReceiveFields ReceiveIndex)
end R

variable {input : Input} {baseEvents events : List CampusTCPModel.Event}
variable {base : Report input baseEvents} {report : Report input events}
variable {current : C.State input.active input.passive} {header : Header}
variable {profile : CampusTCPStartupNative.Profile (input.contextFor .primary)
  (beforeService input base.final .primary) input.zone header}

private theorem same_decoded (same : first = second) : TCPHandshakeRecovery.SameDecoded first second :=
  ⟨congrArg (fun packet : Handshake.Input => packet.packet.header) same,
    congrArg (fun packet : Handshake.Input => packet.packet.segment) same⟩

private theorem milestone_input (stored : StoredEmission report) (value : Current base profile report current)
    (control : TCPHandshakeRecovery.TemplateKind stored.source.occurrence.kind)
    (past : TCPHandshakeRecovery.AdvancingReceipt current.receipts stamp template received actor kind)
    (selectedKind : stored.source.occurrence.kind = kind) : stored.emission.asInput = received := by
  obtain ⟨receipt, member, index, source, inputEq, actorEq, kindEq⟩ := past
  exact (stored.same_prior_receive value receipt member control (selectedKind.trans kindEq.symm)).trans inputEq

private theorem source_template (value : Current base profile report current)
    (member : source ∈ current.emissions) (control : TCPHandshakeRecovery.TemplateKind source.kind)
    (selected : current.phase.controlTemplate source.kind = some original) : source.packet = original := by
  have known := (CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report value.connected).packet_inventory.templates source member control
  exact Option.some.inj (known.symm.trans selected)

theorem receive_ready (value : Current base profile report current) (valid : input.passive.Valid)
    (target : PassiveTarget profile.entry input.passive)
    (item : J.PacketItem input) (serviceIndex : Nat) (served : Served input)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (source : J.Source input) (production : served.ticket.value.produced = source.produced)
    (payload : item.value.payload = .link serviceIndex served emission emitted)
    (pending : item ∈ report.final.custody.pending) :
    ∃ received : R.ReceiveInput current report.final.time .rewrite,
      received.source = source.occurrence ∧ received.packet = emission.asInput ∧
        received.event = .receive source.occurrence.index emission.bytes .rewrite true ∧
        R.ReceiveIndex current report.final.time ∧ R.ReceiveFields current received.receipt := by
  obtain ⟨received, sourceEq, packetEq, eventEq⟩ := CampusTCPRecoveryStartupLinkInput.link_input report value.connected
    item serviceIndex served emission emitted source production payload pending
  have fields := CampusTCPRecoveryStartupReceiveFields.link_fields value item serviceIndex served emission emitted
    source production payload pending
  let stored := StoredEmission.ofLink report item serviceIndex served emission emitted source production payload pending
  have reachable := CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report value.connected
  have fresh : ∀ old, current.last = some old → old < report.final.time :=
    fun _ last => CampusTCPRecoveryStartupReceiveIndex.Report.recovery_last_earlier report value.connected last
  refine ⟨received, sourceEq, packetEq, eventEq,
    CampusTCPRecoveryStartupReceiveIndex.Report.receive_index report value.connected, ?_⟩
  simp only [TCPHandshakeRecovery.ReceiveFields, TCPHandshakeRecovery.ReceiveInput.receipt,
    sourceEq, received.same, packetEq]
  refine ⟨fields.shape.actorEq, ?_⟩
  cases kind : source.occurrence.kind with
  | syn =>
    have control : TCPHandshakeRecovery.TemplateKind source.occurrence.kind := Or.inl kind
    cases phase : current.phase with
    | idle =>
      have absent := reachable.packet_inventory.templates source.occurrence fields.member control
      rw [phase, kind] at absent
      change (none : Option Handshake.Input) = some source.occurrence.packet at absent
      cases absent
    | opened opened =>
      simpa only [kind, phase] using fields.syn_opened value kind phase valid target
    | answered answered =>
      have origins : TCPHandshakeRecovery.AnsweredMilestones current.receipts answered := by
        simpa only [TCPHandshakeRecovery.AdvancingOrigins, phase] using reachable.advancing_origins
      have same := milestone_input stored value control origins kind
      exact ⟨source_template value fields.member control (by rw [phase, kind]; rfl), same_decoded same⟩
    | acknowledged acknowledged client =>
      have origins : TCPHandshakeRecovery.AcknowledgedMilestones current.receipts acknowledged := by
        simpa only [TCPHandshakeRecovery.AdvancingOrigins, phase] using reachable.advancing_origins
      have same := milestone_input stored value control origins.1 kind
      exact ⟨source_template value fields.member control (by rw [phase, kind]; rfl), same_decoded same⟩
    | complete complete client server =>
      have origins : TCPHandshakeRecovery.CompleteMilestones current.receipts complete := by
        simpa only [TCPHandshakeRecovery.AdvancingOrigins, phase] using reachable.advancing_origins
      have same := milestone_input stored value control origins.1 kind
      exact ⟨source_template value fields.member control (by rw [phase, kind]; rfl), same_decoded same⟩
  | synAck =>
    have control : TCPHandshakeRecovery.TemplateKind source.occurrence.kind := Or.inr kind
    cases phase : current.phase with
    | idle | opened opened =>
      have absent := reachable.packet_inventory.templates source.occurrence fields.member control
      rw [phase, kind] at absent
      change (none : Option Handshake.Input) = some source.occurrence.packet at absent
      cases absent
    | answered answered =>
      simpa only [kind, phase] using fields.synAck_answered value kind phase
    | acknowledged acknowledged client =>
      have origins : TCPHandshakeRecovery.AcknowledgedMilestones current.receipts acknowledged := by
        simpa only [TCPHandshakeRecovery.AdvancingOrigins, phase] using reachable.advancing_origins
      have same := milestone_input stored value control origins.2 kind
      exact ⟨source_template value fields.member control (by rw [phase, kind]; rfl), same_decoded same⟩
    | complete complete client server =>
      have origins : TCPHandshakeRecovery.CompleteMilestones current.receipts complete := by
        simpa only [TCPHandshakeRecovery.AdvancingOrigins, phase] using reachable.advancing_origins
      have same := milestone_input stored value control origins.2.1 kind
      exact ⟨source_template value fields.member control (by rw [phase, kind]; rfl), same_decoded same⟩
  | finalAck =>
    have ack : TCPHandshakeRecovery.AckKind source.occurrence.kind := Or.inl kind
    cases phase : current.phase with
    | idle | opened opened | answered answered =>
      have absent := reachable.ack_inventory.templates source.occurrence fields.member ack
      rw [phase, kind] at absent
      change (none : Option Handshake.Input) = some source.occurrence.packet at absent
      cases absent
    | acknowledged acknowledged client =>
      have ordered := reachable.phase_order.acknowledged_before phase fresh
      exact ⟨reachable.acknowledged_finalAck_template phase fields.member kind,
        fields.final_ack_accepted value kind phase, ordered⟩
    | complete complete client server =>
      exact fields.empty_ack_complete_server value kind phase
  | synReplyAck =>
    have ack : TCPHandshakeRecovery.AckKind source.occurrence.kind := Or.inr kind
    cases phase : current.phase with
    | idle | opened opened =>
      have absent := reachable.ack_inventory.templates source.occurrence fields.member ack
      rw [phase, kind] at absent
      change (none : Option Handshake.Input) = some source.occurrence.packet at absent
      cases absent
    | answered answered => exact fields.discard_answered value kind phase
    | acknowledged acknowledged client => exact fields.empty_ack_acknowledged value kind phase
    | complete complete client server => exact fields.empty_ack_complete_client value kind phase

end Netlib.Check.CampusTCPRecoveryStartupReceiveReady
