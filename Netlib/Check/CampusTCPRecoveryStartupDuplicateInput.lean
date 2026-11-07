import Netlib.Check.CampusTCPRecoveryStartupLinkTarget
import Netlib.Check.CampusTCPRecoveryStartupReceiptSteps
import Netlib.Protocol.TCP.WireForwardingEmissionDeterminism

/-!
# Equal received controls from actual stored emissions

The comparison joins literal source occurrences and their recorded services.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupDuplicateInput

open Packet Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupPhase (sideDirection)

namespace J
export CampusTCPStartupJobs (Source PacketItem)
end J
namespace R
export CampusTCPRecoveryStartupReceiptSteps (ActualReceipt)
end R
namespace N
export CampusTCPRecoveryStartupCurrentNative (Current)
end N

variable {input : Input} {baseEvents events : List CampusTCPModel.Event}
variable {base : Report input baseEvents} {report : Report input events}
variable {current : C.State input.active input.passive} {header : Header}
variable {controlStep : C.Step input.active input.passive} {receipt : C.Receipt}
variable {profile : CampusTCPStartupNative.Profile (input.contextFor .primary)
  (beforeService input base.final .primary) input.zone header}

structure StoredEmission (report : Report input events) where
  served : Served input
  member : served ∈ report.final.services
  emission : W.Emission served.ticket.value.source.packet
  emitted : served.evidence.output = some emission
  source : J.Source input
  production : served.ticket.value.produced = source.produced

def StoredEmission.ofLink (report : Report input events)
    (item : J.PacketItem input) (serviceIndex : Nat) (served : Served input)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (source : J.Source input) (production : served.ticket.value.produced = source.produced)
    (payload : item.value.payload = .link serviceIndex served emission emitted)
    (pending : item ∈ report.final.custody.pending) : StoredEmission report := by
  have selected := CampusTCPCustodyFacts.Report.sources report item (List.mem_append_right _ pending)
  rw [payload] at selected
  exact ⟨served, List.mem_of_getElem? selected, emission, emitted, source, production⟩

theorem StoredEmission.source_member (stored : StoredEmission report)
    (connected : report.final.connection = .recovering current) : stored.source.occurrence ∈ current.emissions := by
  obtain ⟨origin⟩ := CampusTCPRecoveryStartupSources.Report.service_source report stored.served stored.member
  exact origin.recovering_member stored.source.actual stored.source.occurrence stored.source.emitted
    stored.production current connected

theorem StoredEmission.target (stored : StoredEmission report) (value : N.Current base profile report current) :
    stored.emission.target = profile.entry.flow.output (sideDirection stored.source.occurrence.actor) := by
  have member := stored.source_member value.connected
  have services : stored.served ∈ report.steps.filterMap (·.result.service) := by
    rw [← CampusTCPPrimaryTransport.Report.services report]
    exact stored.member
  obtain ⟨processing, selected, actualEntry⟩ := CampusTCPRecoveryStartupFold.ServiceChain.output_entry
    (CampusTCPRecoveryStartupTransport.Report.service_chain report value.primary) stored.served services stored.emission stored.emitted
  have entryEq := value.entry _ actualEntry
  have packetHeader : stored.served.ticket.value.source.packet.header =
      profile.entry.flow.input (sideDirection stored.source.occurrence.actor) := by
    change stored.served.ticket.value.produced.output.packet.header = _
    rw [stored.production]
    exact value.headers stored.source.occurrence member
  have key := AdmissionExecution.Result.selectedKey processing.admitted
  change processing.prepared.attachment.entry.flow.key processing.prepared.attachment.direction =
    (input.zone, stored.served.ticket.value.source.packet.header) at key
  rw [entryEq, packetHeader] at key
  have expected : profile.entry.flow.key (sideDirection stored.source.occurrence.actor) =
      (input.zone, profile.entry.flow.input (sideDirection stored.source.occurrence.actor)) := by
    rw [FlowNAT.Entry.key, profile.zone_eq]
  have direction := CampusTCPRecoveryStartupKeys.direction_of_key profile.compatible (key.trans expected.symm)
  have output : processing.outcome.output = some stored.emission := by
    obtain ⟨other, recorded, output⟩ := stored.served.evidence.processed_of_output stored.emission stored.emitted
    have same := Option.some.inj (selected.symm.trans recorded)
    cases same
    exact output
  exact (processing.output_target stored.emission output).trans (by rw [entryEq, direction])

theorem StoredEmission.same_input (first second : StoredEmission report)
    (value : N.Current base profile report current)
    (control : TCPHandshakeRecovery.TemplateKind first.source.occurrence.kind)
    (kind : first.source.occurrence.kind = second.source.occurrence.kind) :
    first.emission.asInput = second.emission.asInput := by
  have firstMember := first.source_member value.connected
  have secondMember := second.source_member value.connected
  have reachable := CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report value.connected
  have packet := reachable.same_control_template firstMember secondMember control kind
  have sameInput : first.served.ticket.value.source.packet = second.served.ticket.value.source.packet := by
    change first.served.ticket.value.produced.output.packet = second.served.ticket.value.produced.output.packet
    rw [first.production, second.production]
    exact congrArg EstablishedReceive.Input.packet packet
  have firstRole := (reachable.output_shape firstMember).actorEq
  have secondRole := (reachable.output_shape secondMember).actorEq
  have sameActor := firstRole.trans ((congrArg TCPHandshakeRecovery.Kind.actor kind).trans secondRole.symm)
  have sameTarget : first.emission.target = second.emission.target := by
    rw [first.target value, second.target value, sameActor]
  exact (Netlib.Protocol.TCP.WireForwarding.Emission.fields_eq_of_input_target first.emission second.emission sameInput sameTarget).2.2.2.2

private theorem input_eq_of_bytes (first second : EstablishedReceive.Input)
    (same : first.bytes = second.bytes) : first = second := by
  cases first with
  | mk bytes packet checked =>
    cases second with
    | mk other decoded verified =>
      dsimp only at same
      subst other
      have equal := Except.ok.inj (checked.symm.trans verified)
      subst decoded
      rfl

theorem receipt_input (receipt : CampusTCPModel.Receipt input) : receipt.received = receipt.emission.asInput :=
  input_eq_of_bytes receipt.received receipt.emission.asInput receipt.bytes

def StoredEmission.ofActualReceipt (past : R.ActualReceipt report controlStep receipt) : StoredEmission report :=
  ⟨past.delivery.receipt.served, past.serviceMember, past.delivery.receipt.emission, past.delivery.receipt.emitted,
    ⟨past.delivery.sourceStep, past.delivery.occurrence, past.delivery.present⟩, past.delivery.production⟩

theorem actual_receipt_source (past : R.ActualReceipt report controlStep receipt) : past.delivery.occurrence = receipt.source := by
  have same := past.source.sourceEq
  rw [past.receiptEq] at same
  exact same.symm

theorem actual_receipt_input (past : R.ActualReceipt report controlStep receipt) :
    receipt.delivery.input = past.delivery.receipt.emission.asInput := by
  have same := past.delivery.sameInput
  rw [past.receiptEq] at same
  exact same.symm.trans (receipt_input past.delivery.receipt)

theorem StoredEmission.same_prior_receive (stored : StoredEmission report)
    (value : N.Current base profile report current) (receipt : C.Receipt) (member : receipt ∈ current.receipts)
    (control : TCPHandshakeRecovery.TemplateKind stored.source.occurrence.kind)
    (kind : stored.source.occurrence.kind = receipt.source.kind) : stored.emission.asInput = receipt.delivery.input := by
  let reachable := CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report value.connected
  obtain ⟨origin⟩ := reachable.receipt_origin member
  have recorded : origin.actual ∈ report.steps.filterMap (·.result.recovery) := by
    change origin.actual ∈ reachable.steps
    have inside : origin.actual ∈ origin.prior ++ origin.actual :: origin.later :=
      List.mem_append_right _ List.mem_cons_self
    exact (congrArg (fun steps => origin.actual ∈ steps) origin.history).mpr inside
  obtain ⟨source, bytes, path, policy, event, _, _, _⟩ :=
    TCPHandshakeRecovery.evaluate_receipt_event origin.actual.computed origin.recorded
  obtain ⟨past⟩ := CampusTCPRecoveryStartupReceiptSteps.Report.actual_receipt report origin.actual recorded receipt origin.recorded event
  let previous := StoredEmission.ofActualReceipt past
  have sameKind : stored.source.occurrence.kind = previous.source.occurrence.kind := by
    change stored.source.occurrence.kind = past.delivery.occurrence.kind
    rw [actual_receipt_source past]
    exact kind
  have same := stored.same_input previous value control sameKind
  exact same.trans (actual_receipt_input past).symm

end Netlib.Check.CampusTCPRecoveryStartupDuplicateInput
