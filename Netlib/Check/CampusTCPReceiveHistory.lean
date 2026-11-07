import Netlib.Check.CampusTCPReceiveCases
import Netlib.Check.CampusTCPApplicationProductionFacts
import Netlib.Check.CampusTCPApplicationHistory
import Netlib.Protocol.TCP.ApplicationPayloadHistory

/-!
# Actual application and startup receive histories

Startup ACKs keep their actual recovery producer and gateway lineage.
Nonempty payload keeps the peer application output that supplied it.
-/

namespace Netlib.Check.CampusTCPReceiveHistory

open Protocol.TCP CampusTCPModel CampusTCPEnabled

namespace F
export CampusTCPFacts (ReceiveAt ServiceAt Lineage ApplicationDelivery)
end F

namespace AH
export CampusTCPApplicationHistory (connectionSteps)
end AH

namespace R
export CampusTCPRecoveryReceipts (Delivery Source LocalAck)
end R

variable {input : Input} {events : List Event} {report : Report input events}
variable {actor : Actor} {operation : T.Step}

structure StartupDelivery (report : Report input events) (actor : Actor) (operation : T.Step) where
  receive : F.ReceiveAt report actor operation
  service : F.ServiceAt receive
  lineage : F.Lineage report receive
  control : C.Step input.active input.passive
  recorded : receive.joint.step.result.recovery = some control
  delivery : R.Delivery receive.joint.step control
  receiptEq : delivery.receipt = receive.receipt
  source : R.Source report delivery
  ack : R.LocalAck delivery actor operation

inductive ReceiveSource (report : Report input events) (peer : List T.Step) (actor : Actor) (operation : T.Step) where
  | application (delivery : F.ApplicationDelivery report peer actor operation)
  | startup (delivery : StartupDelivery report actor operation)

def ReceiveSource.receive (value : ReceiveSource report peer actor operation) : F.ReceiveAt report actor operation :=
  match value with
  | .application delivery => delivery.receive
  | .startup delivery => delivery.receive

private theorem application_delivery (joint : Step input) (member : joint ∈ report.steps)
    (recorded : joint.result.application = some (actor, operation))
    (packet : EstablishedReceive.Input) (received : operation.event = .receive packet)
    (value : CampusTCPReceiveCases.ApplicationCase joint.before joint.event joint.result actor operation packet) :
    Nonempty (F.ApplicationDelivery report (AH.connectionSteps report.final.connection actor.other) actor operation) := by
  let receive : F.ReceiveAt report actor operation :=
    ⟨⟨joint, member, value.stamp.symm⟩, value.service, value.raw, value.policy, value.event,
      value.receipt, value.recorded, recorded, packet, received, value.same, value.receiver⟩
  obtain ⟨service⟩ := CampusTCPStartupOrigins.DeliveryAt.service_exists receive.delivery
  have lineage := CampusTCPFacts.gateway_lineage receive.delivery service
  have other : value.sourceActor = actor.other := by
    have opposite := value.receipt.receiver
    rw [value.production] at opposite
    simp only [Produced.actor] at opposite
    have receiver := value.receiver
    cases sourceActor : value.sourceActor <;> cases actor <;> simp_all [Actor.other]
  have storedLineage := lineage
  obtain ⟨producer, assignment, outputIndex, ingress, producerMember, _, producerOutput, _⟩ := storedLineage
  change producer.result.output = some value.receipt.served.ticket.value.produced at producerOutput
  rw [value.production] at producerOutput
  have sourceRecorded := CampusTCPApplicationProductionFacts.Step.application_output_recorded producer
    value.sourceActor value.sourceStep value.output value.origin producerOutput
  have sourceMember : value.sourceStep ∈ AH.connectionSteps report.final.connection actor.other := by
    have retained := CampusTCPApplicationHistory.Report.application_member report producer producerMember
      value.sourceActor value.sourceStep sourceRecorded
    simpa only [other] using retained
  obtain ⟨prior, later, history⟩ := List.mem_iff_append.mp sourceMember
  let source : T.OutputAt (AH.connectionSteps report.final.connection actor.other) :=
    ⟨prior, value.sourceStep, later, history, value.output, value.origin⟩
  have path : ApplicationTrace.BytePath source.output receive.received := by
    rw [← receive.same]
    simpa only [value.production, Produced.output] using value.receipt.bytePath
  have earlier : source.step.stamp < operation.stamp := by
    have ordered := CampusTCPFacts.GatewayLineage.source_earlier lineage
    change value.receipt.served.ticket.value.produced.time < value.receipt.time at ordered
    simp only [value.production, Produced.time] at ordered
    have time := (CampusTCPFacts.deliver_origin joint value.service value.raw value.policy value.event value.receipt value.recorded).1
    change value.sourceStep.stamp < operation.stamp
    have stamp := value.stamp
    omega
  exact ⟨⟨receive, service, lineage, source,
    ⟨value.sourceActor, value.sourceStep, value.output, value.origin, value.production, other, rfl, rfl⟩,
    path, earlier⟩⟩

theorem Report.receive_source (report : Report input events) (actor : Actor) (operation : T.Step)
    (member : operation ∈ AH.connectionSteps report.final.connection actor)
    (packet : EstablishedReceive.Input) (received : operation.event = .receive packet) :
    Nonempty (ReceiveSource report (AH.connectionSteps report.final.connection actor.other) actor operation) := by
  obtain ⟨joint, jointMember, recorded⟩ := CampusTCPApplicationHistory.Report.application_origin report actor operation member
  obtain ⟨cases⟩ := CampusTCPReceiveCases.Step.receive_cases joint actor operation recorded packet received
  cases cases with
  | application value =>
    obtain ⟨delivery⟩ := application_delivery joint jointMember recorded packet received value
    exact ⟨.application delivery⟩
  | recovery control present delivery ack same =>
    obtain ⟨source⟩ := delivery.report_source report jointMember
    have stamp := ack.ack.2.2.2.2.2.2.2.2
    let receive : F.ReceiveAt report actor operation :=
      ⟨⟨joint, jointMember, stamp.symm⟩, delivery.service, delivery.bytes, delivery.policy, delivery.event,
        delivery.receipt, delivery.recorded, recorded, packet, received, same, source.local_actor ack⟩
    obtain ⟨service⟩ := CampusTCPStartupOrigins.DeliveryAt.service_exists receive.delivery
    have lineage := CampusTCPFacts.gateway_lineage receive.delivery service
    exact ⟨.startup ⟨receive, service, lineage, control, present, delivery, rfl, source, ack⟩⟩

def Receives (report : Report input events) (actor : Actor) : Prop :=
  ∀ operation ∈ AH.connectionSteps report.final.connection actor,
    ∀ packet, operation.event = .receive packet →
      Nonempty (ReceiveSource report (AH.connectionSteps report.final.connection actor.other) actor operation)

theorem Report.receives (report : Report input events) (actor : Actor) : Receives report actor :=
  Report.receive_source report actor

private theorem released_empty (operation : T.Step) (empty : operation.acceptedPayload = []) :
    operation.releasedPayload = [] := by
  cases transition : operation.storeTransition with
  | stutter same released => exact released
  | accepted allocation => exact False.elim (allocation.accepted_payload_nonempty empty)

theorem StartupDelivery.payloads (delivery : StartupDelivery report actor operation) :
    operation.acceptedPayload = [] ∧ operation.releasedPayload = [] := by
  have ack := delivery.ack
  have empty : operation.acceptedPayload = [] := by
    simp only [ApplicationTrace.Step.acceptedPayload, ApplicationTrace.acceptedPayload,
      ack.ack.2.1, ack.ack.2.2.2.2.2.1]
    exact ack.ack.1.2.2
  exact ⟨empty, released_empty operation empty⟩

theorem StartupDelivery.quiet (delivery : StartupDelivery report actor operation) :
    operation.result.output = none ∧ operation.result.read = [] :=
  ⟨delivery.ack.ack.2.2.2.2.2.2.1, delivery.ack.ack.2.2.2.2.2.2.2.1⟩

theorem ReceiveSource.application_nonempty (value : ReceiveSource report peer actor operation)
    (nonempty : operation.acceptedPayload ≠ []) : Nonempty (F.ApplicationDelivery report peer actor operation) := by
  cases value with
  | application delivery => exact ⟨delivery⟩
  | startup delivery => exact False.elim (nonempty delivery.payloads.1)

theorem Report.payload_delivery (report : Report input events) (actor : Actor) (operation : T.Step)
    (member : operation ∈ AH.connectionSteps report.final.connection actor)
    (nonempty : operation.acceptedPayload ≠ []) :
    Nonempty (F.ApplicationDelivery report (AH.connectionSteps report.final.connection actor.other) actor operation) := by
  obtain ⟨packet, _, _, received, _, _⟩ := operation.data nonempty
  obtain ⟨source⟩ := Report.receive_source report actor operation member packet received
  exact source.application_nonempty nonempty

theorem connection_order (connection : Connection active passive) (actor : Actor) :
    ApplicationTrace.Chronological (AH.connectionSteps connection actor) := by
  cases connection with
  | startup stage pending => exact .nil
  | application complete endpoints =>
    cases actor
    · exact endpoints.client.ordered
    · exact endpoints.server.ordered
  | recovering current =>
    cases phase : current.phase <;> cases actor
    all_goals simp only [AH.connectionSteps, TCPHandshakeRecovery.State.applicationSteps, Actor.recoverySide, phase]
    all_goals first | exact .nil | exact TCPHandshakeRecovery.PreData.ordered _

theorem Report.payload_history (report : Report input events) (actor : Actor) :
    ApplicationTrace.PayloadDeliveryHistory (AH.connectionSteps report.final.connection actor.other)
      (AH.connectionSteps report.final.connection actor) := by
  refine ⟨connection_order _ _, connection_order _ _, ?_⟩
  intro operation member nonempty packet received
  obtain ⟨delivery⟩ := Report.payload_delivery report actor operation member nonempty
  have same := ApplicationTrace.Event.receive.inj (delivery.receive.event.symm.trans received)
  exact ⟨delivery.source, delivery.earlier, by simpa only [same] using delivery.path⟩

theorem Report.payload_paired_history (report : Report input events) :
    ApplicationTrace.PayloadDeliveryHistory (AH.connectionSteps report.final.connection .client)
      (AH.connectionSteps report.final.connection .server) ∧
    ApplicationTrace.PayloadDeliveryHistory (AH.connectionSteps report.final.connection .server)
      (AH.connectionSteps report.final.connection .client) :=
  ⟨Report.payload_history report .server, Report.payload_history report .client⟩

theorem ReceiveSource.payload_delivery (value : ReceiveSource report peer actor operation)
    (nonempty : operation.acceptedPayload ≠ []) : Nonempty (F.ApplicationDelivery report peer actor operation) :=
  value.application_nonempty nonempty

theorem Report.payload_application_delivery (report : Report input events) (actor : Actor) (operation : T.Step)
    (member : operation ∈ AH.connectionSteps report.final.connection actor)
    (nonempty : operation.acceptedPayload ≠ []) :
    Nonempty (F.ApplicationDelivery report (AH.connectionSteps report.final.connection actor.other) actor operation) :=
  Report.payload_delivery report actor operation member nonempty

def PayloadReceives (report : Report input events) (peer : List T.Step) (actor : Actor) (steps : List T.Step) : Prop :=
  ∀ operation ∈ steps, operation.acceptedPayload ≠ [] → Nonempty (F.ApplicationDelivery report peer actor operation)

theorem PayloadReceives.prefix (value : PayloadReceives report peer actor steps) (retained : prior <+: steps) :
    PayloadReceives report peer actor prior :=
  fun operation member => value operation (retained.subset member)

theorem Report.payload_receives (report : Report input events) (actor : Actor) :
    PayloadReceives report (AH.connectionSteps report.final.connection actor.other) actor
      (AH.connectionSteps report.final.connection actor) :=
  Report.payload_delivery report actor

theorem Report.payload_application_prefix (report : Report input events) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : report.final.connection = .application complete endpoints)
    (leftEpoch : (endpoints.client.steps.flatMap ApplicationTrace.Step.emitted).length < Seq.halfSpace)
    (rightEpoch : (endpoints.server.steps.flatMap ApplicationTrace.Step.emitted).length < Seq.halfSpace) :
    endpoints.server.steps.flatMap ApplicationTrace.Step.readBytes <+: endpoints.client.steps.flatMap ApplicationTrace.Step.written ∧
      endpoints.client.steps.flatMap ApplicationTrace.Step.readBytes <+: endpoints.server.steps.flatMap ApplicationTrace.Step.written := by
  have histories := Report.payload_paired_history report
  rw [connection] at histories
  have empty := complete.certificate.empty
  exact ApplicationTrace.payload_paired_application_prefix endpoints.client.chain endpoints.server.chain
    histories.1 histories.2 empty.1 empty.2.2.2.1 empty.2.1 empty.2.2.2.2.1 empty.2.2.1 empty.2.2.2.2.2
    complete.certificate.empty_receiveStore.1 complete.certificate.empty_receiveStore.2
    complete.certificate.cursors.1 complete.certificate.cursors.2 leftEpoch rightEpoch

theorem Report.payload_byte_origin (report : Report input events) (actor : Actor) (operation : T.Step)
    (member : operation ∈ AH.connectionSteps report.final.connection actor)
    (sourceChain : T.Chain sourceInitial (AH.connectionSteps report.final.connection actor.other) sourceFinal)
    (emptySent : sourceInitial.core.sent = []) (emptyPending : sourceInitial.pending = [])
    (index : Nat) (byte : UInt8) (selected : operation.acceptedPayload[index]? = some byte) :
    ∃ delivery : F.ApplicationDelivery report (AH.connectionSteps report.final.connection actor.other) actor operation,
      Nonempty (ApplicationTrace.AttemptByteOrigin sourceInitial (AH.connectionSteps report.final.connection actor.other)
        delivery.source index byte) := by
  have nonempty : operation.acceptedPayload ≠ [] := by intro empty; simp [empty] at selected
  obtain ⟨packet, count, size, event, accepted, payload⟩ := operation.data nonempty
  obtain ⟨delivery⟩ := Report.payload_delivery report actor operation member nonempty
  have same := ApplicationTrace.Event.receive.inj (event.symm.trans delivery.receive.event)
  have sourceByte : delivery.source.output.packet.segment.payload[index]? = some byte := by
    rw [payload, same, delivery.path.fields.1] at selected
    exact selected
  exact ⟨delivery, delivery.source.byte_origin sourceChain emptySent emptyPending
    (connection_order _ _) index byte sourceByte⟩

end Netlib.Check.CampusTCPReceiveHistory
