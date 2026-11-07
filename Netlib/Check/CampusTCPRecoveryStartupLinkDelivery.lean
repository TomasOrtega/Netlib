import Netlib.Check.CampusTCPRecoveryStartupReceiveReady
import Netlib.Check.CampusTCPRecoveryStartupDeliveryEnabled

/-!
# Enabled delivery of a current startup link

Raw endpoint configuration and the actual pending link derive the receive step.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupLinkDelivery

open Packet Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupCurrentNative (Current)
open CampusTCPRecoveryStartupReceiveFields (PassiveTarget)

namespace J
export CampusTCPStartupJobs (Source PacketItem)
end J
namespace D
export CampusTCPRecoveryStartupDeliveryEnabled (Delivery)
end D

variable {input : Input} {baseEvents events : List CampusTCPModel.Event}
variable {base : Report input baseEvents} {report : Report input events}
variable {current : C.State input.active input.passive} {header : Header}
variable {profile : CampusTCPStartupNative.Profile (input.contextFor .primary)
  (beforeService input base.final .primary) input.zone header}

structure Delivered (report : Report input events) (current : C.State input.active input.passive)
    (source : J.Source input) (index : Nat) (served : Served input)
    (emission : W.Emission served.ticket.value.source.packet) (actual : Step input) where
  receivedInput : TCPHandshakeRecovery.ReceiveInput current report.final.time .rewrite
  sourceEq : receivedInput.source = source.occurrence
  packetEq : receivedInput.packet = emission.asInput
  delivery : D.Delivery report receivedInput index served emission actual

theorem deliver (value : Current base profile report current) (valid : input.passive.Valid)
    (target : PassiveTarget profile.entry input.passive)
    (item : J.PacketItem input) (index : Nat) (served : Served input)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (source : J.Source input) (production : served.ticket.value.produced = source.produced)
    (payload : item.value.payload = .link index served emission emitted)
    (pending : item ∈ report.final.custody.pending) :
    ∃ actual, Nonempty (Delivered report current source index served emission actual) := by
  obtain ⟨received, sourceEq, packetEq, _, ordered, fields⟩ :=
    CampusTCPRecoveryStartupReceiveReady.receive_ready value valid target item index served emission emitted
      source production payload pending
  obtain ⟨actual, ⟨delivery⟩⟩ := CampusTCPRecoveryStartupDeliveryEnabled.deliver_input report value.connected
    item index served emission emitted source production payload pending received sourceEq packetEq ordered fields
  exact ⟨actual, ⟨⟨received, sourceEq, packetEq, delivery⟩⟩⟩

def Delivered.on_step (value : Delivered report current source index served emission actual)
    (supplied : Step input) (before : supplied.before = report.final)
    (event : supplied.event = .deliver index emission.bytes true) :
    Delivered report current source index served emission supplied :=
  ⟨value.receivedInput, value.sourceEq, value.packetEq, value.delivery.on_step supplied before event⟩

theorem deliver_on_step (value : Current base profile report current) (valid : input.passive.Valid)
    (target : PassiveTarget profile.entry input.passive)
    (item : J.PacketItem input) (index : Nat) (served : Served input)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (source : J.Source input) (production : served.ticket.value.produced = source.produced)
    (payload : item.value.payload = .link index served emission emitted)
    (pending : item ∈ report.final.custody.pending) (actual : Step input)
    (before : actual.before = report.final) (event : actual.event = .deliver index emission.bytes true) :
    Nonempty (Delivered report current source index served emission actual) := by
  obtain ⟨enabled, ⟨delivery⟩⟩ := deliver value valid target item index served emission emitted source production payload pending
  exact ⟨delivery.on_step actual before event⟩

end Netlib.Check.CampusTCPRecoveryStartupLinkDelivery
