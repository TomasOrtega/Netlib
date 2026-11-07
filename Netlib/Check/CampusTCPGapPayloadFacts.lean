import Netlib.Check.CampusTCPGapFacts
import Netlib.Check.CampusTCPReceiveHistory

/-!
# Payload origins in the actual campus history

Allocated bytes retain the exact application source and writer.
Empty startup ACKs need no peer application output.
-/

namespace Netlib.Check.CampusTCPGapFacts

open Protocol

theorem payload_delivery_history (receives : CampusTCPReceiveHistory.PayloadReceives report peer actor steps)
    (peerOrder : TCP.ApplicationTrace.Chronological peer) (receiverOrder : TCP.ApplicationTrace.Chronological steps) :
    TCP.ApplicationTrace.PayloadDeliveryHistory peer steps := by
  refine ⟨peerOrder, receiverOrder, ?_⟩
  intro operation member nonempty packet event
  obtain ⟨delivery⟩ := receives operation member nonempty
  have same := TCP.ApplicationTrace.Event.receive.inj (delivery.receive.event.symm.trans event)
  exact ⟨delivery.source, delivery.earlier, by simpa only [same] using delivery.path⟩

theorem payload_receipt_delivery (history : CampusTCPReceiveHistory.PayloadReceives report peer actor steps)
    (origin : A.RunReceiptOrigin steps run) : Nonempty (ReceiptDelivery report peer actor steps run) := by
  obtain ⟨delivery⟩ := history origin.issuer origin.member origin.allocation.accepted_payload_nonempty
  exact ⟨⟨origin, delivery⟩⟩

theorem payload_endpointEvidence (report : M.Report input events) (peer : List A.Step) (actor : M.Actor)
    (seed : TCP.Endpoint.State) (cursor : M.Cursor seed) (empty : seed.receiveStore.held = [])
    (receives : CampusTCPReceiveHistory.PayloadReceives report peer actor cursor.steps) :
    EndpointEvidence report peer actor seed cursor :=
  ⟨empty, cursor.chain.storage_valid (TCP.Endpoint.storage_valid_of_empty seed empty), cursor.chain.receive_history, by
    intro run member
    obtain ⟨origin⟩ := cursor.chain.held_run_origin empty run member
    exact payload_receipt_delivery receives origin⟩

theorem payload_read_origin (chain : TCP.ApplicationTrace.Chain seed steps final)
    (peerChain : TCP.ApplicationTrace.Chain peerInitial peer peerFinal)
    (history : TCP.ApplicationTrace.PayloadDeliveryHistory peer steps)
    (receives : CampusTCPReceiveHistory.PayloadReceives report peer actor steps)
    (emptyUnread : seed.core.received = []) (emptyHeld : seed.receiveStore.held = [])
    (emptySent : peerInitial.core.sent = []) (emptyPending : peerInitial.pending = [])
    (reader : A.Step) (member : reader ∈ steps) (count : Nat) (event : reader.event = .read count)
    (index : Nat) (byte : UInt8) (selected : reader.readBytes[index]? = some byte) :
    Nonempty (ReadOrigin report peerInitial peer actor steps reader index byte) := by
  obtain ⟨read⟩ := TCP.ApplicationTrace.read_byte_origin chain emptyUnread emptyHeld history.receiverOrder
    reader member count event index byte selected
  obtain ⟨delivery⟩ := receives read.origin.origin.issuer read.origin.origin.issuer_member
    read.origin.origin.allocation.accepted_payload_nonempty
  have same : delivery.receive.received = read.origin.origin.allocation.input :=
    TCP.ApplicationTrace.Event.receive.inj (delivery.receive.event.symm.trans read.origin.origin.allocation.event)
  have path : TCP.ApplicationTrace.BytePath delivery.source.output read.origin.origin.allocation.input := by
    rw [← same]
    exact delivery.path
  have sourceByte : delivery.source.output.packet.segment.payload[read.origin.localIndex]? = some byte := by
    rw [← path.fields.1]
    exact read.origin.input_byte
  exact ⟨⟨read, delivery, delivery.source, rfl, path, delivery.earlier,
    read.origin.origin.no_later history.receiverOrder,
    delivery.source.byte_origin peerChain emptySent emptyPending history.senderOrder read.origin.localIndex byte sourceByte⟩⟩

end Netlib.Check.CampusTCPGapFacts
