import Netlib.Check.CampusTCPFacts
import Netlib.Protocol.TCP.ApplicationTraceFacts

/-!
# Receive storage on the actual campus trace

Held and released bytes retain their actual receipt and gateway source.
An empty final store does not imply eventual packet delivery.
-/

namespace Netlib.Check.CampusTCPGapFacts

open Protocol
namespace M
export Check.CampusTCPModel (Actor Cursor Report)
end M
namespace A
export TCP.ApplicationTrace (Step RunReceiptOrigin ReadReleasedByteOrigin AttemptByteOrigin OutputAt)
end A

structure ReceiptDelivery (report : M.Report input events) (peer : List A.Step) (actor : M.Actor)
    (steps : List A.Step) (run : TCP.ReceiveReassembly.Run) where
  origin : A.RunReceiptOrigin steps run
  delivery : CampusTCPFacts.ApplicationDelivery report peer actor origin.issuer

theorem receipt_delivery (history : CampusTCPFacts.Receives report peer actor steps)
    (origin : A.RunReceiptOrigin steps run) : Nonempty (ReceiptDelivery report peer actor steps run) := by
  obtain ⟨delivery⟩ := history.application_delivery origin.issuer origin.member origin.allocation.input origin.allocation.event
  exact ⟨⟨origin, delivery⟩⟩

structure EndpointEvidence (report : M.Report input events) (peer : List A.Step) (actor : M.Actor)
    (seed : TCP.Endpoint.State) (cursor : M.Cursor seed) where
  empty : seed.receiveStore.held = []
  storage : cursor.current.StorageValid
  history : TCP.ReceiveStoreHistory.History seed.receiveStore
    (TCP.ApplicationTrace.receiveAllocations cursor.steps) cursor.current.receiveStore
  held : ∀ run ∈ cursor.current.receiveStore.held, Nonempty (ReceiptDelivery report peer actor cursor.steps run)

theorem endpointEvidence (report : M.Report input events) (peer : List A.Step) (actor : M.Actor)
    (seed : TCP.Endpoint.State) (cursor : M.Cursor seed) (empty : seed.receiveStore.held = [])
    (receives : CampusTCPFacts.Receives report peer actor cursor.steps) :
    EndpointEvidence report peer actor seed cursor :=
  ⟨empty, cursor.chain.storage_valid (TCP.Endpoint.storage_valid_of_empty seed empty), cursor.chain.receive_history, by
    intro run member
    obtain ⟨origin⟩ := cursor.chain.held_run_origin empty run member
    exact receipt_delivery receives origin⟩

theorem EndpointEvidence.before_storage (value : EndpointEvidence report peer actor seed cursor)
    (step : A.Step) (member : step ∈ cursor.steps) : step.before.StorageValid := by
  obtain ⟨_, _, _, preceding, _⟩ := cursor.chain.split step member
  exact preceding.storage_valid (TCP.Endpoint.storage_valid_of_empty seed value.empty)

theorem EndpointEvidence.after_storage (value : EndpointEvidence report peer actor seed cursor)
    (step : A.Step) (member : step ∈ cursor.steps) : step.result.state.StorageValid :=
  step.storage_valid (value.before_storage step member)

structure Evidence (report : M.Report input events) where
  application : CampusTCPFacts.Assurance report
  client : EndpointEvidence report application.endpoints.server.steps .client
    application.complete.certificate.activeSeed application.endpoints.client
  server : EndpointEvidence report application.endpoints.client.steps .server
    application.complete.certificate.passiveSeed application.endpoints.server

def evidence (report : M.Report input events) : Except String (Evidence report) := do
  let application ← CampusTCPFacts.assure report
  return ⟨application,
    endpointEvidence report _ .client _ application.endpoints.client
      application.complete.certificate.empty_receiveStore.1 application.clientReceives,
    endpointEvidence report _ .server _ application.endpoints.server
      application.complete.certificate.empty_receiveStore.2 application.serverReceives⟩

structure Assurance (report : M.Report input events) extends Evidence report where
  clientClosed : application.endpoints.client.current.receiveStore.held = []
  serverClosed : application.endpoints.server.current.receiveStore.held = []

def assure (value : Evidence report) : Except String (Assurance report) := do
  if clientClosed : value.application.endpoints.client.current.receiveStore.held = [] then
    if serverClosed : value.application.endpoints.server.current.receiveStore.held = [] then
      return ⟨value, clientClosed, serverClosed⟩
    else throw "The server still holds data above a gap."
  else throw "The client still holds data above a gap."

structure ReadOrigin (report : M.Report input events) (peerInitial : TCP.Endpoint.State)
    (peer : List A.Step) (actor : M.Actor) (steps : List A.Step) (reader : A.Step) (index : Nat) (byte : UInt8) where
  read : A.ReadReleasedByteOrigin steps reader index byte
  delivery : CampusTCPFacts.ApplicationDelivery report peer actor read.origin.origin.issuer
  attempt : A.OutputAt peer
  actualSource : attempt = delivery.source
  path : TCP.ApplicationTrace.BytePath attempt.output read.origin.origin.allocation.input
  earlier : attempt.step.stamp < read.origin.origin.issuer.stamp
  receiptBeforeRelease : read.origin.origin.issuer.stamp ≤ read.release.stamp
  provenance : Nonempty (A.AttemptByteOrigin peerInitial peer attempt read.origin.localIndex byte)

theorem read_origin (chain : TCP.ApplicationTrace.Chain seed steps final)
    (peerChain : TCP.ApplicationTrace.Chain peerInitial peer peerFinal)
    (history : TCP.ApplicationTrace.DeliveryHistory peer steps)
    (receives : CampusTCPFacts.Receives report peer actor steps)
    (emptyUnread : seed.core.received = []) (emptyHeld : seed.receiveStore.held = [])
    (emptySent : peerInitial.core.sent = []) (emptyPending : peerInitial.pending = [])
    (reader : A.Step) (member : reader ∈ steps) (count : Nat) (event : reader.event = .read count)
    (index : Nat) (byte : UInt8) (selected : reader.readBytes[index]? = some byte) :
    Nonempty (ReadOrigin report peerInitial peer actor steps reader index byte) := by
  obtain ⟨read⟩ := TCP.ApplicationTrace.read_byte_origin chain emptyUnread emptyHeld history.receiverOrder
    reader member count event index byte selected
  obtain ⟨delivery⟩ := receives.application_delivery read.origin.origin.issuer read.origin.origin.issuer_member
    read.origin.origin.allocation.input read.origin.origin.allocation.event
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

theorem Evidence.client_read_origin (value : Evidence report)
    (reader : A.Step) (member : reader ∈ value.application.endpoints.client.steps)
    (count : Nat) (event : reader.event = .read count)
    (index : Nat) (byte : UInt8) (selected : reader.readBytes[index]? = some byte) :
    Nonempty (ReadOrigin report value.application.complete.certificate.passiveSeed
      value.application.endpoints.server.steps .client value.application.endpoints.client.steps reader index byte) := by
  have empty := value.application.complete.certificate.empty
  exact read_origin value.application.endpoints.client.chain value.application.endpoints.server.chain
    value.application.backward value.application.clientReceives empty.2.2.1 value.client.empty
    empty.2.2.2.2.1 empty.2.2.2.1 reader member count event index byte selected

theorem Evidence.server_read_origin (value : Evidence report)
    (reader : A.Step) (member : reader ∈ value.application.endpoints.server.steps)
    (count : Nat) (event : reader.event = .read count)
    (index : Nat) (byte : UInt8) (selected : reader.readBytes[index]? = some byte) :
    Nonempty (ReadOrigin report value.application.complete.certificate.activeSeed
      value.application.endpoints.client.steps .server value.application.endpoints.server.steps reader index byte) := by
  have empty := value.application.complete.certificate.empty
  exact read_origin value.application.endpoints.server.chain value.application.endpoints.client.chain
    value.application.forward value.application.serverReceives empty.2.2.2.2.2 value.server.empty
    empty.2.1 empty.1 reader member count event index byte selected

theorem Evidence.application_prefix (value : Evidence report) :
    value.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes <+:
        value.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.written ∧
      value.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes <+:
        value.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.written :=
  value.application.application_prefix

end Netlib.Check.CampusTCPGapFacts
