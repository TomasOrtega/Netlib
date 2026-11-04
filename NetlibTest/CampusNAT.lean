import Netlib.Examples.CampusNAT

namespace NetlibTest.CampusNAT

open Netlib Packet Protocol Netlib.Examples.CampusNAT

private def session : Session := Session.run Examples.Campus.context Session.initial [
  .authenticate true,
  .install {
    issuer := Examples.Campus.context.issuer
    subject := Examples.Campus.context.consumer
    audience := Examples.Campus.context.producer
    scopes := [Examples.Campus.application]
    expiresAt := 100
    integrity := true
  },
  .request Examples.Campus.application]

private theorem permitted : session.permits Examples.Campus.context Examples.Campus.application = true := by decide

private def packet : Header := ⟨167772161, 3325256705, Protocol.tcp, 50000, 443⟩
private def allocation : Endpoint := ⟨3405803777, 62000⟩
private def wire : Header := (Rewrite.sourceEndpoint allocation).apply packet
private def empty : Store := (NAT.State.initial, NAT.State.initial)
private def opened : NAT.State :=
  ((NAT.outboundProcessor allocation 60 applicationACL).run NAT.State.initial packet).1
private def primaryStore : Store := (opened, NAT.State.initial)
private def replicaStore : Store := replicatePrimary primaryStore

private theorem accepted : (NAT.outboundProcessor allocation 60 applicationACL).run NAT.State.initial packet =
    (opened, some wire) := by decide

private theorem primarySafe : StoreSafe primaryStore :=
  ⟨NAT.outboundProcessor_safe allocation 60 applicationACL NAT.State.initial packet NAT.initial_safe,
    NAT.initial_safe⟩

example :
    (network session allocation 60 Network.Fault.none).Reachable
      ⟨.client, packet, empty⟩ ⟨.server, wire, primaryStore⟩ ∧
    (network session allocation 60 Network.Fault.none).Reachable
      ⟨.server, wire.reverse, primaryStore⟩ ⟨.client, packet.reverse, primaryStore⟩ :=
  primary_roundtrip session allocation 60 permitted NAT.State.initial opened NAT.State.initial packet wire accepted

example : StoreSafe replicaStore := replication_safe primaryStore primarySafe.1

example : replicaStore.1.tracking.now = primaryStore.1.tracking.now ∧
    replicaStore.2.tracking.now = primaryStore.2.tracking.now :=
  replication_clock primaryStore (by decide)

example (fault : Network.Fault Node)
    (admissible : Network.singleInternalNode Examples.Campus.clients Examples.Campus.servers fault) :
    (network session allocation 60 fault).Reachable
      ⟨.server, wire.reverse, replicaStore⟩ ⟨.client, packet.reverse, replicaStore⟩ :=
  replicated_return_survives session allocation 60 permitted NAT.State.initial opened packet wire accepted fault admissible

example : (physical.afterFault failedPrimary).Reachable .server .client ∧
    ∀ header store, ¬(network session allocation 60 failedPrimary).Reachable
      ⟨.server, wire.reverse, primaryStore⟩ ⟨.client, header, store⟩ :=
  topology_without_grants_insufficient session allocation 60 opened NAT.State.initial rfl wire.reverse

private def mappingsOnly : NAT.State := ⟨NAT.State.initial.tracking, opened.bindings⟩

example (header : Header) (store : Store) :
    ¬(network session allocation 60 failedPrimary).Reachable
      ⟨.server, wire.reverse, (opened, mappingsOnly)⟩ ⟨.client, header, store⟩ :=
  unreplicated_return_blocked session allocation 60 opened mappingsOnly rfl wire.reverse header store

example (header : Header) (store : Store) (fault : Network.Fault Node) :
    ¬(network Session.initial allocation 60 fault).Reachable
      ⟨.client, packet, empty⟩ ⟨.server, header, store⟩ :=
  denied_isolated Session.initial allocation 60 fault (by decide) _ _ rfl rfl

private def pathProcessor (currentSession : Session) : List Node → Processor Store
  | source :: target :: rest =>
    (programs currentSession allocation 60 source target).seq (pathProcessor currentSession (target :: rest))
  | _ => Processor.identity

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  let outbound := (pathProcessor session [.client, .apA, .gatewayA, .server]).run empty packet
  ensure (outbound.2 == some wire && decide (outbound.1 = primaryStore))
    "The outbound campus path did not thread gateway A's actual NAT state."
  ensure (decide (outbound.1.2 = NAT.State.initial)) "Gateway A's processing changed gateway B's store."
  let primaryReply := (pathProcessor session [.server, .gatewayA, .apA, .client]).run outbound.1 wire.reverse
  ensure (primaryReply.2 == some packet.reverse && decide (primaryReply.1 = outbound.1))
    "The primary return path did not restore the client endpoint from the installed state."
  let lostState := (pathProcessor session [.server, .gatewayB, .apB, .client]).run outbound.1 wire.reverse
  ensure (lostState.2.isNone && decide (lostState.1 = outbound.1))
    "An empty standby gateway forwarded the established reply."
  let mappings := (opened, mappingsOnly)
  let missingGrant := (pathProcessor session [.server, .gatewayB, .apB, .client]).run mappings wire.reverse
  ensure (missingGrant.2.isNone && decide (missingGrant.1 = mappings))
    "Mapping replication without flow grants admitted a reply."
  let copied := replicatePrimary outbound.1
  ensure (copied.1.tracking.now == outbound.1.1.tracking.now &&
    copied.2.tracking.now == outbound.1.2.tracking.now) "The synchronized snapshot changed a gateway clock."
  let recovered := (pathProcessor session [.server, .gatewayB, .apB, .client]).run copied wire.reverse
  ensure (recovered.2 == some packet.reverse && decide (recovered.1 = copied))
    "The exact pre-fault replica failed to restore the reply through gateway B."
  let denied := (pathProcessor Session.initial [.client, .apA, .gatewayA, .server]).run empty packet
  ensure (denied.2.isNone && decide (denied.1 = empty)) "A denied session opened a campus mapping."
  for forbidden in [{ packet with source := 167772162 }, { packet with destinationPort := 22 }] do
    let result := (pathProcessor session [.client, .apA, .gatewayA, .server]).run empty forbidden
    ensure (result.2.isNone && decide (result.1 = empty)) "The application ACL admitted an unrelated flow."
  let expired := (NAT.advance copied.1 60, NAT.advance copied.2 60)
  let late := (pathProcessor session [.server, .gatewayB, .apB, .client]).run expired wire.reverse
  ensure late.2.isNone "The standby snapshot retained an expired reply grant."
  IO.println "Campus stateful failover tests passed."

end NetlibTest.CampusNAT
