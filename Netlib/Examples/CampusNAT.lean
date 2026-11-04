import Netlib.Examples.Campus
import Netlib.Packet.Stateful
import Netlib.Protocol.NATPipeline

/-!
# Campus source-NAPT failover

Each gateway has its own mapping and flow-grant store.
The duplex topology extends the existing campus graph with reverse links.
Session checks and exact state replication are explicit model assumptions.
-/

namespace Netlib.Examples.CampusNAT

open Packet Protocol

abbrev Node := Campus.Node
abbrev Store := NAT.State × NAT.State
abbrev Vertex := Stateful.Vertex Node Store

def physical : Network Node :=
  Network.union Campus.base ⟨fun source target => Campus.base.link target source⟩

theorem physical_management_isolated : physical.Isolated Campus.clients Campus.managers := by
  apply Network.isolated_of_closed (· ≠ .management)
  · intro source target edge _
    cases source <;> cases target <;>
      simp_all [physical, Network.union, Campus.base, Campus.access, Campus.distribution]
  · intro source member
    cases source <;> simp_all [Campus.clients]
  · intro target member
    cases target <;> simp_all [Campus.managers]

theorem physical_gateway_mediated : physical.Mediated Campus.clients Campus.servers Campus.gateways := by
  apply Network.mediated_of_cut (fun node => node = .client ∨ node = .apA ∨ node = .apB)
  · intro source target edge sourceOutside targetOutside inside
    cases source <;> cases target <;>
      simp_all [physical, Network.union, Campus.base, Campus.access, Campus.distribution, Campus.gateways]
  · intro source member
    cases source <;> simp_all [Campus.clients]
  · intro target member
    cases target <;> simp_all [Campus.servers]

theorem physical_failure_available (fault : Network.Fault Node)
    (admissible : Network.singleInternalNode Campus.clients Campus.servers fault) :
    (physical.afterFault fault).Available Campus.clients Campus.servers :=
  Network.available_mono (Campus.service_survives_one_internal_failure fault admissible)
    (fun _ _ edge => ⟨.inl edge.1, edge.2⟩)

def failedPrimary : Network.Fault Node := Network.Fault.node .gatewayA

theorem alternate_return_topology : (physical.afterFault failedPrimary).Reachable .server .client := by
  apply Network.Reachable.step (next := Campus.Node.gatewayB)
  · simp [physical, Network.union, Campus.base, Campus.access, Campus.distribution,
      Network.afterFault, Network.restrict, failedPrimary, Network.Fault.node]
  apply Network.Reachable.step (next := Campus.Node.apB)
  · simp [physical, Network.union, Campus.base, Campus.access, Campus.distribution,
      Network.afterFault, Network.restrict, failedPrimary, Network.Fault.node]
  apply Network.Reachable.single
  simp [physical, Network.union, Campus.base, Campus.access, Campus.distribution,
    Network.afterFault, Network.restrict, failedPrimary, Network.Fault.node]

def applicationMatch : Match := {
  source := some ⟨167772161, 32⟩
  destination := some ⟨3325256705, 32⟩
  protocol := some Protocol.tcp
  destinationPorts := some (PortRange.single 443)
}

def applicationACL : ACL := [⟨applicationMatch, .permit⟩]

def sessionGate (session : Session) : Processor NAT.State :=
  Processor.guard (fun _ => session.permits Campus.context Campus.application)

def outbound (session : Session) (allocation : Endpoint) (deadline : Nat) : Processor NAT.State :=
  (sessionGate session).seq (NAT.outboundProcessor allocation deadline applicationACL)

def inbound (session : Session) : Processor NAT.State :=
  (sessionGate session).seq NAT.inboundProcessor

def programs (session : Session) (allocation : Endpoint) (deadline : Nat) : Node → Node → Processor Store
  | .gatewayA, .server => (outbound session allocation deadline).liftLeft
  | .gatewayB, .server => (outbound session allocation deadline).liftRight
  | .server, .gatewayA => (inbound session).liftLeft
  | .server, .gatewayB => (inbound session).liftRight
  | _, _ => Processor.identity

def network (session : Session) (allocation : Endpoint) (deadline : Nat) (fault : Network.Fault Node) :
    Network Vertex := Stateful.network (physical.afterFault fault) (programs session allocation deadline)

def StoreSafe (store : Store) : Prop := store.1.Safe ∧ store.2.Safe

theorem programs_preserve (session : Session) (allocation : Endpoint) (deadline : Nat) (source target : Node) :
    (programs session allocation deadline source target).Preserves StoreSafe := by
  have outboundSafe : (outbound session allocation deadline).Preserves NAT.State.Safe :=
    (Processor.guard_preserves _ _).seq (NAT.outboundProcessor_safe allocation deadline applicationACL)
  have inboundSafe : (inbound session).Preserves NAT.State.Safe :=
    (Processor.guard_preserves _ _).seq NAT.inboundProcessor_safe
  cases source <;> cases target <;> simp only [programs]
  all_goals first
    | exact Processor.identity_preserves StoreSafe
    | exact outboundSafe.liftLeft NAT.State.Safe
    | exact outboundSafe.liftRight NAT.State.Safe
    | exact inboundSafe.liftLeft NAT.State.Safe
    | exact inboundSafe.liftRight NAT.State.Safe

theorem stores_safe (session : Session) (allocation : Endpoint) (deadline : Nat) (fault : Network.Fault Node)
    {before after : Vertex} (path : (network session allocation deadline fault).Reachable before after)
    (initial : StoreSafe before.store) : StoreSafe after.store :=
  Stateful.invariant _ _ StoreSafe (programs_preserve session allocation deadline) path initial

theorem management_isolated (session : Session) (allocation : Endpoint) (deadline : Nat)
    (fault : Network.Fault Node) :
    (network session allocation deadline fault).Isolated
      (fun vertex => Campus.clients vertex.node) (fun vertex => Campus.managers vertex.node) :=
  Stateful.isolated_of_physical _ _
    (Network.isolated_mono physical_management_isolated (fun _ _ edge => edge.1))

theorem gateway_mediated (session : Session) (allocation : Endpoint) (deadline : Nat)
    (fault : Network.Fault Node) :
    (network session allocation deadline fault).Mediated
      (fun vertex => Campus.clients vertex.node) (fun vertex => Campus.servers vertex.node)
      (fun vertex => Campus.gateways vertex.node) :=
  Stateful.mediated_of_physical _ _
    (Network.mediated_mono physical_gateway_mediated (fun _ _ edge => edge.1))

theorem outbound_run (session : Session) (allocation : Endpoint) (deadline : Nat)
    (permitted : session.permits Campus.context Campus.application = true)
    (state : NAT.State) (packet : Header) :
    (outbound session allocation deadline).run state packet =
      (NAT.outboundProcessor allocation deadline applicationACL).run state packet := by
  simp [outbound, sessionGate, Processor.seq, Processor.guard, Processor.stateless, permitted]

theorem inbound_run (session : Session)
    (permitted : session.permits Campus.context Campus.application = true)
    (state : NAT.State) (packet : Header) :
    (inbound session).run state packet = NAT.inboundProcessor.run state packet := by
  simp [inbound, sessionGate, Processor.seq, Processor.guard, Processor.stateless, permitted]

theorem denied_isolated (session : Session) (allocation : Endpoint) (deadline : Nat)
    (fault : Network.Fault Node)
    (denied : session.permits Campus.context Campus.application = false) :
    (network session allocation deadline fault).Isolated
      (fun vertex => Campus.clients vertex.node) (fun vertex => Campus.servers vertex.node) := by
  apply Network.isolated_of_closed (fun vertex => vertex.node ≠ .server)
  · intro before after edge _ server
    rcases before with ⟨source, packet, store⟩
    rcases after with ⟨target, output, next⟩
    change target = .server at server
    subst target
    have adjacency := edge.1.1
    have processed := edge.2
    cases source <;>
      simp_all [physical, Network.union, Campus.base, Campus.access, Campus.distribution,
        programs, outbound, sessionGate, Processor.seq, Processor.guard, Processor.stateless,
        Processor.liftLeft, Processor.liftRight]
  · intro vertex source
    intro server
    have same : Campus.Node.client = .server := (show vertex.node = .client from source).symm.trans server
    cases same
  · intro vertex server outside
    exact outside server

/-- The inactive gateway's store is carried unchanged through the outbound path. -/
theorem primary_forward (session : Session) (allocation : Endpoint) (deadline : Nat)
    (permitted : session.permits Campus.context Campus.application = true)
    (before after standby : NAT.State) (packet wire : Header)
    (accepted : (NAT.outboundProcessor allocation deadline applicationACL).run before packet =
      (after, some wire)) :
    (network session allocation deadline Network.Fault.none).Reachable
      ⟨.client, packet, (before, standby)⟩ ⟨.server, wire, (after, standby)⟩ := by
  apply Network.Reachable.step (next := (⟨.apA, packet, (before, standby)⟩ : Vertex))
  · constructor
    · simp [physical, Network.union, Campus.base, Campus.access, Campus.distribution,
        Network.afterFault, Network.restrict, Network.Fault.none]
    · rfl
  apply Network.Reachable.step (next := (⟨.gatewayA, packet, (before, standby)⟩ : Vertex))
  · constructor
    · simp [physical, Network.union, Campus.base, Campus.access, Campus.distribution,
        Network.afterFault, Network.restrict, Network.Fault.none]
    · rfl
  apply Network.Reachable.single
  constructor
  · simp [physical, Network.union, Campus.base, Campus.access, Campus.distribution,
      Network.afterFault, Network.restrict, Network.Fault.none]
  · change (outbound session allocation deadline).liftLeft.run (before, standby) packet = _
    simp [Processor.liftLeft, outbound_run session allocation deadline permitted, accepted]

theorem primary_return (session : Session) (allocation : Endpoint) (deadline : Nat)
    (permitted : session.permits Campus.context Campus.application = true)
    (before after standby : NAT.State) (packet wire : Header)
    (accepted : (NAT.outboundProcessor allocation deadline applicationACL).run before packet =
      (after, some wire)) :
    (network session allocation deadline Network.Fault.none).Reachable
      ⟨.server, wire.reverse, (after, standby)⟩ ⟨.client, packet.reverse, (after, standby)⟩ := by
  have restored := NAT.processor_roundtrip before after packet wire allocation deadline applicationACL accepted
  apply Network.Reachable.step (next := (⟨.gatewayA, packet.reverse, (after, standby)⟩ : Vertex))
  · constructor
    · simp [physical, Network.union, Campus.base, Campus.access, Campus.distribution,
        Network.afterFault, Network.restrict, Network.Fault.none]
    · change (inbound session).liftLeft.run (after, standby) wire.reverse = _
      simp [Processor.liftLeft, inbound_run session permitted, restored]
  apply Network.Reachable.step (next := (⟨.apA, packet.reverse, (after, standby)⟩ : Vertex))
  · constructor
    · simp [physical, Network.union, Campus.base, Campus.access, Campus.distribution,
        Network.afterFault, Network.restrict, Network.Fault.none]
    · rfl
  apply Network.Reachable.single
  constructor
  · simp [physical, Network.union, Campus.base, Campus.access, Campus.distribution,
      Network.afterFault, Network.restrict, Network.Fault.none]
  · rfl

theorem primary_roundtrip (session : Session) (allocation : Endpoint) (deadline : Nat)
    (permitted : session.permits Campus.context Campus.application = true)
    (before after standby : NAT.State) (packet wire : Header)
    (accepted : (NAT.outboundProcessor allocation deadline applicationACL).run before packet =
      (after, some wire)) :
    (network session allocation deadline Network.Fault.none).Reachable
      ⟨.client, packet, (before, standby)⟩ ⟨.server, wire, (after, standby)⟩ ∧
    (network session allocation deadline Network.Fault.none).Reachable
      ⟨.server, wire.reverse, (after, standby)⟩ ⟨.client, packet.reverse, (after, standby)⟩ :=
  ⟨primary_forward _ _ _ permitted _ _ _ _ _ accepted,
    primary_return _ _ _ permitted _ _ _ _ _ accepted⟩

private def gateway (primary : Bool) : Node := if primary then .gatewayA else .gatewayB
private def accessPoint (primary : Bool) : Node := if primary then .apA else .apB

private theorem return_via (primary : Bool) (session : Session) (allocation : Endpoint) (deadline : Nat)
    (fault : Network.Fault Node)
    (permitted : session.permits Campus.context Campus.application = true)
    (state : NAT.State) (packet wire : Header)
    (restored : NAT.inboundProcessor.run state wire.reverse = (state, some packet.reverse))
    (alive : ∀ node ∈ [.server, gateway primary, accessPoint primary, .client], ¬fault.nodes node)
    (linksAlive : ∀ source target, ¬fault.links source target) :
    (network session allocation deadline fault).Reachable
      ⟨.server, wire.reverse, (state, state)⟩ ⟨.client, packet.reverse, (state, state)⟩ := by
  apply Network.Reachable.step (next := (⟨gateway primary, packet.reverse, (state, state)⟩ : Vertex))
  · constructor
    · refine ⟨?_, alive _ (by simp), alive _ (by simp), linksAlive _ _⟩
      cases primary <;> simp [physical, Network.union, Campus.base, Campus.access, Campus.distribution, gateway]
    · cases primary <;>
        simp [programs, gateway, Processor.liftLeft, Processor.liftRight,
          inbound_run session permitted, restored]
  apply Network.Reachable.step (next := (⟨accessPoint primary, packet.reverse, (state, state)⟩ : Vertex))
  · constructor
    · refine ⟨?_, alive _ (by simp), alive _ (by simp), linksAlive _ _⟩
      cases primary <;> simp [physical, Network.union, Campus.base, Campus.access, Campus.distribution, gateway, accessPoint]
    · cases primary <;> rfl
  apply Network.Reachable.single
  constructor
  · refine ⟨?_, alive _ (by simp), alive _ (by simp), linksAlive _ _⟩
    cases primary <;> simp [physical, Network.union, Campus.base, Campus.access, Campus.distribution, accessPoint]
  · cases primary <;> rfl

def replicatePrimary (store : Store) : Store := (store.1, store.1)

theorem replication_safe (store : Store) (primarySafe : store.1.Safe) :
    StoreSafe (replicatePrimary store) := ⟨primarySafe, primarySafe⟩

theorem replication_clock (store : Store) (synchronized : store.1.tracking.now = store.2.tracking.now) :
    (replicatePrimary store).1.tracking.now = store.1.tracking.now ∧
      (replicatePrimary store).2.tracking.now = store.2.tracking.now := ⟨rfl, synchronized⟩

/-- The exact replica must already exist before the fault; no replication protocol is modeled. -/
theorem replicated_return_survives (session : Session) (allocation : Endpoint) (deadline : Nat)
    (permitted : session.permits Campus.context Campus.application = true)
    (before after : NAT.State) (packet wire : Header)
    (accepted : (NAT.outboundProcessor allocation deadline applicationACL).run before packet = (after, some wire))
    (fault : Network.Fault Node)
    (admissible : Network.singleInternalNode Campus.clients Campus.servers fault) :
    (network session allocation deadline fault).Reachable
      ⟨.server, wire.reverse, (after, after)⟩ ⟨.client, packet.reverse, (after, after)⟩ := by
  have restored := NAT.processor_roundtrip before after packet wire allocation deadline applicationACL accepted
  obtain ⟨oneNode, clientAlive, serverAlive, linksAlive⟩ := admissible
  have sourceAlive := clientAlive .client rfl
  have targetAlive := serverAlive .server rfl
  by_cases primaryAlive : ∀ node ∈ [.server, gateway true, accessPoint true, .client], ¬fault.nodes node
  · exact return_via true session allocation deadline fault permitted after packet wire restored primaryAlive linksAlive
  · apply return_via false session allocation deadline fault permitted after packet wire restored ?_ linksAlive
    intro node member failed
    apply primaryAlive
    intro other otherMember otherFailed
    have same := oneNode other node otherFailed failed
    subst node
    have endpoint : other = .server ∨ other = .client := by
      cases other <;> simp_all [gateway, accessPoint]
    rcases endpoint with endpoint | endpoint
    · exact targetAlive (endpoint ▸ otherFailed)
    · exact sourceAlive (endpoint ▸ otherFailed)

theorem inbound_without_grants (state : NAT.State) (empty : state.tracking.entries = []) (packet : Header) :
    NAT.inboundProcessor.run state packet = (state, none) := by
  have denied : NAT.inbound state packet = none := by
    cases accepted : NAT.inbound state packet with
    | none => rfl
    | some restored =>
      obtain ⟨_, _, _, _, _, entry, member, _, _⟩ := NAT.inbound_sound state packet restored accepted
      rw [empty] at member
      cases member
  exact Prod.ext rfl denied

/-- Missing grants on the surviving gateway block every possible client output state. -/
theorem unreplicated_return_blocked (session : Session) (allocation : Endpoint) (deadline : Nat)
    (primary secondary : NAT.State) (empty : secondary.tracking.entries = []) (reply : Header)
    (header : Header) (store : Store) :
    ¬(network session allocation deadline failedPrimary).Reachable
      ⟨.server, reply, (primary, secondary)⟩ ⟨.client, header, store⟩ := by
  have noStep : ∀ after : Vertex,
      ¬(network session allocation deadline failedPrimary).link ⟨.server, reply, (primary, secondary)⟩ after := by
    intro after edge
    rcases after with ⟨target, output, next⟩
    have adjacency := edge.1
    have processed := edge.2
    have denied := inbound_without_grants secondary empty reply
    cases permitted : session.permits Campus.context Campus.application <;> cases target <;>
      simp_all [physical, Network.union, Campus.base, Campus.access, Campus.distribution,
        Network.afterFault, Network.restrict, failedPrimary, Network.Fault.node,
        programs, inbound, sessionGate, Processor.seq, Processor.guard, Processor.stateless,
        Processor.liftRight]
  intro path
  cases path with
  | step edge _ => exact noStep _ edge

theorem topology_without_grants_insufficient (session : Session) (allocation : Endpoint) (deadline : Nat)
    (primary secondary : NAT.State) (empty : secondary.tracking.entries = []) (reply : Header) :
    (physical.afterFault failedPrimary).Reachable .server .client ∧
      ∀ header store, ¬(network session allocation deadline failedPrimary).Reachable
        ⟨.server, reply, (primary, secondary)⟩ ⟨.client, header, store⟩ :=
  ⟨alternate_return_topology, fun header store =>
    unreplicated_return_blocked session allocation deadline primary secondary empty reply header store⟩

end Netlib.Examples.CampusNAT
