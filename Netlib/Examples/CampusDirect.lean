import Netlib.Examples.CampusDuplex

/-!
# Direct wired interpretation of the campus graph

Abstract access-point vertices collapse to the client role.
No native access point or wireless link is inferred.
-/

namespace Netlib.Examples.CampusDirect
open Network Protocol
open StatefulFailover (Gateway)

inductive Node
  | client | primary | standby | server | management
  deriving Repr, BEq, DecidableEq

def clients : Node → Prop := (· = .client)
def servers : Node → Prop := (· = .server)
def managers : Node → Prop := (· = .management)
def endpoints (node : Node) : Prop := clients node ∨ servers node
def gateways (node : Node) : Prop := node = .primary ∨ node = .standby

def physical : Network Node where
  link a b := (endpoints a ∧ gateways b) ∨ (gateways a ∧ endpoints b)

def gatewayNode : Gateway → Node
  | .primary => .primary
  | .standby => .standby

def collapse : Campus.Node → Node
  | .client | .apA | .apB => .client
  | .gatewayA => .primary
  | .gatewayB => .standby
  | .server => .server
  | .management => .management

def expand : Node → Campus.Node
  | .client => .client
  | .primary => .gatewayA
  | .standby => .gatewayB
  | .server => .server
  | .management => .management

theorem collapse_expand (node : Node) : collapse (expand node) = node := by cases node <;> rfl

def collapse_refinement : StutteringRefinement CampusDuplex.physical physical where
  project := collapse
  simulate a b edge := by
    cases a <;> cases b <;>
      simp_all [CampusDuplex.physical, CampusNAT.physical, Network.union, Campus.base, Campus.access,
        Campus.distribution, collapse, physical, endpoints, clients, servers, gateways]

private theorem client_gateway (gateway : Gateway) :
    CampusDuplex.physical.Reachable .client (CampusDuplex.gatewayNode gateway) := by
  exact .step (next := CampusDuplex.accessPoint gateway)
    (by cases gateway <;> simp [CampusDuplex.physical, CampusNAT.physical, Network.union, Campus.base,
      Campus.access, Campus.distribution, CampusDuplex.accessPoint])
    (.single (by cases gateway <;> simp [CampusDuplex.physical, CampusNAT.physical, Network.union, Campus.base,
      Campus.access, Campus.distribution, CampusDuplex.accessPoint, CampusDuplex.gatewayNode]))

private theorem gateway_client (gateway : Gateway) :
    CampusDuplex.physical.Reachable (CampusDuplex.gatewayNode gateway) .client := by
  exact .step (next := CampusDuplex.accessPoint gateway)
    (by cases gateway <;> simp [CampusDuplex.physical, CampusNAT.physical, Network.union, Campus.base,
      Campus.access, Campus.distribution, CampusDuplex.accessPoint, CampusDuplex.gatewayNode])
    (.single (by cases gateway <;> simp [CampusDuplex.physical, CampusNAT.physical, Network.union, Campus.base,
      Campus.access, Campus.distribution, CampusDuplex.accessPoint]))

def expansion : Refinement physical CampusDuplex.physical where
  project := expand
  simulate a b edge := by
    cases a <;> cases b <;> simp [physical, endpoints, clients, servers, gateways] at edge
    all_goals first
      | exact client_gateway .primary
      | exact client_gateway .standby
      | exact gateway_client .primary
      | exact gateway_client .standby
      | exact .single (by simp [expand, CampusDuplex.physical, CampusNAT.physical, Network.union, Campus.base, Campus.access, Campus.distribution])

def primaryWithdrawal : Fault Node := .node .primary

def physicalAt (withdrawn : Bool) : Network Node :=
  physical.afterFault (if withdrawn then primaryWithdrawal else Fault.none)

private theorem collapse_primary (node : Campus.Node) : collapse node = .primary ↔ node = .gatewayA := by
  cases node <;> simp [collapse]

private theorem collapse_gateways (node : Campus.Node) : gateways (collapse node) ↔ Campus.gateways node := by
  cases node <;> simp [collapse, gateways, Campus.gateways]

def fault_refinement (withdrawn : Bool) :
    StutteringRefinement
      (CampusDuplex.physical.afterFault (if withdrawn then CampusDuplex.primaryWithdrawal else Fault.none)) (physicalAt withdrawn) where
  project := collapse
  simulate a b edge := by
    rcases collapse_refinement.simulate a b edge.1 with same | step
    · exact .inl same
    · right
      refine ⟨step, ?_⟩
      cases withdrawn
      · simp [Fault.none]
      · have liveA := edge.2.1
        have liveB := edge.2.2.1
        change ¬a = .gatewayA at liveA
        change ¬b = .gatewayA at liveB
        simp [primaryWithdrawal, Fault.node, collapse_primary, liveA, liveB]

def network (context : Context) (session : EAPSession.State) (scope : Scope) (withdrawn : Bool) : Network Node :=
  ZeroTrust.enforce (physicalAt withdrawn) gateways (Session.policy context session.session) (CampusDuplex.request context scope)

def network_refinement (context : Context) (session : EAPSession.State) (scope : Scope) (withdrawn : Bool) :
    StutteringRefinement
      (CampusDuplex.network context session scope (if withdrawn then CampusDuplex.primaryWithdrawal else Fault.none))
      (network context session scope withdrawn) where
  project := collapse
  simulate a b edge := by
    rcases (fault_refinement withdrawn).simulate a b edge.1 with same | step
    · exact .inl same
    · exact .inr ⟨step, fun incident => edge.2 (by simpa only [collapse_gateways] using incident)⟩

def Duplex (net : Network Node) : Prop := net.Reachable .client .server ∧ net.Reachable .server .client

theorem permitted_duplex (context : Context) (session : EAPSession.State) (scope : Scope) (withdrawn : Bool)
    (permitted : session.session.permits context scope = true) : Duplex (network context session scope withdrawn) := by
  have available : CampusDuplex.Duplex
      (CampusDuplex.network context session scope (if withdrawn then CampusDuplex.primaryWithdrawal else Fault.none)) := by
    cases withdrawn
    · exact CampusDuplex.permitted_duplex context session scope Fault.none (singleInternalNode_none _ _) permitted
    · exact CampusDuplex.permitted_duplex context session scope CampusDuplex.primaryWithdrawal CampusDuplex.primaryWithdrawal_admissible permitted
  exact ⟨(network_refinement context session scope withdrawn).toRefinement.reachable available.1,
    (network_refinement context session scope withdrawn).toRefinement.reachable available.2⟩

theorem physical_management_isolated : physical.Isolated endpoints managers := by
  apply Network.isolated_of_closed (· ≠ .management)
  · intro a b edge _
    cases a <;> cases b <;> simp_all [physical, endpoints, clients, servers, gateways]
  · intro a member
    cases a <;> simp_all [endpoints, clients, servers]
  · intro b member
    exact fun outside => outside member

theorem physical_request_mediated : physical.Mediated clients servers gateways := by
  apply Network.mediated_of_cut (· = .client)
  · intro a b edge outsideA outsideB inside
    cases a <;> cases b <;> simp_all [physical, endpoints, clients, servers, gateways]
  · intro a member
    exact member
  · intro b member
    cases b <;> simp_all [servers]

theorem physical_reply_mediated : physical.Mediated servers clients gateways := by
  apply Network.mediated_of_cut (· = .server)
  · intro a b edge outsideA outsideB inside
    cases a <;> cases b <;> simp_all [physical, endpoints, clients, servers, gateways]
  · intro a member
    exact member
  · intro b member
    cases b <;> simp_all [clients]

theorem management_isolated (context : Context) (session : EAPSession.State) (scope : Scope) (withdrawn : Bool) :
    (network context session scope withdrawn).Isolated endpoints managers :=
  isolated_mono physical_management_isolated (fun _ _ edge => edge.1.1)

theorem request_mediated (context : Context) (session : EAPSession.State) (scope : Scope) (withdrawn : Bool) :
    (network context session scope withdrawn).Mediated clients servers gateways :=
  mediated_mono physical_request_mediated (fun _ _ edge => edge.1.1)

theorem reply_mediated (context : Context) (session : EAPSession.State) (scope : Scope) (withdrawn : Bool) :
    (network context session scope withdrawn).Mediated servers clients gateways :=
  mediated_mono physical_reply_mediated (fun _ _ edge => edge.1.1)

theorem denied_isolated (context : Context) (session : EAPSession.State) (scope : Scope) (withdrawn : Bool)
    (denied : session.session.permits context scope = false) :
    (network context session scope withdrawn).Isolated clients servers := by
  have mediated : (physicalAt withdrawn).Mediated clients servers gateways :=
    mediated_mono physical_request_mediated (fun _ _ edge => edge.1)
  apply ZeroTrust.denied_isolated mediated
  · intro node member
    cases node <;> simp_all [clients, gateways]
  · intro node member
    cases node <;> simp_all [servers, gateways]
  · simpa only [CampusDuplex.request, Session.policy_allows] using denied

theorem duplex_reachable_iff (context : Context) (session : EAPSession.State) (scope : Scope) (withdrawn : Bool) :
    Duplex (network context session scope withdrawn) ↔ session.session.permits context scope = true := by
  constructor
  · intro available
    cases permitted : session.session.permits context scope with
    | false => exact False.elim (denied_isolated context session scope withdrawn permitted _ _ rfl rfl available.1)
    | true => rfl
  · exact permitted_duplex context session scope withdrawn

def source : FlowNAT.Direction → Node
  | .original => .client
  | .reply => .server

def target : FlowNAT.Direction → Node
  | .original => .server
  | .reply => .client

def routeTrace (gateway : Gateway) : FlowNAT.Direction → List Node
  | .original => [.client, gatewayNode gateway, .server]
  | .reply => [.server, gatewayNode gateway, .client]

theorem standby_after_withdrawal (context : Context) (session : EAPSession.State) (scope : Scope)
    (direction : FlowNAT.Direction) (permitted : session.session.permits context scope = true) :
    Walk (network context session scope true) (source direction) (target direction) (routeTrace .standby direction) := by
  have allowed : (Session.policy context session.session).allows (CampusDuplex.request context scope) = true := by
    simpa only [CampusDuplex.request, Session.policy_allows] using permitted
  rw [network, ZeroTrust.allowed_network_eq _ _ _ _ allowed]
  cases direction <;>
    exact .cons (next := Node.standby)
      (by simp [source, physicalAt, physical, endpoints, clients, servers, gateways, primaryWithdrawal, afterFault, Network.restrict, Fault.node])
      (.cons (by simp [target, physicalAt, physical, endpoints, clients, servers, gateways, primaryWithdrawal, afterFault, Network.restrict, Fault.node]) (.nil _))


theorem selected_route (context : Context) (session : EAPSession.State) (scope : Scope) (withdrawn : Bool)
    (gateway : Gateway) (direction : FlowNAT.Direction) (permitted : session.session.permits context scope = true)
    (live : withdrawn = false ∨ gateway = .standby) :
    Walk (network context session scope withdrawn) (source direction) (target direction) (routeTrace gateway direction) := by
  have allowed : (Session.policy context session.session).allows (CampusDuplex.request context scope) = true := by
    simpa only [CampusDuplex.request, Session.policy_allows] using permitted
  rw [network, ZeroTrust.allowed_network_eq _ _ _ _ allowed]
  cases direction with
  | original =>
    change Walk (physicalAt withdrawn) .client .server [.client, gatewayNode gateway, .server]
    exact .cons (next := gatewayNode gateway)
      (by cases withdrawn <;> cases gateway <;>
        simp_all [physicalAt, physical, endpoints, clients, servers, gateways, gatewayNode, primaryWithdrawal, afterFault, Network.restrict, Fault.node, Fault.none])
      (.cons (by cases withdrawn <;> cases gateway <;>
        simp_all [physicalAt, physical, endpoints, clients, servers, gateways, gatewayNode, primaryWithdrawal, afterFault, Network.restrict, Fault.node, Fault.none]) (.nil _))
  | reply =>
    change Walk (physicalAt withdrawn) .server .client [.server, gatewayNode gateway, .client]
    exact .cons (next := gatewayNode gateway)
      (by cases withdrawn <;> cases gateway <;>
        simp_all [physicalAt, physical, endpoints, clients, servers, gateways, gatewayNode, primaryWithdrawal, afterFault, Network.restrict, Fault.node, Fault.none])
      (.cons (by cases withdrawn <;> cases gateway <;>
        simp_all [physicalAt, physical, endpoints, clients, servers, gateways, gatewayNode, primaryWithdrawal, afterFault, Network.restrict, Fault.node, Fault.none]) (.nil _))

theorem withdrawn_pending_path (context : Context) (session : EAPSession.State) (scope : Scope)
    (state : CampusWithdrawal.State) (safe : state.Safe) (withdrawn : state.withdrawn = true)
    (item : Theory.Outstanding.Item SafeHandoff.Ticket) (member : item ∈ state.handoff.work.pending)
    (permitted : session.session.permits context scope = true) :
    item.value.gateway = .standby ∧ Walk (network context session scope state.withdrawn)
      (source item.value.direction) (target item.value.direction) (routeTrace item.value.gateway item.value.direction) := by
  have assigned := state.pending_standby safe withdrawn item member
  exact ⟨assigned, selected_route context session scope state.withdrawn item.value.gateway item.value.direction permitted (.inr assigned)⟩

end Netlib.Examples.CampusDirect
