import Netlib.Examples.CampusNAT
import Netlib.Examples.EAPDeployment
import Netlib.Protocol.CampusWithdrawal

/-!
# Duplex campus topology and current session permission

Request and reply paths share the declared gateway interpretation.
Faults preserve endpoints and permit at most one internal node withdrawal.
-/

namespace Netlib.Examples.CampusDuplex

open Network Protocol
open StatefulFailover (Gateway)
abbrev Node := Campus.Node

def physical : Network Node := CampusNAT.physical

def gatewayNode : Gateway → Node
  | .primary => .gatewayA
  | .standby => .gatewayB

def accessPoint : Gateway → Node
  | .primary => .apA
  | .standby => .apB

def source : FlowNAT.Direction → Node
  | .original => .client
  | .reply => .server

def target : FlowNAT.Direction → Node
  | .original => .server
  | .reply => .client

def routeTrace (gateway : Gateway) : FlowNAT.Direction → List Node
  | .original => [.client, accessPoint gateway, gatewayNode gateway, .server]
  | .reply => [.server, gatewayNode gateway, accessPoint gateway, .client]

theorem route_walk (gateway : Gateway) (direction : FlowNAT.Direction) :
    Walk physical (source direction) (target direction) (routeTrace gateway direction) := by
  cases direction with
  | original =>
    change Walk physical .client .server [.client, accessPoint gateway, gatewayNode gateway, .server]
    exact .cons (next := accessPoint gateway)
      (by cases gateway <;> simp [physical, CampusNAT.physical, Network.union, Campus.base, Campus.access, Campus.distribution, accessPoint])
      (.cons (next := gatewayNode gateway)
        (by cases gateway <;> simp [physical, CampusNAT.physical, Network.union, Campus.base, Campus.access, Campus.distribution, accessPoint, gatewayNode])
        (.cons (next := Campus.Node.server)
          (by cases gateway <;> simp [physical, CampusNAT.physical, Network.union, Campus.base, Campus.access, Campus.distribution, gatewayNode]) (.nil _)))
  | reply =>
    change Walk physical .server .client [.server, gatewayNode gateway, accessPoint gateway, .client]
    exact .cons (next := gatewayNode gateway)
      (by cases gateway <;> simp [physical, CampusNAT.physical, Network.union, Campus.base, Campus.access, Campus.distribution, gatewayNode])
      (.cons (next := accessPoint gateway)
        (by cases gateway <;> simp [physical, CampusNAT.physical, Network.union, Campus.base, Campus.access, Campus.distribution, accessPoint, gatewayNode])
        (.cons (next := Campus.Node.client)
          (by cases gateway <;> simp [physical, CampusNAT.physical, Network.union, Campus.base, Campus.access, Campus.distribution, accessPoint]) (.nil _)))

theorem physical_symmetric (a b : Node) (edge : physical.link a b) : physical.link b a :=
  edge.elim Or.inr Or.inl

private theorem reachable_symmetric {net : Network Node}
    (symmetric : ∀ a b, net.link a b → net.link b a) {a b : Node} (path : net.Reachable a b) :
    net.Reachable b a := by
  induction path with
  | refl node => exact .refl node
  | @step first next last edge tail ih => exact ih.trans (.single (symmetric first next edge))

theorem fault_symmetric (fault : Fault Node) (links : ∀ a b, ¬fault.links a b)
    (a b : Node) (edge : (physical.afterFault fault).link a b) :
    (physical.afterFault fault).link b a :=
  ⟨physical_symmetric a b edge.1, edge.2.2.1, edge.2.1, links b a⟩

def Duplex (net : Network Node) : Prop := net.Reachable .client .server ∧ net.Reachable .server .client

theorem physical_duplex (fault : Fault Node)
    (admissible : singleInternalNode Campus.clients Campus.servers fault) : Duplex (physical.afterFault fault) := by
  have forward := CampusNAT.physical_failure_available fault admissible _ _ rfl rfl
  exact ⟨forward, reachable_symmetric (fault_symmetric fault admissible.2.2.2) forward⟩

def endpoints (node : Node) : Prop := Campus.clients node ∨ Campus.servers node

theorem physical_management_isolated : physical.Isolated endpoints Campus.managers := by
  apply Network.isolated_of_closed (· ≠ .management)
  · intro a b edge _
    cases a <;> cases b <;>
      simp_all [physical, CampusNAT.physical, Network.union, Campus.base, Campus.access, Campus.distribution]
  · intro a member
    cases a <;> simp_all [endpoints, Campus.clients, Campus.servers]
  · intro b member
    cases b <;> simp_all [Campus.managers]

theorem physical_request_mediated : physical.Mediated Campus.clients Campus.servers Campus.gateways :=
  CampusNAT.physical_gateway_mediated

theorem physical_reply_mediated : physical.Mediated Campus.servers Campus.clients Campus.gateways := by
  apply Network.mediated_of_cut (· = .server)
  · intro a b edge outsideA outsideB inside
    cases a <;> cases b <;>
      simp_all [physical, CampusNAT.physical, Network.union, Campus.base, Campus.access, Campus.distribution, Campus.gateways]
  · intro a member
    exact member
  · intro b member
    cases b <;> simp_all [Campus.clients]

def request (context : Context) (scope : Scope) : ZeroTrust.Request String String String :=
  ⟨context.consumer, scope.resource, scope.operation⟩

def network (context : Context) (session : EAPSession.State) (scope : Scope) (fault : Fault Node) : Network Node :=
  ZeroTrust.enforce (physical.afterFault fault) Campus.gateways (Session.policy context session.session) (request context scope)

theorem permitted_network_eq (context : Context) (session : EAPSession.State) (scope : Scope) (fault : Fault Node)
    (permitted : session.session.permits context scope = true) : network context session scope fault = physical.afterFault fault :=
  ZeroTrust.allowed_network_eq _ _ _ _ (by simpa only [request, Session.policy_allows] using permitted)

theorem management_isolated (context : Context) (session : EAPSession.State) (scope : Scope) (fault : Fault Node) :
    (network context session scope fault).Isolated endpoints Campus.managers :=
  isolated_mono physical_management_isolated (fun _ _ edge => edge.1.1)

theorem request_mediated (context : Context) (session : EAPSession.State) (scope : Scope) (fault : Fault Node) :
    (network context session scope fault).Mediated Campus.clients Campus.servers Campus.gateways :=
  mediated_mono physical_request_mediated (fun _ _ edge => edge.1.1)

theorem reply_mediated (context : Context) (session : EAPSession.State) (scope : Scope) (fault : Fault Node) :
    (network context session scope fault).Mediated Campus.servers Campus.clients Campus.gateways :=
  mediated_mono physical_reply_mediated (fun _ _ edge => edge.1.1)

theorem permitted_duplex (context : Context) (session : EAPSession.State) (scope : Scope) (fault : Fault Node)
    (admissible : singleInternalNode Campus.clients Campus.servers fault)
    (permitted : session.session.permits context scope = true) : Duplex (network context session scope fault) := by
  rw [permitted_network_eq context session scope fault permitted]
  exact physical_duplex fault admissible

theorem denied_request_isolated (context : Context) (session : EAPSession.State) (scope : Scope) (fault : Fault Node)
    (denied : session.session.permits context scope = false) :
    (network context session scope fault).Isolated Campus.clients Campus.servers := by
  have mediated : (physical.afterFault fault).Mediated Campus.clients Campus.servers Campus.gateways :=
    mediated_mono physical_request_mediated (fun _ _ edge => edge.1)
  apply ZeroTrust.denied_isolated mediated
  · intro node member
    cases node <;> simp_all [Campus.clients, Campus.gateways]
  · intro node member
    cases node <;> simp_all [Campus.servers, Campus.gateways]
  · simpa only [request, Session.policy_allows] using denied

theorem denied_reply_isolated (context : Context) (session : EAPSession.State) (scope : Scope) (fault : Fault Node)
    (denied : session.session.permits context scope = false) :
    (network context session scope fault).Isolated Campus.servers Campus.clients := by
  have mediated : (physical.afterFault fault).Mediated Campus.servers Campus.clients Campus.gateways :=
    mediated_mono physical_reply_mediated (fun _ _ edge => edge.1)
  apply ZeroTrust.denied_isolated mediated
  · intro node member
    cases node <;> simp_all [Campus.servers, Campus.gateways]
  · intro node member
    cases node <;> simp_all [Campus.clients, Campus.gateways]
  · simpa only [request, Session.policy_allows] using denied

theorem duplex_reachable_iff (context : Context) (session : EAPSession.State) (scope : Scope) (fault : Fault Node)
    (admissible : singleInternalNode Campus.clients Campus.servers fault) :
    Duplex (network context session scope fault) ↔ session.session.permits context scope = true := by
  constructor
  · intro duplex
    cases permitted : session.session.permits context scope with
    | false => exact False.elim (denied_request_isolated context session scope fault permitted _ _ rfl rfl duplex.1)
    | true => rfl
  · exact permitted_duplex context session scope fault admissible

theorem selected_route (context : Context) (session : EAPSession.State) (scope : Scope) (fault : Fault Node)
    (gateway : Gateway) (direction : FlowNAT.Direction)
    (permitted : session.session.permits context scope = true)
    (nodes : ∀ node ∈ routeTrace gateway direction, ¬fault.nodes node) (links : ∀ a b, ¬fault.links a b) :
    Walk (network context session scope fault) (source direction) (target direction) (routeTrace gateway direction) := by
  rw [permitted_network_eq context session scope fault permitted]
  exact (route_walk gateway direction).afterFault nodes (fun a b _ => links a b)

def primaryWithdrawal : Fault Node := .node .gatewayA

theorem primaryWithdrawal_admissible : singleInternalNode Campus.clients Campus.servers primaryWithdrawal :=
  singleInternalNode_node (sources := Campus.clients) (targets := Campus.servers) Campus.Node.gatewayA (by simp [Campus.clients]) (by simp [Campus.servers])

theorem standby_after_withdrawal (context : Context) (session : EAPSession.State) (scope : Scope)
    (direction : FlowNAT.Direction) (permitted : session.session.permits context scope = true) :
    Walk (network context session scope primaryWithdrawal) (source direction) (target direction) (routeTrace .standby direction) := by
  apply selected_route context session scope primaryWithdrawal .standby direction permitted
  · cases direction <;> simp [routeTrace, accessPoint, gatewayNode, primaryWithdrawal, Fault.node]
  · simp [primaryWithdrawal, Fault.node]

def interpretation (context : Context) (session : EAPSession.State) (scope : Scope)
    (state : CampusWithdrawal.State) : Network Node :=
  network context session scope (if state.withdrawn then primaryWithdrawal else Fault.none)

theorem interpretation_duplex_iff (context : Context) (session : EAPSession.State) (scope : Scope)
    (state : CampusWithdrawal.State) :
    Duplex (interpretation context session scope state) ↔ session.session.permits context scope = true := by
  cases withdrawn : state.withdrawn
  · simpa only [interpretation, withdrawn, Bool.false_eq_true, ite_false] using
      duplex_reachable_iff context session scope Fault.none (singleInternalNode_none _ _)
  · simpa only [interpretation, withdrawn, ite_true] using
      duplex_reachable_iff context session scope primaryWithdrawal primaryWithdrawal_admissible

theorem interpretation_management_isolated (context : Context) (session : EAPSession.State) (scope : Scope)
    (state : CampusWithdrawal.State) : (interpretation context session scope state).Isolated endpoints Campus.managers :=
  management_isolated context session scope _

theorem interpretation_request_mediated (context : Context) (session : EAPSession.State) (scope : Scope)
    (state : CampusWithdrawal.State) :
    (interpretation context session scope state).Mediated Campus.clients Campus.servers Campus.gateways :=
  request_mediated context session scope _

theorem interpretation_reply_mediated (context : Context) (session : EAPSession.State) (scope : Scope)
    (state : CampusWithdrawal.State) :
    (interpretation context session scope state).Mediated Campus.servers Campus.clients Campus.gateways :=
  reply_mediated context session scope _

theorem withdrawn_pending_path (context : Context) (session : EAPSession.State) (scope : Scope)
    (state : CampusWithdrawal.State) (safe : state.Safe) (withdrawn : state.withdrawn = true)
    (item : Theory.Outstanding.Item SafeHandoff.Ticket) (member : item ∈ state.handoff.work.pending)
    (permitted : session.session.permits context scope = true) :
    item.value.gateway = .standby ∧
      Walk (interpretation context session scope state) (source item.value.direction) (target item.value.direction)
        (routeTrace item.value.gateway item.value.direction) := by
  have assigned := state.pending_standby safe withdrawn item member
  refine ⟨assigned, ?_⟩
  simpa only [interpretation, withdrawn, Bool.true_eq_false, ite_true, assigned] using
    standby_after_withdrawal context session scope item.value.direction permitted

theorem observed_admission_duplex {context : Context} {initial : EAPSession.State}
    {observations : List Check.EAP.Observation} (report : Check.EAP.Report context initial observations)
    (safe : initial.Safe context) (compliant : report.compliant = true)
    (finding : Check.EAP.Finding) (member : finding ∈ report.findings) (scope : Scope)
    (event : finding.observation.event = .application (.request scope))
    (accepted : finding.observation.accepted = some true) (fault : Fault Node)
    (admissible : singleInternalNode Campus.clients Campus.servers fault) :
    EAPAuth.State.Ready (EAPSession.authContext context) finding.result.auth ∧
      Session.Valid context finding.result.session scope ∧ Duplex (network context finding.result scope fault) := by
  obtain ⟨selected, requested, _, valid, ready⟩ := report.observed_admission_valid safe compliant finding member accepted
  have same : selected = scope := by rw [event] at requested; cases requested; rfl
  subst selected
  exact ⟨ready, valid, permitted_duplex context finding.result scope fault admissible ((Session.permits_iff _ _ _).mpr valid)⟩

end Netlib.Examples.CampusDuplex
