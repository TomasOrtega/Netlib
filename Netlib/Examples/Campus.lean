import Netlib.Network.Contract
import Netlib.Network.Failure
import Netlib.Network.Upgrade

/-!
# Campus composition

Two disjoint access paths connect a client to an application server.
Session observations control both enforcement gateways.
Identity and token integrity are supplied evidence, not cryptographic proofs.
-/

namespace Netlib.Examples.Campus

open Network Protocol

inductive Node
  | client | apA | gatewayA | apB | gatewayB | server | management
  deriving Repr, DecidableEq, BEq

def clients : Node → Prop := (· = .client)
def servers : Node → Prop := (· = .server)
def managers : Node → Prop := (· = .management)
def gateways (node : Node) : Prop := node = .gatewayA ∨ node = .gatewayB

def access : Network Node where
  link a b := a = .client ∧ (b = .apA ∨ b = .apB)

def distribution : Network Node where
  link a b := (a = .apA ∧ b = .gatewayA) ∨ (a = .apB ∧ b = .gatewayB) ∨
    ((a = .gatewayA ∨ a = .gatewayB) ∧ b = .server)

def base : Network Node := Network.union access distribution

theorem management_isolated : base.Isolated clients managers := by
  apply isolated_union_of_closed (region := (· ≠ .management))
  · intro a b _ edge
    cases a <;> cases b <;> simp_all [access]
  · intro a b _ edge
    cases a <;> cases b <;> simp_all [distribution]
  · intro a source
    cases a <;> simp_all [clients]
  · intro b target
    cases b <;> simp_all [managers]

private def beforeGateways (node : Node) : Prop :=
  node = .client ∨ node = .apA ∨ node = .apB

theorem gateway_mediated : base.Mediated clients servers gateways := by
  apply mediated_union_of_closed (region := beforeGateways)
  · intro a b inside edge
    cases a <;> cases b <;> simp_all [Network.without, Network.restrict, access, gateways, beforeGateways]
  · intro a b inside edge
    cases a <;> cases b <;> simp_all [Network.without, Network.restrict, distribution, gateways, beforeGateways]
  · intro a source
    cases a <;> simp_all [clients, beforeGateways]
  · intro b target
    cases b <;> simp_all [servers, beforeGateways]

theorem service_survives_one_internal_failure :
    base.RobustAvailable (singleInternalNode clients servers) clients servers := by
  apply robustAvailable_disjoint_walks
  intro source target sourceMember targetMember
  have sourceIsClient : source = .client := sourceMember
  have targetIsServer : target = .server := targetMember
  subst source
  subst target
  refine ⟨[.client, .apA, .gatewayA, .server], [.client, .apB, .gatewayB, .server], ?_, ?_, ?_⟩
  · exact .cons (by simp [base, Network.union, access])
      (.cons (by simp [base, Network.union, distribution])
        (.cons (by simp [base, Network.union, distribution]) (.nil _)))
  · exact .cons (by simp [base, Network.union, access])
      (.cons (by simp [base, Network.union, distribution])
        (.cons (by simp [base, Network.union, distribution]) (.nil _)))
  · intro node firstMember secondMember
    cases node <;> simp_all

def context : Context := ⟨"campus-client", "campus-application", "campus-authority"⟩
def application : Scope := ⟨"application", "read"⟩

def request : ZeroTrust.Request String String String :=
  ⟨context.consumer, application.resource, application.operation⟩

def applicationNetwork (session : Session) (fault : Fault Node) : Network Node :=
  ZeroTrust.enforce (base.afterFault fault) gateways (Session.policy context session) request

theorem permitted_network_eq (session : Session) (fault : Fault Node)
    (permitted : session.permits context application = true) :
    applicationNetwork session fault = base.afterFault fault :=
  ZeroTrust.allowed_network_eq _ _ _ _
    (by simpa only [request, Session.policy_allows] using permitted)

theorem permitted_available (session : Session) (fault : Fault Node)
    (admissible : singleInternalNode clients servers fault)
    (permitted : session.permits context application = true) :
    (applicationNetwork session fault).Available clients servers := by
  rw [permitted_network_eq session fault permitted]
  exact service_survives_one_internal_failure fault admissible

theorem denied_isolated (session : Session) (fault : Fault Node)
    (denied : session.permits context application = false) :
    (applicationNetwork session fault).Isolated clients servers := by
  have mediated : (base.afterFault fault).Mediated clients servers gateways :=
    mediated_mono gateway_mediated (fun _ _ edge => edge.1)
  apply ZeroTrust.denied_isolated mediated
  · intro source member
    cases source <;> simp_all [clients, gateways]
  · intro target member
    cases target <;> simp_all [servers, gateways]
  · simpa only [request, Session.policy_allows] using denied

theorem application_management_isolated (session : Session) (fault : Fault Node) :
    (applicationNetwork session fault).Isolated clients managers :=
  isolated_mono management_isolated (fun _ _ edge => edge.1.1)

theorem application_gateway_mediated (session : Session) (fault : Fault Node) :
    (applicationNetwork session fault).Mediated clients servers gateways :=
  mediated_mono gateway_mediated (fun _ _ edge => edge.1.1)

theorem application_reachable_iff (session : Session) (fault : Fault Node)
    (admissible : singleInternalNode clients servers fault) :
    (applicationNetwork session fault).Reachable .client .server ↔
      session.permits context application = true := by
  constructor
  · intro path
    cases guard : session.permits context application with
    | false => exact False.elim (denied_isolated session fault guard _ _ rfl rfl path)
    | true => rfl
  · intro permitted
    exact permitted_available session fault admissible permitted _ _ rfl rfl

theorem trace_admission_available {session : Session} {events : List Event}
    (execution : (Session.transition context).Trace Session.initial events session)
    (recorded : session.admitted = some application)
    (fault : Fault Node) (admissible : singleInternalNode clients servers fault) :
    Session.Valid context session application ∧
      (applicationNetwork session fault).Available clients servers := by
  have safe := (Session.transition_safe context).trace (Session.initial_safe context) execution
  have permitted := safe application recorded
  exact ⟨(Session.permits_iff _ _ _).mp permitted,
    permitted_available session fault admissible permitted⟩

theorem run_admission_available (events : List Event)
    (recorded : (Session.run context Session.initial events).admitted = some application)
    (fault : Fault Node) (admissible : singleInternalNode clients servers fault) :
    Session.Valid context (Session.run context Session.initial events) application ∧
      (applicationNetwork (Session.run context Session.initial events) fault).Available clients servers := by
  have valid := Session.admitted_valid context Session.initial events
    (Session.initial_safe context) application recorded
  exact ⟨valid, permitted_available _ fault admissible ((Session.permits_iff _ _ _).mpr valid)⟩

def sessionContract (session : Session) : Prop :=
  Session.Safe context session ∧
  ∀ fault, singleInternalNode clients servers fault →
    (applicationNetwork session fault).Isolated clients managers ∧
    ((applicationNetwork session fault).Reachable .client .server ↔
      session.permits context application = true)

/-- Every intermediate session preserves the modeled application contract. -/
theorem session_updates_preserve (events : List Event) :
    Network.Upgrade.Preserves (Session.step context) sessionContract Session.initial events := by
  apply Network.Upgrade.of_invariant
  · intro before event after _ edge
    change Session.step context before event = after at edge
    subst after
    exact ⟨Session.step_safe _ _ _, fun fault admissible =>
      ⟨application_management_isolated _ fault, application_reachable_iff _ fault admissible⟩⟩
  · exact ⟨Session.initial_safe _, fun fault admissible =>
      ⟨application_management_isolated _ fault, application_reachable_iff _ fault admissible⟩⟩

end Netlib.Examples.Campus
