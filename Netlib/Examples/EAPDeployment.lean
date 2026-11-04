import Netlib.Check.EAP
import Netlib.Examples.Campus

/-!
# Checked EAP principals and campus admission

The checker context supplies the principal for the modeled campus request.
An accepted application observation connects its current method evidence and
credential guard to the campus graph. This does not assert native application
admission or physical campus enforcement.
-/

namespace Netlib.Examples.EAPDeployment

open Network Protocol

def request (context : Context) : ZeroTrust.Request String String String :=
  ⟨context.consumer, Campus.application.resource, Campus.application.operation⟩

def network (context : Context) (state : EAPSession.State) (fault : Fault Campus.Node) : Network Campus.Node :=
  ZeroTrust.enforce (Campus.base.afterFault fault) Campus.gateways (Session.policy context state.session)
    (request context)

theorem permitted_network_eq (context : Context) (state : EAPSession.State) (fault : Fault Campus.Node)
    (permitted : state.session.permits context Campus.application = true) :
    network context state fault = Campus.base.afterFault fault :=
  ZeroTrust.allowed_network_eq _ _ _ _
    (by simpa only [request, Session.policy_allows] using permitted)

theorem permitted_available (context : Context) (state : EAPSession.State) (fault : Fault Campus.Node)
    (admissible : singleInternalNode Campus.clients Campus.servers fault)
    (permitted : state.session.permits context Campus.application = true) :
    (network context state fault).Available Campus.clients Campus.servers := by
  rw [permitted_network_eq context state fault permitted]
  exact Campus.service_survives_one_internal_failure fault admissible

theorem denied_isolated (context : Context) (state : EAPSession.State) (fault : Fault Campus.Node)
    (denied : state.session.permits context Campus.application = false) :
    (network context state fault).Isolated Campus.clients Campus.servers := by
  have mediated : (Campus.base.afterFault fault).Mediated Campus.clients Campus.servers Campus.gateways :=
    mediated_mono Campus.gateway_mediated (fun _ _ edge => edge.1)
  apply ZeroTrust.denied_isolated mediated
  · intro source member
    cases source <;> simp_all [Campus.clients, Campus.gateways]
  · intro target member
    cases target <;> simp_all [Campus.servers, Campus.gateways]
  · simpa only [request, Session.policy_allows] using denied

theorem management_isolated (context : Context) (state : EAPSession.State) (fault : Fault Campus.Node) :
    (network context state fault).Isolated Campus.clients Campus.managers :=
  isolated_mono Campus.management_isolated (fun _ _ edge => edge.1.1)

theorem gateway_mediated (context : Context) (state : EAPSession.State) (fault : Fault Campus.Node) :
    (network context state fault).Mediated Campus.clients Campus.servers Campus.gateways :=
  mediated_mono Campus.gateway_mediated (fun _ _ edge => edge.1.1)

theorem reachable_iff (context : Context) (state : EAPSession.State) (fault : Fault Campus.Node)
    (admissible : singleInternalNode Campus.clients Campus.servers fault) :
    (network context state fault).Reachable .client .server ↔ state.session.permits context Campus.application = true := by
  constructor
  · intro path
    cases guard : state.session.permits context Campus.application with
    | false => exact False.elim (denied_isolated context state fault guard _ _ rfl rfl path)
    | true => rfl
  · intro permitted
    exact permitted_available context state fault admissible permitted _ _ rfl rfl

theorem without_credential_isolated (context : Context) (state : EAPSession.State) (fault : Fault Campus.Node)
    (missing : state.session.credential = none) :
    (network context state fault).Isolated Campus.clients Campus.servers := by
  apply denied_isolated context state fault
  simp [Session.permits, Session.claims, missing]

theorem observed_admission_available {context : Context} {initial : EAPSession.State}
    {observations : List Check.EAP.Observation} (report : Check.EAP.Report context initial observations)
    (safe : initial.Safe context) (compliant : report.compliant = true)
    (finding : Check.EAP.Finding) (member : finding ∈ report.findings)
    (event : finding.observation.event = .application (.request Campus.application))
    (accepted : finding.observation.accepted = some true)
    (fault : Fault Campus.Node) (admissible : singleInternalNode Campus.clients Campus.servers fault) :
    EAPAuth.State.Ready (EAPSession.authContext context) finding.result.auth ∧
      Session.Valid context finding.result.session Campus.application ∧
      (network context finding.result fault).Available Campus.clients Campus.servers := by
  obtain ⟨scope, requested, _, valid, ready⟩ :=
    report.observed_admission_valid safe compliant finding member accepted
  have same : scope = Campus.application := by
    rw [event] at requested
    cases requested
    rfl
  subst scope
  exact ⟨ready, valid, permitted_available context finding.result fault admissible
    ((Session.permits_iff _ _ _).mpr valid)⟩

end Netlib.Examples.EAPDeployment
