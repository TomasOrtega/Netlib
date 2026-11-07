import Netlib.Check.CampusTCPRecoveryRoundNetwork
import Netlib.Check.CampusTCPDeliveryEnabled

/-!
# Current network moves during planned transfer

Current route and gateway guards enable each actual assignment or service.
Primary service can drain pending work while assignments are paused.
-/

namespace Netlib.Check.CampusTCPTwoTransferNetwork

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)

namespace O
export Theory.Outstanding (Item)
end O
namespace A
export CampusTCPRoundAssignment (AssignmentFacts ticket)
end A
namespace S
export CampusTCPRoundService (ServiceFacts)
end S

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {current : Cut input complete}

private def networkMove (current : Cut input complete) (actual : Step input)
    (before : actual.before = current.report.final) (supported : actual.result.supported = true)
    (passed : actual.result.passed = true) (event : CampusTCPRoundClock.NetworkAction actual.event) : Move current actual :=
  ⟨current.appendNetwork actual before supported event, before, supported, passed, rfl, rfl⟩

structure Assignment (current : Cut input complete) (index : Nat) (ingress : I.InterfaceRef)
    (produced : Produced input.active input.passive) (actual : Step input) where
  move : Move current actual
  facts : A.AssignmentFacts current.report.final index ingress produced actual
  endpoints : move.after.endpoints = current.endpoints
  serviceFrame : ∀ gateway, beforeService input move.after.report.final gateway = beforeService input current.report.final gateway
  environment : CampusTCPRoundEnvironment.environment current.report.final =
    CampusTCPRoundEnvironment.environment move.after.report.final

theorem assign_at (current : Cut input complete) (index : Nat) (ingress : I.InterfaceRef)
    (produced : Produced input.active input.passive)
    (source : current.report.final.outputs[index]? = some produced)
    (route : RouteReady current.report.final produced.actor) (pending : IngressPending current.report.final index) :
    ∃ actual : Step input, Nonempty (Assignment current index ingress produced actual) := by
  obtain ⟨actual, facts⟩ := CampusTCPRoundAssignment.Report.assign_enabled current.report index ingress produced source route pending
  let move := networkMove current actual facts.beforeEq facts.supported facts.passed (by rw [facts.event]; exact .assign _ _)
  have environment : CampusTCPRoundEnvironment.environment current.report.final =
      CampusTCPRoundEnvironment.environment move.after.report.final := by
    rw [move.final, ← facts.beforeEq]
    exact CampusTCPRoundEnvironment.Step.environment actual (by rw [facts.event]; trivial)
  refine ⟨actual, ⟨⟨move, facts, rfl, ?_, environment⟩⟩⟩
  intro gateway
  rw [move.final, ← facts.beforeEq]
  exact CampusTCPRoundLocal.step_service_nonservice actual (by rw [facts.event]; trivial) gateway

variable {index : Nat} {ingress : I.InterfaceRef} {produced : Produced input.active input.passive} {actual : Step input}

def Assignment.ticket (_value : Assignment current index ingress produced actual) :
    O.Item (Ticket input.active input.passive) := A.ticket current.report.final index ingress produced

theorem Assignment.pending (value : Assignment current index ingress produced actual) :
    value.ticket ∈ value.move.after.report.final.work.pending := by
  rw [value.move.final]
  exact value.facts.pending

theorem Assignment.ticket_gateway (value : Assignment current index ingress produced actual) :
    value.ticket.value.gateway = current.report.final.owner produced.actor := rfl

theorem Step.assign (actual : Step input) (current : Cut input complete) (index : Nat) (ingress : I.InterfaceRef)
    (produced : Produced input.active input.passive)
    (source : current.report.final.outputs[index]? = some produced)
    (route : RouteReady current.report.final produced.actor) (pending : IngressPending current.report.final index)
    (before : actual.before = current.report.final) (event : actual.event = .assign index ingress) :
    Nonempty (Assignment current index ingress produced actual) := by
  obtain ⟨enabled, ⟨value⟩⟩ := assign_at current index ingress produced source route pending
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (value.move.beforeEq.trans before.symm) (value.facts.event.trans event.symm)
  exact ⟨same ▸ value⟩

structure Service (current : Cut input complete) (item : O.Item (Ticket input.active input.passive))
    (hit : FlowNAT.Hit) (session : Admission.Session) (actual : Step input) (served : Served input)
    (emission : WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission) where
  move : Move current actual
  facts : S.ServiceFacts current.report.final item hit session actual served emission emitted
  endpoints : move.after.endpoints = current.endpoints
  environment : CampusTCPRoundEnvironment.environment current.report.final =
    CampusTCPRoundEnvironment.environment move.after.report.final

variable {item : O.Item (Ticket input.active input.passive)} {hit : FlowNAT.Hit} {session : Admission.Session}
variable {served : Served input} {emission : WireForwarding.Emission served.ticket.value.source.packet}
variable {emitted : served.evidence.output = some emission}

private def serviceMove (facts : S.ServiceFacts current.report.final item hit session actual served emission emitted) :
    Service current item hit session actual served emission emitted := by
  let move := networkMove current actual facts.beforeEq facts.supported facts.passed (by rw [facts.event]; exact .serve _ _)
  have environment : CampusTCPRoundEnvironment.environment current.report.final =
      CampusTCPRoundEnvironment.environment move.after.report.final := by rw [move.final]; exact facts.environment
  exact ⟨move, facts, rfl, environment⟩

theorem serve_at (current : Cut input complete) (item : O.Item (Ticket input.active input.passive))
    (member : item ∈ current.report.final.work.pending)
    (phase : CampusTCPGatewayEnabled.ServicePhaseReady current.report.final item.value.gateway)
    (hit : FlowNAT.Hit) (session : Admission.Session)
    (ready : CampusTCPService.ExistingDataReady (input.contextFor item.value.gateway)
      (beforeService input current.report.final item.value.gateway) item.value.source input.zone item.value.ingress
      hit session item.value.produced.actor.nextHop) :
    ∃ actual : Step input, ∃ served : Served input, ∃ emission : WireForwarding.Emission served.ticket.value.source.packet,
      ∃ emitted : served.evidence.output = some emission,
        Nonempty (Service current item hit session actual served emission emitted) := by
  obtain ⟨actual, served, emission, emitted, facts⟩ :=
    CampusTCPRoundService.Report.serve_enabled current.report item member phase hit session ready
  exact ⟨actual, served, emission, emitted, ⟨serviceMove facts⟩⟩

theorem serve_repeated_at (current : Cut input complete) (item : O.Item (Ticket input.active input.passive))
    (member : item ∈ current.report.final.work.pending)
    (phase : CampusTCPGatewayEnabled.ServicePhaseReady current.report.final item.value.gateway)
    (hit : FlowNAT.Hit) (session : Admission.Session)
    (ready : CampusTCPService.ExistingRepeatedReady (input.contextFor item.value.gateway)
      (beforeService input current.report.final item.value.gateway) item.value.source input.zone item.value.ingress
      hit session item.value.produced.actor.nextHop) :
    ∃ actual : Step input, ∃ served : Served input, ∃ emission : WireForwarding.Emission served.ticket.value.source.packet,
      ∃ emitted : served.evidence.output = some emission,
        Nonempty (Service current item hit session actual served emission emitted) := by
  obtain ⟨actual, served, emission, emitted, facts⟩ :=
    CampusTCPRecoveryRoundNetwork.Report.serve_repeated_enabled current.report item member phase hit session ready
  exact ⟨actual, served, emission, emitted, ⟨serviceMove facts⟩⟩

def afterProcessing (processing : CampusTCPService.Processing context before source zone) : CampusTCPService.Before :=
  { before with tracker := processing.outcome.state, admission := processing.nextAdmission }

private theorem before_eq (before after : CampusTCPService.Before) (environment : before.environment = after.environment)
    (tracker : before.tracker = after.tracker) (admission : before.admission = after.admission) : before = after := by
  cases before
  cases after
  simp only [CampusTCPService.Before.environment, CampusTCPService.Before.Environment.mk.injEq] at environment
  rcases environment with ⟨rfl, rfl, rfl, rfl, rfl⟩
  cases tracker
  cases admission
  rfl

theorem Service.after_before (value : Service current item hit session actual served emission emitted)
    (processing : CampusTCPService.Processing (input.contextFor served.ticket.value.gateway)
      served.before served.ticket.value.source input.zone) (present : served.evidence.processing = some processing) :
    beforeService input value.move.after.report.final item.value.gateway = afterProcessing processing := by
  have environment := CampusTCPRoundEnvironment.service_environment _ _ value.environment item.value.gateway
  apply before_eq
  · exact environment.symm.trans (congrArg CampusTCPService.Before.environment value.facts.current).symm
  · rw [value.move.final]
    exact value.facts.tracker processing present
  · rw [value.move.final]
    exact value.facts.admission processing present

theorem Service.link_pending (value : Service current item hit session actual served emission emitted) :
    CampusTCPDeliveryEnabled.LinkPending value.move.after.report.final current.report.final.services.length := by
  obtain ⟨packet, member, _, payload, _⟩ := value.facts.link
  refine ⟨packet, by rw [value.move.final]; exact member, ?_⟩
  simp only [payload, Transit.linkAt]
  exact beq_self_eq_true _

theorem Step.serve (actual : Step input) (current : Cut input complete) (item : O.Item (Ticket input.active input.passive))
    (member : item ∈ current.report.final.work.pending)
    (phase : CampusTCPGatewayEnabled.ServicePhaseReady current.report.final item.value.gateway)
    (hit : FlowNAT.Hit) (session : Admission.Session)
    (ready : CampusTCPService.ExistingDataReady (input.contextFor item.value.gateway)
      (beforeService input current.report.final item.value.gateway) item.value.source input.zone item.value.ingress
      hit session item.value.produced.actor.nextHop)
    (before : actual.before = current.report.final) (event : actual.event = .serve item.id none) :
    ∃ served : Served input, ∃ emission : WireForwarding.Emission served.ticket.value.source.packet,
      ∃ emitted : served.evidence.output = some emission,
        Nonempty (Service current item hit session actual served emission emitted) := by
  obtain ⟨enabled, served, emission, emitted, ⟨value⟩⟩ := serve_at current item member phase hit session ready
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (value.move.beforeEq.trans before.symm) (value.facts.event.trans event.symm)
  subst enabled
  exact ⟨served, emission, emitted, ⟨value⟩⟩

theorem Step.serve_repeated (actual : Step input) (current : Cut input complete) (item : O.Item (Ticket input.active input.passive))
    (member : item ∈ current.report.final.work.pending)
    (phase : CampusTCPGatewayEnabled.ServicePhaseReady current.report.final item.value.gateway)
    (hit : FlowNAT.Hit) (session : Admission.Session)
    (ready : CampusTCPService.ExistingRepeatedReady (input.contextFor item.value.gateway)
      (beforeService input current.report.final item.value.gateway) item.value.source input.zone item.value.ingress
      hit session item.value.produced.actor.nextHop)
    (before : actual.before = current.report.final) (event : actual.event = .serve item.id none) :
    ∃ served : Served input, ∃ emission : WireForwarding.Emission served.ticket.value.source.packet,
      ∃ emitted : served.evidence.output = some emission,
        Nonempty (Service current item hit session actual served emission emitted) := by
  obtain ⟨enabled, served, emission, emitted, ⟨value⟩⟩ := serve_repeated_at current item member phase hit session ready
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (value.move.beforeEq.trans before.symm) (value.facts.event.trans event.symm)
  subst enabled
  exact ⟨served, emission, emitted, ⟨value⟩⟩

end Netlib.Check.CampusTCPTwoTransferNetwork
