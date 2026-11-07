import Netlib.Check.CampusTCPApplicationService
import Netlib.Check.CampusTCPTwoProgressSetup
import Netlib.Check.CampusTCPRecoveryRoundNetwork

/-!
# Actual network moves for two TCP records

Both directions use the selected current gateway.
Assignments and services retain endpoint history and old pending work.
-/

namespace Netlib.Check.CampusTCPTwoProgressNetwork

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPTwoProgressStart
open CampusTCPRound (Cut)
open CampusTCPGapProgressPhaseBase (Anchor Move)

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
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper} {entry : NetfilterNAT.Entry}

theorem owner_at (native : NativeEnv cut gateway entry) (state : State input)
    (same : CampusTCPRoundEnvironment.environment cut.report.final = CampusTCPRoundEnvironment.environment state)
    (actor : Actor) : state.owner actor = gateway := by
  have owners := congrArg CampusTCPRoundEnvironment.Environment.owners same
  change cut.report.final.owners = state.owners at owners
  simpa only [State.owner, ← owners] using native.owners actor

theorem installed_at (native : NativeEnv cut gateway entry) (state : State input)
    (same : CampusTCPRoundEnvironment.environment cut.report.final = CampusTCPRoundEnvironment.environment state)
    (selected : gateway = .standby) : state.installation.isSome = true := by
  have installed := congrArg CampusTCPRoundEnvironment.Environment.installed same
  change cut.report.final.installation.isSome = state.installation.isSome at installed
  obtain ⟨installation, present, _, _⟩ := native.standby selected
  rw [present] at installed
  exact installed.symm

theorem primary_at (native : NativeEnv cut gateway entry) (state : State input)
    (same : CampusTCPRoundEnvironment.environment cut.report.final = CampusTCPRoundEnvironment.environment state)
    (selected : gateway = .primary) : state.primarySealed = false ∧ state.primaryFenced = false := by
  have sealed := congrArg CampusTCPRoundEnvironment.Environment.primarySealed same
  have fenced := congrArg CampusTCPRoundEnvironment.Environment.primaryFenced same
  exact ⟨sealed.symm.trans (native.primary selected).1, fenced.symm.trans (native.primary selected).2⟩

theorem route_at (native : NativeEnv cut gateway entry) (state : State input)
    (same : CampusTCPRoundEnvironment.environment cut.report.final = CampusTCPRoundEnvironment.environment state)
    (actor : Actor) : RouteReady state actor := by
  have paused := congrArg CampusTCPRoundEnvironment.Environment.assignmentPaused same
  refine ⟨paused.symm.trans native.unpaused, ?_, ?_, ?_⟩
  · rw [owner_at native state same actor]
    exact native.configured
  · intro primary
    exact primary_at native state same ((owner_at native state same actor).symm.trans primary)
  · intro standby
    exact installed_at native state same ((owner_at native state same actor).symm.trans standby)

theorem service_phase_at (native : NativeEnv cut gateway entry) (state : State input)
    (same : CampusTCPRoundEnvironment.environment cut.report.final = CampusTCPRoundEnvironment.environment state) :
    CampusTCPGatewayEnabled.ServicePhaseReady state gateway := by
  have paused := congrArg CampusTCPRoundEnvironment.Environment.assignmentPaused same
  exact ⟨primary_at native state same, fun selected =>
    ⟨paused.symm.trans native.unpaused, installed_at native state same selected⟩⟩

theorem service_environment (anchor : Anchor cut current) :
    (beforeService input cut.report.final gateway).environment =
      (beforeService input current.report.final gateway).environment :=
  CampusTCPRoundEnvironment.service_environment _ _ anchor.environment gateway

private def networkMove (current : Cut input complete) (actual : Step input)
    (before : actual.before = current.report.final) (supported : actual.result.supported = true)
    (passed : actual.result.passed = true) (event : CampusTCPRoundClock.NetworkAction actual.event) : Move current actual :=
  ⟨current.appendNetwork actual before supported event, before, supported, passed, rfl, rfl⟩

structure AssignmentMove (initial : TwoWriteInitial cut sender gateway lower upper) (current : Cut input complete)
    (index : Nat) (ingress : I.InterfaceRef) (produced : Produced input.active input.passive) (actual : Step input) where
  move : Move current actual
  facts : A.AssignmentFacts current.report.final index ingress produced actual
  endpoints : move.after.endpoints = current.endpoints
  serviceFrame : ∀ selected, beforeService input move.after.report.final selected = beforeService input current.report.final selected
  environment : CampusTCPRoundEnvironment.environment current.report.final =
    CampusTCPRoundEnvironment.environment move.after.report.final
  anchor : Anchor cut move.after
  selected : current.report.final.owner produced.actor = gateway

theorem assign_at (initial : TwoWriteInitial cut sender gateway lower upper) (native : NativeEnv cut gateway initial.gatewayState.session.entry)
    (current : Cut input complete) (anchor : Anchor cut current) (index : Nat) (produced : Produced input.active input.passive)
    (source : current.report.final.outputs[index]? = some produced) (pending : IngressPending current.report.final index) :
    ∃ actual : Step input, Nonempty (AssignmentMove initial current index (native.ingress produced.actor) produced actual) := by
  obtain ⟨actual, facts⟩ := CampusTCPRoundAssignment.Report.assign_enabled current.report index (native.ingress produced.actor)
    produced source (route_at native current.report.final anchor.environment produced.actor) pending
  let move := networkMove current actual facts.beforeEq facts.supported facts.passed (by rw [facts.event]; exact .assign _ _)
  have environment : CampusTCPRoundEnvironment.environment current.report.final =
      CampusTCPRoundEnvironment.environment move.after.report.final := by
    rw [move.final, ← facts.beforeEq]
    exact CampusTCPRoundEnvironment.Step.environment actual (by rw [facts.event]; trivial)
  refine ⟨actual, ⟨⟨move, facts, rfl, ?_, environment,
    ⟨anchor.guards, anchor.retained.trans move.retained, anchor.environment.trans environment⟩,
    owner_at native current.report.final anchor.environment produced.actor⟩⟩⟩
  intro selected
  rw [move.final, ← facts.beforeEq]
  exact CampusTCPRoundLocal.step_service_nonservice actual (by rw [facts.event]; trivial) selected

variable {index : Nat} {ingress : I.InterfaceRef} {produced : Produced input.active input.passive} {actual : Step input}

def AssignmentMove.ticket (_value : AssignmentMove initial current index ingress produced actual) :
    O.Item (Ticket input.active input.passive) := A.ticket current.report.final index ingress produced

theorem AssignmentMove.pending (value : AssignmentMove initial current index ingress produced actual) :
    value.ticket ∈ value.move.after.report.final.work.pending := by
  rw [value.move.final]
  exact value.facts.pending

theorem AssignmentMove.ticket_gateway (value : AssignmentMove initial current index ingress produced actual) :
    value.ticket.value.gateway = gateway := value.selected

theorem Step.assign (actual : Step input) (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (current : Cut input complete) (anchor : Anchor cut current)
    (index : Nat) (produced : Produced input.active input.passive)
    (source : current.report.final.outputs[index]? = some produced) (pending : IngressPending current.report.final index)
    (before : actual.before = current.report.final) (event : actual.event = .assign index (native.ingress produced.actor)) :
    Nonempty (AssignmentMove initial current index (native.ingress produced.actor) produced actual) := by
  obtain ⟨enabled, ⟨facts⟩⟩ := assign_at initial native current anchor index produced source pending
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (facts.move.beforeEq.trans before.symm) (facts.facts.event.trans event.symm)
  exact ⟨same ▸ facts⟩

structure ServiceMove (initial : TwoWriteInitial cut sender gateway lower upper) (current : Cut input complete)
    (item : O.Item (Ticket input.active input.passive)) (hit : FlowNAT.Hit) (session : Admission.Session)
    (actual : Step input) (served : Served input) (emission : WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission) where
  move : Move current actual
  facts : S.ServiceFacts current.report.final item hit session actual served emission emitted
  endpoints : move.after.endpoints = current.endpoints
  environment : CampusTCPRoundEnvironment.environment current.report.final =
    CampusTCPRoundEnvironment.environment move.after.report.final
  anchor : Anchor cut move.after
  selected : item.value.gateway = gateway

private def serviceMove (anchor : Anchor cut current) (selected : item.value.gateway = gateway)
    (facts : S.ServiceFacts current.report.final item hit session actual served emission emitted) :
    ServiceMove initial current item hit session actual served emission emitted := by
  let move := networkMove current actual facts.beforeEq facts.supported facts.passed (by rw [facts.event]; exact .serve _ _)
  have environment : CampusTCPRoundEnvironment.environment current.report.final =
      CampusTCPRoundEnvironment.environment move.after.report.final := by rw [move.final]; exact facts.environment
  exact ⟨move, facts, rfl, environment,
    ⟨anchor.guards, anchor.retained.trans move.retained, anchor.environment.trans environment⟩, selected⟩

theorem serve_at (initial : TwoWriteInitial cut sender gateway lower upper) (native : NativeEnv cut gateway initial.gatewayState.session.entry)
    (current : Cut input complete) (anchor : Anchor cut current)
    (item : O.Item (Ticket input.active input.passive)) (member : item ∈ current.report.final.work.pending)
    (selected : item.value.gateway = gateway) (hit : FlowNAT.Hit) (session : Admission.Session)
    (ready : CampusTCPService.ExistingDataReady (input.contextFor item.value.gateway)
      (beforeService input current.report.final item.value.gateway) item.value.source input.zone item.value.ingress
      hit session item.value.produced.actor.nextHop) :
    ∃ actual : Step input, ∃ served : Served input, ∃ emission : WireForwarding.Emission served.ticket.value.source.packet,
      ∃ emitted : served.evidence.output = some emission,
        Nonempty (ServiceMove initial current item hit session actual served emission emitted) := by
  have phase : CampusTCPGatewayEnabled.ServicePhaseReady current.report.final item.value.gateway := by
    rw [selected]
    exact service_phase_at native current.report.final anchor.environment
  obtain ⟨actual, served, emission, emitted, facts⟩ :=
    CampusTCPRoundService.Report.serve_enabled current.report item member phase hit session ready
  exact ⟨actual, served, emission, emitted, ⟨serviceMove anchor selected facts⟩⟩

theorem serve_repeated_at (initial : TwoWriteInitial cut sender gateway lower upper) (native : NativeEnv cut gateway initial.gatewayState.session.entry)
    (current : Cut input complete) (anchor : Anchor cut current)
    (item : O.Item (Ticket input.active input.passive)) (member : item ∈ current.report.final.work.pending)
    (selected : item.value.gateway = gateway) (hit : FlowNAT.Hit) (session : Admission.Session)
    (ready : CampusTCPService.ExistingRepeatedReady (input.contextFor item.value.gateway)
      (beforeService input current.report.final item.value.gateway) item.value.source input.zone item.value.ingress
      hit session item.value.produced.actor.nextHop) :
    ∃ actual : Step input, ∃ served : Served input, ∃ emission : WireForwarding.Emission served.ticket.value.source.packet,
      ∃ emitted : served.evidence.output = some emission,
        Nonempty (ServiceMove initial current item hit session actual served emission emitted) := by
  have phase : CampusTCPGatewayEnabled.ServicePhaseReady current.report.final item.value.gateway := by
    rw [selected]
    exact service_phase_at native current.report.final anchor.environment
  obtain ⟨actual, served, emission, emitted, facts⟩ :=
    CampusTCPRecoveryRoundNetwork.Report.serve_repeated_enabled current.report item member phase hit session ready
  exact ⟨actual, served, emission, emitted, ⟨serviceMove anchor selected facts⟩⟩

def afterProcessing (processing : CampusTCPService.Processing context before source zone mode) : CampusTCPService.Before :=
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

theorem ServiceMove.after_before (value : ServiceMove initial current item hit session actual served emission emitted)
    (processing : CampusTCPService.Processing (input.contextFor served.ticket.value.gateway)
      served.before served.ticket.value.source input.zone served.mode) (present : served.evidence.processing = some processing) :
    beforeService input value.move.after.report.final gateway = afterProcessing processing := by
  have previous : served.before = beforeService input current.report.final gateway := by
    rw [value.facts.current, value.selected]
  have environment := CampusTCPRoundEnvironment.service_environment _ _ value.environment gateway
  apply before_eq
  · exact environment.symm.trans (congrArg CampusTCPService.Before.environment previous).symm
  · rw [value.move.final]
    have tracker := value.facts.tracker processing present
    rw [value.selected] at tracker
    exact tracker
  · rw [value.move.final]
    have admission := value.facts.admission processing present
    rw [value.selected] at admission
    exact admission

theorem ServiceMove.ordinary_mode (value : ServiceMove initial current item hit session actual served emission emitted) :
    served.mode = AdmissionExecution.Mode.ordinary := by
  simpa only [current.connection, Connection.admissionMode] using value.facts.mode

def ServiceMove.ordinaryEvidence (value : ServiceMove initial current item hit session actual served emission emitted) :=
  CampusTCPApplicationService.ordinaryEvidence served.evidence value.ordinary_mode

theorem ServiceMove.ordinary_processing (value : ServiceMove initial current item hit session actual served emission emitted) :
    ∃ processing : CampusTCPService.Processing (input.contextFor served.ticket.value.gateway)
        served.before served.ticket.value.source input.zone,
      value.ordinaryEvidence.processing = some processing ∧
        processing.outcome.nextHop = some item.value.produced.actor.nextHop ∧
        processing.prepared.attachment.entry = session.entry ∧
        processing.prepared.attachment.direction = hit.direction ∧ processing.prepared.attachment.fresh = false :=
  CampusTCPApplicationService.ordinary_processing value.facts value.ordinary_mode

theorem ServiceMove.after_ordinary_before (value : ServiceMove initial current item hit session actual served emission emitted)
    (processing : CampusTCPService.Processing (input.contextFor served.ticket.value.gateway)
      served.before served.ticket.value.source input.zone)
    (present : value.ordinaryEvidence.processing = some processing) :
    beforeService input value.move.after.report.final gateway = afterProcessing processing := by
  have original := CampusTCPApplicationService.restoreProcessing_present served.evidence processing value.ordinary_mode present
  have after := value.after_before (CampusTCPApplicationService.restoreProcessing processing value.ordinary_mode) original
  have fields := CampusTCPApplicationService.restoreProcessing_fields processing value.ordinary_mode
  rw [after]
  simp only [afterProcessing, fields.1, fields.2]

theorem ServiceMove.link_pending (value : ServiceMove initial current item hit session actual served emission emitted) :
    CampusTCPDeliveryEnabled.LinkPending value.move.after.report.final current.report.final.services.length := by
  obtain ⟨packet, member, _, payload, _⟩ := value.facts.link
  refine ⟨packet, by rw [value.move.final]; exact member, ?_⟩
  simp only [payload, Transit.linkAt]
  exact beq_self_eq_true _

theorem Step.serve (actual : Step input) (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (current : Cut input complete) (anchor : Anchor cut current)
    (item : O.Item (Ticket input.active input.passive)) (member : item ∈ current.report.final.work.pending)
    (selected : item.value.gateway = gateway) (hit : FlowNAT.Hit) (session : Admission.Session)
    (ready : CampusTCPService.ExistingDataReady (input.contextFor item.value.gateway)
      (beforeService input current.report.final item.value.gateway) item.value.source input.zone item.value.ingress
      hit session item.value.produced.actor.nextHop)
    (before : actual.before = current.report.final) (event : actual.event = .serve item.id none) :
    ∃ served : Served input, ∃ emission : WireForwarding.Emission served.ticket.value.source.packet,
      ∃ emitted : served.evidence.output = some emission,
        Nonempty (ServiceMove initial current item hit session actual served emission emitted) := by
  obtain ⟨enabled, served, emission, emitted, ⟨facts⟩⟩ := serve_at initial native current anchor item member selected hit session ready
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (facts.move.beforeEq.trans before.symm) (facts.facts.event.trans event.symm)
  subst enabled
  exact ⟨served, emission, emitted, ⟨facts⟩⟩

theorem Step.serve_repeated (actual : Step input) (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (current : Cut input complete) (anchor : Anchor cut current)
    (item : O.Item (Ticket input.active input.passive)) (member : item ∈ current.report.final.work.pending)
    (selected : item.value.gateway = gateway) (hit : FlowNAT.Hit) (session : Admission.Session)
    (ready : CampusTCPService.ExistingRepeatedReady (input.contextFor item.value.gateway)
      (beforeService input current.report.final item.value.gateway) item.value.source input.zone item.value.ingress
      hit session item.value.produced.actor.nextHop)
    (before : actual.before = current.report.final) (event : actual.event = .serve item.id none) :
    ∃ served : Served input, ∃ emission : WireForwarding.Emission served.ticket.value.source.packet,
      ∃ emitted : served.evidence.output = some emission,
        Nonempty (ServiceMove initial current item hit session actual served emission emitted) := by
  obtain ⟨enabled, served, emission, emitted, ⟨facts⟩⟩ := serve_repeated_at initial native current anchor item member selected hit session ready
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (facts.move.beforeEq.trans before.symm) (facts.facts.event.trans event.symm)
  subst enabled
  exact ⟨served, emission, emitted, ⟨facts⟩⟩

end Netlib.Check.CampusTCPTwoProgressNetwork
