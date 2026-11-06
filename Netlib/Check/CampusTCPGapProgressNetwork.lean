import Netlib.Check.CampusTCPGapProgressState
import Netlib.Check.CampusTCPRecoveryRoundNetwork

namespace Netlib.Check.CampusTCPGapProgressNetwork

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPGapProgressStart
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
variable {cut current : Cut input complete} {sender : Actor} {lower upper : List UInt8}
variable {initial : GapInitial cut sender lower upper} {entry : NetfilterNAT.Entry}

theorem owner_at (native : NativeEnv cut entry) (state : State input)
    (same : CampusTCPRoundEnvironment.environment cut.report.final = CampusTCPRoundEnvironment.environment state)
    (actor : Actor) : state.owner actor = .standby := by
  have owners := congrArg CampusTCPRoundEnvironment.Environment.owners same
  change cut.report.final.owners = state.owners at owners
  simpa only [State.owner, ← owners] using native.owners actor

theorem installed_at (native : NativeEnv cut entry) (state : State input)
    (same : CampusTCPRoundEnvironment.environment cut.report.final = CampusTCPRoundEnvironment.environment state) :
    state.installation.isSome = true := by
  have installed := congrArg CampusTCPRoundEnvironment.Environment.installed same
  change cut.report.final.installation.isSome = state.installation.isSome at installed
  rw [native.installed] at installed
  exact installed.symm

theorem route_at (native : NativeEnv cut entry) (state : State input)
    (same : CampusTCPRoundEnvironment.environment cut.report.final = CampusTCPRoundEnvironment.environment state)
    (actor : Actor) : RouteReady state actor := by
  have paused := congrArg CampusTCPRoundEnvironment.Environment.assignmentPaused same
  refine ⟨paused.symm.trans native.unpaused, ?_, ?_, fun _ => installed_at native state same⟩
  · rw [owner_at native state same actor]
    exact native.configured
  · intro primary
    rw [owner_at native state same actor] at primary
    cases primary

theorem service_phase_at (native : NativeEnv cut entry) (state : State input)
    (same : CampusTCPRoundEnvironment.environment cut.report.final = CampusTCPRoundEnvironment.environment state) :
    CampusTCPGatewayEnabled.ServicePhaseReady state .standby := by
  have paused := congrArg CampusTCPRoundEnvironment.Environment.assignmentPaused same
  constructor
  · intro impossible
    cases impossible
  · intro _
    exact ⟨paused.symm.trans native.unpaused, installed_at native state same⟩

theorem service_environment (anchor : Anchor cut current) :
    (beforeService input cut.report.final .standby).environment =
      (beforeService input current.report.final .standby).environment :=
  CampusTCPRoundEnvironment.service_environment _ _ anchor.environment .standby

private def networkMove (current : Cut input complete) (actual : Step input)
    (before : actual.before = current.report.final) (supported : actual.result.supported = true)
    (passed : actual.result.passed = true) (event : CampusTCPRoundClock.NetworkAction actual.event) : Move current actual :=
  ⟨current.appendNetwork actual before supported event, before, supported, passed, rfl, rfl⟩

structure AssignmentMove (initial : GapInitial cut sender lower upper) (current : Cut input complete)
    (index : Nat) (ingress : I.InterfaceRef) (produced : Produced input.active input.passive) (actual : Step input) where
  move : Move current actual
  facts : A.AssignmentFacts current.report.final index ingress produced actual
  endpoints : move.after.endpoints = current.endpoints
  gateway : ∀ selected, beforeService input move.after.report.final selected = beforeService input current.report.final selected
  environment : CampusTCPRoundEnvironment.environment current.report.final =
    CampusTCPRoundEnvironment.environment move.after.report.final
  anchor : Anchor cut move.after
  standby : current.report.final.owner produced.actor = .standby

theorem assign_at (initial : GapInitial cut sender lower upper) (native : NativeEnv cut initial.gateway.seed.entry)
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
    value.ticket.value.gateway = .standby := value.standby

def AssignmentMove.live (value : AssignmentMove initial current index ingress produced actual)
    (live : CampusTCPGapProgressState.Live initial current retries released) :
    CampusTCPGapProgressState.Live initial value.move.after retries released := by
  apply live.reindex value.move.retained value.environment
  · intro actor
    rw [value.endpoints]
  · rw [value.endpoints]
  · exact value.gateway .standby

theorem Step.assign (actual : Step input) (initial : GapInitial cut sender lower upper)
    (native : NativeEnv cut initial.gateway.seed.entry) (current : Cut input complete) (anchor : Anchor cut current)
    (index : Nat) (produced : Produced input.active input.passive)
    (source : current.report.final.outputs[index]? = some produced) (pending : IngressPending current.report.final index)
    (before : actual.before = current.report.final) (event : actual.event = .assign index (native.ingress produced.actor)) :
    Nonempty (AssignmentMove initial current index (native.ingress produced.actor) produced actual) := by
  obtain ⟨enabled, ⟨facts⟩⟩ := assign_at initial native current anchor index produced source pending
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (facts.move.beforeEq.trans before.symm) (facts.facts.event.trans event.symm)
  exact ⟨same ▸ facts⟩

structure ServiceMove (initial : GapInitial cut sender lower upper) (current : Cut input complete)
    (item : O.Item (Ticket input.active input.passive)) (hit : FlowNAT.Hit) (session : Admission.Session)
    (actual : Step input) (served : Served input) (emission : WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission) where
  move : Move current actual
  facts : S.ServiceFacts current.report.final item hit session actual served emission emitted
  endpoints : move.after.endpoints = current.endpoints
  environment : CampusTCPRoundEnvironment.environment current.report.final =
    CampusTCPRoundEnvironment.environment move.after.report.final
  anchor : Anchor cut move.after
  standby : item.value.gateway = .standby

private def serviceMove (anchor : Anchor cut current) (standby : item.value.gateway = .standby)
    (facts : S.ServiceFacts current.report.final item hit session actual served emission emitted) :
    ServiceMove initial current item hit session actual served emission emitted := by
  let move := networkMove current actual facts.beforeEq facts.supported facts.passed (by rw [facts.event]; exact .serve _ _)
  have environment : CampusTCPRoundEnvironment.environment current.report.final =
      CampusTCPRoundEnvironment.environment move.after.report.final := by rw [move.final]; exact facts.environment
  exact ⟨move, facts, rfl, environment,
    ⟨anchor.guards, anchor.retained.trans move.retained, anchor.environment.trans environment⟩, standby⟩

theorem serve_at (initial : GapInitial cut sender lower upper) (native : NativeEnv cut initial.gateway.seed.entry)
    (current : Cut input complete) (anchor : Anchor cut current)
    (item : O.Item (Ticket input.active input.passive)) (member : item ∈ current.report.final.work.pending)
    (standby : item.value.gateway = .standby) (hit : FlowNAT.Hit) (session : Admission.Session)
    (ready : CampusTCPService.ExistingDataReady (input.contextFor item.value.gateway)
      (beforeService input current.report.final item.value.gateway) item.value.source input.zone item.value.ingress
      hit session item.value.produced.actor.nextHop) :
    ∃ actual : Step input, ∃ served : Served input, ∃ emission : WireForwarding.Emission served.ticket.value.source.packet,
      ∃ emitted : served.evidence.output = some emission,
        Nonempty (ServiceMove initial current item hit session actual served emission emitted) := by
  have phase : CampusTCPGatewayEnabled.ServicePhaseReady current.report.final item.value.gateway := by
    rw [standby]
    exact service_phase_at native current.report.final anchor.environment
  obtain ⟨actual, served, emission, emitted, facts⟩ :=
    CampusTCPRoundService.Report.serve_enabled current.report item member phase hit session ready
  exact ⟨actual, served, emission, emitted, ⟨serviceMove anchor standby facts⟩⟩

theorem serve_repeated_at (initial : GapInitial cut sender lower upper) (native : NativeEnv cut initial.gateway.seed.entry)
    (current : Cut input complete) (anchor : Anchor cut current)
    (item : O.Item (Ticket input.active input.passive)) (member : item ∈ current.report.final.work.pending)
    (standby : item.value.gateway = .standby) (hit : FlowNAT.Hit) (session : Admission.Session)
    (ready : CampusTCPService.ExistingRepeatedReady (input.contextFor item.value.gateway)
      (beforeService input current.report.final item.value.gateway) item.value.source input.zone item.value.ingress
      hit session item.value.produced.actor.nextHop) :
    ∃ actual : Step input, ∃ served : Served input, ∃ emission : WireForwarding.Emission served.ticket.value.source.packet,
      ∃ emitted : served.evidence.output = some emission,
        Nonempty (ServiceMove initial current item hit session actual served emission emitted) := by
  have phase : CampusTCPGatewayEnabled.ServicePhaseReady current.report.final item.value.gateway := by
    rw [standby]
    exact service_phase_at native current.report.final anchor.environment
  obtain ⟨actual, served, emission, emitted, facts⟩ :=
    CampusTCPRecoveryRoundNetwork.Report.serve_repeated_enabled current.report item member phase hit session ready
  exact ⟨actual, served, emission, emitted, ⟨serviceMove anchor standby facts⟩⟩

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

theorem ServiceMove.after_before (value : ServiceMove initial current item hit session actual served emission emitted)
    (processing : CampusTCPService.Processing (input.contextFor served.ticket.value.gateway)
      served.before served.ticket.value.source input.zone) (present : served.evidence.processing = some processing) :
    beforeService input value.move.after.report.final .standby = afterProcessing processing := by
  have previous : served.before = beforeService input current.report.final .standby := by
    rw [value.facts.current, value.standby]
  have environment := CampusTCPRoundEnvironment.service_environment _ _ value.environment .standby
  apply before_eq
  · exact environment.symm.trans (congrArg CampusTCPService.Before.environment previous).symm
  · rw [value.move.final]
    have tracker := value.facts.tracker processing present
    rw [value.standby] at tracker
    exact tracker
  · rw [value.move.final]
    have admission := value.facts.admission processing present
    rw [value.standby] at admission
    exact admission

theorem ServiceMove.link_pending (value : ServiceMove initial current item hit session actual served emission emitted) :
    CampusTCPDeliveryEnabled.LinkPending value.move.after.report.final current.report.final.services.length := by
  obtain ⟨packet, member, _, payload, _⟩ := value.facts.link
  refine ⟨packet, by rw [value.move.final]; exact member, ?_⟩
  simp only [payload, Transit.linkAt]
  exact beq_self_eq_true _

theorem Step.serve (actual : Step input) (initial : GapInitial cut sender lower upper)
    (native : NativeEnv cut initial.gateway.seed.entry) (current : Cut input complete) (anchor : Anchor cut current)
    (item : O.Item (Ticket input.active input.passive)) (member : item ∈ current.report.final.work.pending)
    (standby : item.value.gateway = .standby) (hit : FlowNAT.Hit) (session : Admission.Session)
    (ready : CampusTCPService.ExistingDataReady (input.contextFor item.value.gateway)
      (beforeService input current.report.final item.value.gateway) item.value.source input.zone item.value.ingress
      hit session item.value.produced.actor.nextHop)
    (before : actual.before = current.report.final) (event : actual.event = .serve item.id none) :
    ∃ served : Served input, ∃ emission : WireForwarding.Emission served.ticket.value.source.packet,
      ∃ emitted : served.evidence.output = some emission,
        Nonempty (ServiceMove initial current item hit session actual served emission emitted) := by
  obtain ⟨enabled, served, emission, emitted, ⟨facts⟩⟩ := serve_at initial native current anchor item member standby hit session ready
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (facts.move.beforeEq.trans before.symm) (facts.facts.event.trans event.symm)
  subst enabled
  exact ⟨served, emission, emitted, ⟨facts⟩⟩

theorem Step.serve_repeated (actual : Step input) (initial : GapInitial cut sender lower upper)
    (native : NativeEnv cut initial.gateway.seed.entry) (current : Cut input complete) (anchor : Anchor cut current)
    (item : O.Item (Ticket input.active input.passive)) (member : item ∈ current.report.final.work.pending)
    (standby : item.value.gateway = .standby) (hit : FlowNAT.Hit) (session : Admission.Session)
    (ready : CampusTCPService.ExistingRepeatedReady (input.contextFor item.value.gateway)
      (beforeService input current.report.final item.value.gateway) item.value.source input.zone item.value.ingress
      hit session item.value.produced.actor.nextHop)
    (before : actual.before = current.report.final) (event : actual.event = .serve item.id none) :
    ∃ served : Served input, ∃ emission : WireForwarding.Emission served.ticket.value.source.packet,
      ∃ emitted : served.evidence.output = some emission,
        Nonempty (ServiceMove initial current item hit session actual served emission emitted) := by
  obtain ⟨enabled, served, emission, emitted, ⟨facts⟩⟩ := serve_repeated_at initial native current anchor item member standby hit session ready
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (facts.move.beforeEq.trans before.symm) (facts.facts.event.trans event.symm)
  subst enabled
  exact ⟨served, emission, emitted, ⟨facts⟩⟩

end Netlib.Check.CampusTCPGapProgressNetwork
