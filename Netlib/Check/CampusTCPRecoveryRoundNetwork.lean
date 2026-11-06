import Netlib.Check.CampusTCPRecoveryRoundPhaseBase
import Netlib.Check.CampusTCPRoundService
import Netlib.Check.CampusTCPRoundAssignment

namespace Netlib.Check.CampusTCPRecoveryRoundNetwork

open Protocol CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)

namespace O
export Theory.Outstanding (Item Completed complete)
end O
namespace A
export CampusTCPRoundAssignment (AssignmentFacts ticket)
end A
namespace S
export CampusTCPRoundService (ServiceFacts)
end S

variable {input : Input} {events : List CampusTCPModel.Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}
variable {initial : Initial report complete request} {native : NativeEnv initial}

private theorem Processing.repeated_attachment (processing : CampusTCPService.Processing context before source zone)
    (ready : CampusTCPService.ExistingRepeatedReady context before source zone ingress hit session hop) :
    processing.prepared.attachment.entry = session.entry ∧
      processing.prepared.attachment.direction = hit.direction ∧ processing.prepared.attachment.fresh = false := by
  obtain ⟨record, prepared, _, member, same, attached, attachment, _⟩ :=
    ConntrackLifecycle.prepare_existing_completes before.tracker (CampusTCPService.packetInput before source zone).lifecycle
      hit ready.tracker.valid ready.tracker.zone ready.tracker.transport ready.tracker.candidate ready.tracker.lookup
  have actual : processing.prepared = prepared := Except.ok.inj (processing.attached.symm.trans attached)
  rw [actual, attachment]
  exact ⟨ready.binding record member same, rfl, rfl⟩

theorem Report.serve_repeated_enabled (report : Report input events)
    (item : O.Item (Ticket input.active input.passive)) (member : item ∈ report.final.work.pending)
    (phase : CampusTCPGatewayEnabled.ServicePhaseReady report.final item.value.gateway)
    (hit : FlowNAT.Hit) (session : TCP.Admission.Session)
    (ready : CampusTCPService.ExistingRepeatedReady (input.contextFor item.value.gateway)
      (beforeService input report.final item.value.gateway) item.value.source input.zone item.value.ingress
      hit session item.value.produced.actor.nextHop) :
    ∃ actual : Step input, ∃ served : Served input,
      ∃ emission : TCP.WireForwarding.Emission served.ticket.value.source.packet,
      ∃ emitted : served.evidence.output = some emission,
        S.ServiceFacts report.final item hit session actual served emission emitted := by
  let before := report.final
  obtain ⟨completed, completedAt, selected⟩ := Theory.Outstanding.complete_item before.work item (CampusTCPOrigins.Report.work_valid report) member
  have phaseSelected : CampusTCPGatewayEnabled.ServicePhaseReady before completed.item.value.gateway := by rw [selected]; exact phase
  have readySelected : CampusTCPService.ExistingRepeatedReady (input.contextFor completed.item.value.gateway)
      (beforeService input before completed.item.value.gateway) completed.item.value.source input.zone
      completed.item.value.ingress hit session completed.item.value.produced.actor.nextHop := by
    rw [selected]
    exact ready
  obtain ⟨evidence, emission, computed, emitted, passed, target, _, processing, processingAt, nextHop⟩ :=
    CampusTCPService.run_existing_repeated_enabled (input.contextFor completed.item.value.gateway)
      (beforeService input before completed.item.value.gateway) completed.item.value.source input.zone
      completed.item.value.ingress hit session completed.item.value.produced.actor.nextHop readySelected
  let served : Served input := ⟨before.time, completed.item,
    beforeService input before completed.item.value.gateway, evidence, computed, true⟩
  have route : served.routeMatched = true := by
    simp only [Served.routeMatched, served, processingAt]
    split
    · rfl
    · simp only [nextHop, decide_true]
  have servicePassed : served.passed = true := by
    simp only [Served.passed, served, passed, route, Bool.true_and]
  have primary : (completed.item.value.gateway == .primary && (before.primarySealed || before.primaryFenced)) = false := by
    cases gateway : completed.item.value.gateway with
    | primary => simp [(phaseSelected.1 gateway).1, (phaseSelected.1 gateway).2]
    | standby => rfl
  have standby : (completed.item.value.gateway == .standby && (before.assignmentPaused || before.installation.isNone)) = false := by
    cases gateway : completed.item.value.gateway with
    | primary => rfl
    | standby =>
      have allowed := phaseSelected.2 gateway
      cases installed : before.installation <;> simp_all
  let resident := before.resident completed.item.value.gateway
  let next : Local := { resident with
    transport := ⟨evidence.tracker, evidence.admission⟩
    history := evidence.history resident.history }
  let after : State input := { before.write completed.item.value.gateway next with
    work := completed.state, services := before.services ++ [served] }
  let core : Effect input := { state := after, passed := served.passed, service := some served }
  have coreComputed : processCore input before (.serve item.id none) = .ok core := by
    simp only [processCore, completedAt, Except.mapError, bind, Except.bind, primary, Bool.false_eq_true, ite_false, standby]
    split
    · rename_i reason failed
      rw [computed] at failed
      cases failed
    · rename_i reason failed
      rw [computed] at failed
      cases failed
    · rename_i actual accepted
      have same : actual = evidence := Except.ok.inj (accepted.symm.trans computed)
      subst actual
      rfl
  let effect : Effect input := { core with state := { core.state with
    custody := finishCustody before core before.custody, time := before.time + 1 } }
  have actualComputed : step input before (.serve item.id none) = .ok effect := by
    simp only [step, process, coreComputed, bind, Except.bind, prepareCustody, pure, Except.pure]
    rfl
  let actual : Step input := ⟨before, .serve item.id none, effect, actualComputed⟩
  have serviceAt : actual.result.service = some served := rfl
  obtain ⟨packet, pending, parent, source, bytes⟩ := CampusTCPCustodyFacts.Step.emission_packet actual served serviceAt emission emitted
  obtain ⟨completedActual, completedActualAt, ticketEq, currentAt, work, transport, connection, outputs, receipts⟩ :=
    CampusTCPRoundService.Step.serve_frame actual item.id none rfl served serviceAt
  have actualReady : CampusTCPService.ExistingRepeatedReady (input.contextFor served.ticket.value.gateway)
      served.before served.ticket.value.source input.zone served.ticket.value.ingress hit session
      served.ticket.value.produced.actor.nextHop := readySelected
  have attachment := Processing.repeated_attachment processing actualReady
  have environment := CampusTCPRoundEnvironment.Step.environment actual (by trivial)
  have serviceIndex : actual.result.state.services[report.final.services.length]? = some served := by
    rw [CampusTCPOrigins.service_history actual, serviceAt]
    change (report.final.services ++ [served])[report.final.services.length]? = some served
    simp
  have ticketSelected : served.ticket = item := selected
  refine ⟨actual, served, emission, emitted, rfl, rfl, rfl, servicePassed, serviceAt, selected, ?_, target,
    ?_, ?_, ?_, connection, outputs, receipts, environment, serviceIndex, ⟨packet, pending, parent, source, bytes⟩⟩
  · simpa only [ticketSelected] using currentAt
  · exact ⟨processing, processingAt, by simpa only [selected] using nextHop, attachment⟩
  · exact ⟨completedActual, completedActualAt, ticketEq.symm.trans selected, work⟩
  · simpa only [ticketSelected] using transport

private def networkMove (current : Cut input complete) (actual : Step input)
    (before : actual.before = current.report.final) (supported : actual.result.supported = true)
    (passed : actual.result.passed = true) (event : CampusTCPRoundClock.NetworkAction actual.event) : Move current actual :=
  ⟨current.appendNetwork actual before supported event, before, supported, passed, rfl, rfl⟩

structure AssignmentMove (initial : Initial report complete request) (current : Cut input complete)
    (index : Nat) (ingress : I.InterfaceRef) (produced : Produced input.active input.passive) (actual : Step input) where
  move : Move current actual
  facts : A.AssignmentFacts current.report.final index ingress produced actual
  endpoints : move.after.endpoints = current.endpoints
  gateway : ∀ selected, beforeService input move.after.report.final selected = beforeService input current.report.final selected
  environment : CampusTCPRoundEnvironment.environment current.report.final =
    CampusTCPRoundEnvironment.environment move.after.report.final
  anchor : CampusTCPRecoveryRoundPhaseBase.Anchor initial move.after

theorem assign_at (initial : Initial report complete request) (native : NativeEnv initial)
    (current : Cut input complete) (anchor : CampusTCPRecoveryRoundPhaseBase.Anchor initial current)
    (index : Nat) (ingress : I.InterfaceRef) (produced : Produced input.active input.passive)
    (source : current.report.final.outputs[index]? = some produced)
    (pending : IngressPending current.report.final index) :
    ∃ actual : Step input, Nonempty (AssignmentMove initial current index ingress produced actual) := by
  obtain ⟨actual, facts⟩ := CampusTCPRoundAssignment.Report.assign_enabled current.report index ingress produced source
    (native.route_at current.report.final anchor.environment produced.actor) pending
  let move := networkMove current actual facts.beforeEq facts.supported facts.passed (by rw [facts.event]; exact .assign _ _)
  have environment : CampusTCPRoundEnvironment.environment current.report.final =
      CampusTCPRoundEnvironment.environment move.after.report.final := by
    rw [move.final, ← facts.beforeEq]
    exact CampusTCPRoundEnvironment.Step.environment actual (by rw [facts.event]; trivial)
  refine ⟨actual, ⟨⟨move, facts, rfl, ?_, environment,
    ⟨anchor.guards, anchor.retained.trans move.retained, anchor.environment.trans environment⟩⟩⟩⟩
  intro selected
  rw [move.final, ← facts.beforeEq]
  exact CampusTCPRoundLocal.step_service_nonservice actual (by rw [facts.event]; trivial) selected

def AssignmentMove.ticket (_value : AssignmentMove initial current index ingress produced actual) :
    O.Item (Ticket input.active input.passive) := A.ticket current.report.final index ingress produced

theorem AssignmentMove.pending (value : AssignmentMove initial current index ingress produced actual) :
    value.ticket ∈ value.move.after.report.final.work.pending := by
  rw [value.move.final]
  exact value.facts.pending

theorem Step.assign (actual : Step input) (initial : Initial report complete request) (native : NativeEnv initial)
    (current : Cut input complete) (anchor : CampusTCPRecoveryRoundPhaseBase.Anchor initial current)
    (index : Nat) (ingress : I.InterfaceRef) (produced : Produced input.active input.passive)
    (source : current.report.final.outputs[index]? = some produced) (pending : IngressPending current.report.final index)
    (before : actual.before = current.report.final) (event : actual.event = .assign index ingress) :
    Nonempty (AssignmentMove initial current index ingress produced actual) := by
  obtain ⟨enabled, ⟨facts⟩⟩ := assign_at initial native current anchor index ingress produced source pending
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (facts.move.beforeEq.trans before.symm) (facts.facts.event.trans event.symm)
  exact ⟨same ▸ facts⟩

structure ServiceMove (initial : Initial report complete request) (current : Cut input complete)
    (item : O.Item (Ticket input.active input.passive)) (hit : FlowNAT.Hit) (session : TCP.Admission.Session)
    (actual : Step input) (served : Served input)
    (emission : TCP.WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission) where
  move : Move current actual
  facts : S.ServiceFacts current.report.final item hit session actual served emission emitted
  endpoints : move.after.endpoints = current.endpoints
  environment : CampusTCPRoundEnvironment.environment current.report.final =
    CampusTCPRoundEnvironment.environment move.after.report.final
  anchor : CampusTCPRecoveryRoundPhaseBase.Anchor initial move.after

private def serviceMove (anchor : CampusTCPRecoveryRoundPhaseBase.Anchor initial current)
    (facts : S.ServiceFacts current.report.final item hit session actual served emission emitted) :
    ServiceMove initial current item hit session actual served emission emitted := by
  let move := networkMove current actual facts.beforeEq facts.supported facts.passed (by rw [facts.event]; exact .serve _ _)
  have environment : CampusTCPRoundEnvironment.environment current.report.final =
      CampusTCPRoundEnvironment.environment move.after.report.final := by rw [move.final]; exact facts.environment
  exact ⟨move, facts, rfl, environment,
    ⟨anchor.guards, anchor.retained.trans move.retained, anchor.environment.trans environment⟩⟩

theorem serve_at (initial : Initial report complete request) (current : Cut input complete)
    (anchor : CampusTCPRecoveryRoundPhaseBase.Anchor initial current)
    (item : O.Item (Ticket input.active input.passive)) (member : item ∈ current.report.final.work.pending)
    (phase : CampusTCPGatewayEnabled.ServicePhaseReady current.report.final item.value.gateway)
    (hit : FlowNAT.Hit) (session : TCP.Admission.Session)
    (ready : CampusTCPService.ExistingDataReady (input.contextFor item.value.gateway)
      (beforeService input current.report.final item.value.gateway) item.value.source input.zone item.value.ingress
      hit session item.value.produced.actor.nextHop) :
    ∃ actual : Step input, ∃ served : Served input,
      ∃ emission : TCP.WireForwarding.Emission served.ticket.value.source.packet,
      ∃ emitted : served.evidence.output = some emission,
        Nonempty (ServiceMove initial current item hit session actual served emission emitted) := by
  obtain ⟨actual, served, emission, emitted, facts⟩ :=
    CampusTCPRoundService.Report.serve_enabled current.report item member phase hit session ready
  exact ⟨actual, served, emission, emitted, ⟨serviceMove anchor facts⟩⟩

theorem serve_repeated_at (initial : Initial report complete request) (current : Cut input complete)
    (anchor : CampusTCPRecoveryRoundPhaseBase.Anchor initial current)
    (item : O.Item (Ticket input.active input.passive)) (member : item ∈ current.report.final.work.pending)
    (phase : CampusTCPGatewayEnabled.ServicePhaseReady current.report.final item.value.gateway)
    (hit : FlowNAT.Hit) (session : TCP.Admission.Session)
    (ready : CampusTCPService.ExistingRepeatedReady (input.contextFor item.value.gateway)
      (beforeService input current.report.final item.value.gateway) item.value.source input.zone item.value.ingress
      hit session item.value.produced.actor.nextHop) :
    ∃ actual : Step input, ∃ served : Served input,
      ∃ emission : TCP.WireForwarding.Emission served.ticket.value.source.packet,
      ∃ emitted : served.evidence.output = some emission,
        Nonempty (ServiceMove initial current item hit session actual served emission emitted) := by
  obtain ⟨actual, served, emission, emitted, facts⟩ :=
    Report.serve_repeated_enabled current.report item member phase hit session ready
  exact ⟨actual, served, emission, emitted, ⟨serviceMove anchor facts⟩⟩

theorem Step.serve (actual : Step input) (initial : Initial report complete request) (current : Cut input complete)
    (anchor : CampusTCPRecoveryRoundPhaseBase.Anchor initial current)
    (item : O.Item (Ticket input.active input.passive)) (member : item ∈ current.report.final.work.pending)
    (phase : CampusTCPGatewayEnabled.ServicePhaseReady current.report.final item.value.gateway)
    (hit : FlowNAT.Hit) (session : TCP.Admission.Session)
    (ready : CampusTCPService.ExistingDataReady (input.contextFor item.value.gateway)
      (beforeService input current.report.final item.value.gateway) item.value.source input.zone item.value.ingress
      hit session item.value.produced.actor.nextHop)
    (before : actual.before = current.report.final) (event : actual.event = .serve item.id none) :
    ∃ served : Served input, ∃ emission : TCP.WireForwarding.Emission served.ticket.value.source.packet,
      ∃ emitted : served.evidence.output = some emission,
        Nonempty (ServiceMove initial current item hit session actual served emission emitted) := by
  obtain ⟨enabled, served, emission, emitted, ⟨facts⟩⟩ := serve_at initial current anchor item member phase hit session ready
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (facts.move.beforeEq.trans before.symm) (facts.facts.event.trans event.symm)
  subst enabled
  exact ⟨served, emission, emitted, ⟨facts⟩⟩

theorem Step.serve_repeated (actual : Step input) (initial : Initial report complete request) (current : Cut input complete)
    (anchor : CampusTCPRecoveryRoundPhaseBase.Anchor initial current)
    (item : O.Item (Ticket input.active input.passive)) (member : item ∈ current.report.final.work.pending)
    (phase : CampusTCPGatewayEnabled.ServicePhaseReady current.report.final item.value.gateway)
    (hit : FlowNAT.Hit) (session : TCP.Admission.Session)
    (ready : CampusTCPService.ExistingRepeatedReady (input.contextFor item.value.gateway)
      (beforeService input current.report.final item.value.gateway) item.value.source input.zone item.value.ingress
      hit session item.value.produced.actor.nextHop)
    (before : actual.before = current.report.final) (event : actual.event = .serve item.id none) :
    ∃ served : Served input, ∃ emission : TCP.WireForwarding.Emission served.ticket.value.source.packet,
      ∃ emitted : served.evidence.output = some emission,
        Nonempty (ServiceMove initial current item hit session actual served emission emitted) := by
  obtain ⟨enabled, served, emission, emitted, ⟨facts⟩⟩ := serve_repeated_at initial current anchor item member phase hit session ready
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (facts.move.beforeEq.trans before.symm) (facts.facts.event.trans event.symm)
  subst enabled
  exact ⟨served, emission, emitted, ⟨facts⟩⟩

end Netlib.Check.CampusTCPRecoveryRoundNetwork
