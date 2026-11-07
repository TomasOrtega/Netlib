import Netlib.Check.CampusTCPCustodyFacts
import Netlib.Check.CampusTCPServiceEnabled
import Netlib.Check.CampusTCPStartupServiceEnabled

/-!
# Campus gateway service from pending work

The selected ticket is actual pending work.
Its current gateway and packet conditions derive service and packet custody.
-/

namespace Netlib.Check.CampusTCPGatewayEnabled

open CampusTCPModel

variable {input : Input}

def ServicePhaseReady (before : State input) (gateway : Gateway) : Prop :=
  (gateway = .primary → before.primarySealed = false ∧ before.primaryFenced = false) ∧
    (gateway = .standby → before.assignmentPaused = false ∧ before.installation.isSome = true)

private def existingData_admission (ready : CampusTCPService.ExistingDataReady context before source zone ingress hit session hop)
    (mode : Protocol.TCP.AdmissionExecution.Mode) :
    CampusTCPService.ExistingAdmissionReady context before source zone ingress hit hop mode := by
  refine ⟨ready.checks, ready.budget, ready.ingressPermit, ready.tracker, ?_, ready.ttl,
    ready.forwardComparison, ready.guardComparison, ready.covered⟩
  intro record member same
  have allowed : Protocol.TCP.Admission.Allowed before.admission.phase
      (Protocol.ConntrackLifecycle.selectedAttachment record hit.direction) source.packet.segment before.admission.observations := by
    rw [ready.phase]
    exact Protocol.TCP.Admission.DataReady.allowed session _ source.packet.segment before.admission.observations
      (ready.binding record member same) rfl ready.data
  cases mode with
  | ordinary => exact allowed
  | startupRecovery => exact Or.inl allowed

theorem serve_enabled (before : State input) (item : Theory.Outstanding.Item (Ticket input.active input.passive))
    (valid : before.work.Valid) (member : item ∈ before.work.pending)
    (phase : ServicePhaseReady before item.value.gateway)
    (hit : Protocol.FlowNAT.Hit) (session : Protocol.TCP.Admission.Session)
    (ready : CampusTCPService.ExistingDataReady (input.contextFor item.value.gateway)
      (beforeService input before item.value.gateway) item.value.source input.zone item.value.ingress
      hit session item.value.produced.actor.nextHop) :
    ∃ actual : Step input, actual.before = before ∧ actual.event = .serve item.id none ∧
      actual.result.supported = true ∧ actual.result.passed = true ∧
      ∃ served, actual.result.service = some served ∧ served.ticket = item ∧
      ∃ emission, ∃ emitted : served.evidence.output = some emission,
      ∃ packet ∈ actual.result.state.custody.pending,
        packet.value.parent = none ∧
        packet.value.payload = .link before.services.length served emission emitted ∧
        packet.value.payload.bytes = emission.bytes := by
  obtain ⟨completed, completedAt, selected⟩ := Theory.Outstanding.complete_item before.work item valid member
  have phaseSelected : ServicePhaseReady before completed.item.value.gateway := by rw [selected]; exact phase
  have readySelected : CampusTCPService.ExistingDataReady (input.contextFor completed.item.value.gateway)
      (beforeService input before completed.item.value.gateway) completed.item.value.source input.zone
      completed.item.value.ingress hit session completed.item.value.produced.actor.nextHop := by
    rw [selected]
    exact ready
  obtain ⟨evidence, emission, computed, emitted, passed, _, _, processing, processingAt, nextHop⟩ :=
    CampusTCPService.run_existing_admission_enabled (input.contextFor completed.item.value.gateway)
      (beforeService input before completed.item.value.gateway) completed.item.value.source input.zone
      completed.item.value.ingress hit completed.item.value.produced.actor.nextHop
      (existingData_admission readySelected before.connection.admissionMode)
  let served : Served input := ⟨before.time, completed.item,
    beforeService input before completed.item.value.gateway, before.connection.admissionMode, evidence, computed, true⟩
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
  exact ⟨actual, rfl, rfl, rfl, servicePassed, served, serviceAt, selected,
    emission, emitted, packet, pending, parent, source, bytes⟩

theorem Report.serve_enabled (report : Report input events)
    (item : Theory.Outstanding.Item (Ticket input.active input.passive))
    (member : item ∈ report.final.work.pending)
    (phase : ServicePhaseReady report.final item.value.gateway)
    (hit : Protocol.FlowNAT.Hit) (session : Protocol.TCP.Admission.Session)
    (ready : CampusTCPService.ExistingDataReady (input.contextFor item.value.gateway)
      (beforeService input report.final item.value.gateway) item.value.source input.zone item.value.ingress
      hit session item.value.produced.actor.nextHop) :
    ∃ actual : Step input, actual.before = report.final ∧ actual.event = .serve item.id none ∧
      actual.result.supported = true ∧ actual.result.passed = true ∧
      ∃ served, actual.result.service = some served ∧ served.ticket = item ∧
      ∃ emission, ∃ emitted : served.evidence.output = some emission,
      ∃ packet ∈ actual.result.state.custody.pending,
        packet.value.parent = none ∧
        packet.value.payload = .link report.final.services.length served emission emitted ∧
        packet.value.payload.bytes = emission.bytes :=
  CampusTCPGatewayEnabled.serve_enabled report.final item (CampusTCPOrigins.Report.work_valid report)
    member phase hit session ready

end Netlib.Check.CampusTCPGatewayEnabled
