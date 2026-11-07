import Netlib.Check.CampusTCPRecoveryStartupServiceFull
import Netlib.Check.CampusTCPStartupControlFrames
import Netlib.Check.CampusTCPStartupTicketIngress

/-!
# Actual campus service for a current startup ticket

The same pending work item selects the native service and fresh link packet.
Raw ingress and next-hop equalities describe the installed paths.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupServiceEnabled

open Packet Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupCurrentNative (Current gatewayBefore)
open CampusTCPRecoveryStartupPhase (sideDirection)

variable {input : Input} {baseEvents events : List CampusTCPModel.Event}
variable {base : Report input baseEvents} {report : Report input events}
variable {current : C.State input.active input.passive} {header : Header}
variable {profile : CampusTCPStartupNative.Profile (input.contextFor .primary) (beforeService input base.final .primary) input.zone header}

structure PathsAligned (config : CampusTCPStartupTransferMonitor.Config)
    (profile : CampusTCPStartupNative.Profile context before zone header) : Prop where
  ingress : ∀ side, (profile.paths (sideDirection side)).ingress = config.transfer.ingress .primary (Actor.ofRecovery side)
  hop : ∀ side, (profile.paths (sideDirection side)).hop = (Actor.ofRecovery side).nextHop

structure Service (report : Report input events) (item : Work.Item (Ticket input.active input.passive)) (actual : Step input) where
  before : actual.before = report.final
  event : actual.event = .serve item.id none
  supported : actual.result.supported = true
  passed : actual.result.passed = true
  served : Served input
  recorded : actual.result.service = some served
  ticket : served.ticket = item
  primary : served.ticket.value.gateway = .primary
  mode : served.mode = .startupRecovery
  emission : W.Emission served.ticket.value.source.packet
  emitted : served.evidence.output = some emission
  packet : Theory.PacketCustody.Item (Transit input)
  pending : packet ∈ actual.result.state.custody.pending
  packetID : packet.id = report.final.custody.nextID
  parent : packet.value.parent = none
  payload : packet.value.payload = .link report.final.services.length served emission emitted
  services : actual.result.state.services = report.final.services ++ [served]
  outputs : actual.result.state.outputs = report.final.outputs
  connection : actual.result.state.connection = report.final.connection
  environment : CampusTCPRoundEnvironment.environment report.final = CampusTCPRoundEnvironment.environment actual.result.state
  completed : Work.Completed report.final.work item.id
  completeComputed : Work.complete report.final.work item.id = .ok completed
  selected : completed.item = item
  work : actual.result.state.work = completed.state

private theorem serve_current (value : Current base profile report current)
    (item : Work.Item (Ticket input.active input.passive)) (source : CampusTCPStartupJobs.Source input)
    (production : item.value.produced = source.produced) (pending : item ∈ report.final.work.pending)
    (ingress : item.value.ingress = (profile.paths (sideDirection source.occurrence.actor)).ingress)
    (hop : (profile.paths (sideDirection source.occurrence.actor)).hop = item.value.produced.actor.nextHop) :
    ∃ actual, Nonempty (Service report item actual) := by
  have gateway := CampusTCPStartupPrimaryServices.Report.pending_primary report value.cold item pending
  have physical := CampusTCPStartupControlFrames.Report.control_fields report value.cold
  have mode : report.final.connection.admissionMode = .startupRecovery := by rw [value.connected]; rfl
  obtain ⟨completed, completedAt, selected⟩ := Theory.Outstanding.complete_item report.final.work item
    (CampusTCPOrigins.Report.work_valid report) pending
  have wire : item.value.source = source.produced.source := congrArg Produced.source production
  have enabled : ∃ evidence emission,
      CampusTCPService.run (input.contextFor completed.item.value.gateway)
        (beforeService input report.final completed.item.value.gateway) completed.item.value.source input.zone
        completed.item.value.ingress 100000 report.final.connection.admissionMode = .ok evidence ∧
      evidence.output = some emission ∧ evidence.passed = true ∧
      ∃ processing, evidence.processing = some processing ∧
        processing.outcome.nextHop = some completed.item.value.produced.actor.nextHop := by
    rw [selected, gateway, wire, ingress, mode]
    obtain ⟨evidence, emission, computed, emitted, passed, _, processing, processingAt, nextHop⟩ :=
      CampusTCPRecoveryStartupServiceFull.Current.job_service_full_enabled value
        (.ticket item source production) pending
    exact ⟨evidence, emission, computed, emitted, passed, processing, processingAt, nextHop.trans (congrArg some hop)⟩
  obtain ⟨evidence, emission, computed, emitted, passed, processing, processingAt, nextHop⟩ := enabled
  let served : Served input := ⟨report.final.time, completed.item,
    beforeService input report.final completed.item.value.gateway, report.final.connection.admissionMode, evidence, computed, true⟩
  have route : served.routeMatched = true := by
    simp only [Served.routeMatched, served, processingAt]
    split
    · rfl
    · simp only [nextHop, decide_true]
  have servicePassed : served.passed = true := by
    simp only [Served.passed, served, passed, route, Bool.true_and]
  have primary : (completed.item.value.gateway == .primary &&
      (report.final.primarySealed || report.final.primaryFenced)) = false := by
    rw [selected, gateway, physical.2.1, physical.2.2.1]
    rfl
  have standby : (completed.item.value.gateway == .standby &&
      (report.final.assignmentPaused || report.final.installation.isNone)) = false := by
    rw [selected, gateway]
    rfl
  let resident := report.final.resident completed.item.value.gateway
  let next : Local := { resident with transport := ⟨evidence.tracker, evidence.admission⟩, history := evidence.history resident.history }
  let after : State input := { report.final.write completed.item.value.gateway next with
    work := completed.state, services := report.final.services ++ [served] }
  let core : Effect input := { state := after, passed := served.passed, service := some served }
  have coreComputed : processCore input report.final (.serve item.id none) = .ok core := by
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
    custody := finishCustody report.final core report.final.custody, time := report.final.time + 1 } }
  have actualComputed : step input report.final (.serve item.id none) = .ok effect := by
    simp only [step, process, coreComputed, bind, Except.bind, prepareCustody, pure, Except.pure]
    rfl
  let actual : Step input := ⟨report.final, .serve item.id none, effect, actualComputed⟩
  let packet : Theory.PacketCustody.Item (Transit input) :=
    Theory.PacketCustody.newItem report.final.custody (.link report.final.services.length served emission emitted)
  have packetPending : packet ∈ actual.result.state.custody.pending := by
    change packet ∈ (finishCustody report.final core report.final.custody).pending
    have servedEmitted : served.evidence.output = some emission := emitted
    simp only [finishCustody, core]
    split
    · rename_i absent
      rw [servedEmitted] at absent
      cases absent
    · rename_i output outputAt
      have same : output = emission := Option.some.inj (outputAt.symm.trans servedEmitted)
      subst output
      exact List.mem_append_right _ (List.mem_singleton_self _)
  have serviceAt : actual.result.service = some served := rfl
  have services : actual.result.state.services = report.final.services ++ [served] := by
    simpa only [serviceAt, Option.toList_some] using CampusTCPOrigins.service_history actual
  have outputs : actual.result.state.outputs = report.final.outputs := by
    have output : actual.result.output = none := rfl
    simpa only [output, Option.toList_none, List.append_nil] using CampusTCPOrigins.output_history actual
  have connection : actual.result.state.connection = report.final.connection := by
    change (report.final.write completed.item.value.gateway next).connection = report.final.connection
    cases completed.item.value.gateway <;> rfl
  have environment := CampusTCPRoundEnvironment.Step.environment actual (by trivial)
  refine ⟨actual, ⟨⟨rfl, rfl, rfl, servicePassed, served, serviceAt, selected, ?_, mode,
    emission, emitted, packet, packetPending, rfl, rfl, rfl, services, outputs, connection,
    environment, completed, completedAt, selected, ?_⟩⟩⟩
  · change completed.item.value.gateway = .primary
    rw [selected]
    exact gateway
  · rfl


def Service.on_step (value : Service report item actual) (supplied : Step input)
    (before : supplied.before = report.final) (event : supplied.event = .serve item.id none) :
    Service report item supplied := by
  have computed := actual.computed
  rw [value.before.trans before.symm, value.event.trans event.symm, supplied.computed] at computed
  have result : actual.result = supplied.result := (Except.ok.inj computed).symm
  have beforeEq := value.before.trans before.symm
  have eventEq := value.event.trans event.symm
  have same : actual = supplied := by
    cases actual
    cases supplied
    simp_all only
  exact same ▸ value

variable {config : CampusTCPStartupTransferMonitor.Config}

theorem serve_at (whole : Report input wholeEvents) (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : CampusTCPStartupTransferExecution.actions config input.initial (CampusTCPStartupTransferExecution.initial config) whole.steps = true)
    (within : count ≤ whole.steps.length)
    (ending : CampusTCPStartupTransferExecution.monitorAt config (CampusTCPStartupTransferExecution.initial config) whole.steps count = .startup monitor)
    (value : Current base profile (CampusTCPSchedule.Report.cut whole count within) current)
    (paths : PathsAligned config profile)
    (item : Work.Item (Ticket input.active input.passive)) (source : CampusTCPStartupJobs.Source input)
    (production : item.value.produced = source.produced)
    (pending : item ∈ (CampusTCPSchedule.Report.cut whole count within).final.work.pending) :
    ∃ actual, Nonempty (Service (CampusTCPSchedule.Report.cut whole count within) item actual) := by
  have rawIngress := CampusTCPStartupTicketIngress.Report.pending_ingress whole prep actions within ending item pending
  have actor : item.value.produced.actor = Actor.ofRecovery source.occurrence.actor := congrArg Produced.actor production
  have ingress : item.value.ingress = (profile.paths (sideDirection source.occurrence.actor)).ingress := by
    rw [rawIngress, actor, paths.ingress]
  have hop : (profile.paths (sideDirection source.occurrence.actor)).hop = item.value.produced.actor.nextHop := by
    rw [paths.hop, actor]
  exact serve_current value item source production pending ingress hop

end Netlib.Check.CampusTCPRecoveryStartupServiceEnabled
