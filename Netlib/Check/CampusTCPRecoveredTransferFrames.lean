import Netlib.Check.CampusTCPRecoveryStartupCold
import Netlib.Check.CampusTCPRecoveryStartupTransport
import Netlib.Check.CampusTCPRecoveredTwoWriteEndpoints

/-!
# Empty queues at the recovered transfer boundary

Every cold-prefix packet and ticket retains a recovery producer.
The actual drain and endpoint setup preserve the resulting empty queues.
-/

namespace Netlib.Check.CampusTCPRecoveredTransferFrames

open Protocol.TCP CampusTCPModel CampusTCPRecoveredSetup CampusTCPRecoveredSetupAppend
open CampusTCPRecoveryStartupCold

variable {input : Input} {events : List Event} {report : Report input events}
variable {ready : DrainReady report} {archive : RecoveryArchive input.active input.passive}
variable {bytes : List UInt8}

theorem Report.output_recovery (report : Report input events) (cold : ColdProfile report)
    (produced : Produced input.active input.passive) (member : produced ∈ report.final.outputs) :
    produced.isRecovery = true := by
  obtain ⟨actual, present, recorded, _, _⟩ := CampusTCPOrigins.Report.outputs_origin report produced member
  exact CampusTCPRecoveryStartupCold.Report.recovery_outputs report cold actual present produced recorded

theorem Report.pending_recovery (report : Report input events) (cold : ColdProfile report)
    (item : Work.Item (Ticket input.active input.passive)) (member : item ∈ report.final.work.pending) :
    item.value.produced.isRecovery = true := by
  obtain ⟨assignment, index, ingress, produced, assignedMember, _, lookup, itemEq, _⟩ :=
    CampusTCPOrigins.Report.pending_origin report item member
  obtain ⟨prior, later, history, preceding, _, _⟩ := CampusTCPFacts.step_origin report assignment assignedMember
  let beforeReport : Report input (prior.map (·.event)) := ⟨assignment.before, prior, [], preceding⟩
  obtain ⟨producer, present, recorded, _, _⟩ :=
    CampusTCPOrigins.Report.outputs_origin beforeReport produced (List.mem_of_getElem? lookup)
  have producerMember : producer ∈ report.steps := by
    rw [history]
    exact List.mem_append_left _ present
  have recovery := CampusTCPRecoveryStartupCold.Report.recovery_outputs report cold producer producerMember produced recorded
  simpa only [itemEq, Theory.Outstanding.newItem] using recovery

theorem Report.packet_recovery (report : Report input events) (cold : ColdProfile report)
    (item : Theory.PacketCustody.Item (Transit input)) (member : item ∈ report.final.custody.pending) :
    item.value.payload.isRecovery = true := by
  have source := CampusTCPCustodyFacts.Report.sources report item (List.mem_append_right _ member)
  cases packet : item.value.payload with
  | ingress index produced =>
    rw [packet] at source
    change report.final.outputs[index]? = some produced at source
    exact Report.output_recovery report cold produced (List.mem_of_getElem? source)
  | link index served emission emitted =>
    rw [packet] at source
    change report.final.services[index]? = some served at source
    exact CampusTCPRecoveryStartupCold.Report.recovery_services report cold served (List.mem_of_getElem? source)

theorem DrainReady.work_empty (ready : DrainReady report) (cold : ColdProfile report) :
    report.final.work.pending = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro item member
  have recovery := Report.pending_recovery report cold item member
  have none := List.any_eq_false.mp ready.tickets item member
  rw [recovery] at none
  exact none rfl

theorem DrainReady.packets_empty (ready : DrainReady report) (cold : ColdProfile report) :
    report.final.custody.pending = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro item member
  have recovery := Report.packet_recovery report cold item member
  have none := List.any_eq_false.mp ready.packets item member
  rw [recovery] at none
  exact none rfl

private def SetupEvent : Event → Prop
  | .finishStartup | .enableStartupRecovery .. | .enableAck .. | .write .. => True
  | _ => False

private def QuietWork (before : State input) (effect : Effect input) : Prop :=
  effect.state.work = before.work ∧ effect.service = none

private theorem application_work (computed : applyApplication input before actor event = .ok effect) :
    QuietWork before effect := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; exact ⟨rfl, rfl⟩)
    | cases computed
    | split at computed
    | dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed

private theorem handoff_work (computed : enableStartupRecovery input before actor = .ok effect) :
    QuietWork before effect := by
  unfold enableStartupRecovery at computed
  split at computed
  · cases computed; exact ⟨rfl, rfl⟩
  · exact application_work computed

private theorem ack_work (computed : enableAck input before actor = .ok effect) : QuietWork before effect := by
  unfold enableAck at computed
  repeat' first
    | (solve | exact application_work computed)
    | cases computed
    | split at computed
    | dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed

private theorem finish_work (computed : finishStartup input before = .ok effect) :
    QuietWork before effect ∧ effect.output = none := by
  unfold finishStartup at computed
  repeat' first
    | (solve | cases computed; exact ⟨⟨rfl, rfl⟩, rfl⟩)
    | cases computed
    | split at computed
    | dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed

private theorem setup_work (computed : processCore input before event = .ok effect) (selected : SetupEvent event) :
    QuietWork before effect := by
  cases event with
  | finishStartup => exact (finish_work computed).1
  | enableStartupRecovery actor => exact handoff_work computed
  | enableAck actor => exact ack_work computed
  | write actor bytes => exact application_work computed
  | _ => cases selected

private theorem setup_frames (actual : Step input) (selected : SetupEvent actual.event)
    (quiet : actual.result.output = none) :
    actual.result.state.work = actual.before.work ∧ actual.result.state.custody = actual.before.custody := by
  obtain ⟨effect, custody, computed, prepared, final⟩ := actual.transaction
  have work := setup_work computed selected
  have stored : custody = actual.before.custody := by
    cases event : actual.event <;> simp only [event, SetupEvent] at selected <;> try cases selected
    all_goals simpa only [prepareCustody, event, pure, Except.pure, Except.ok.injEq] using prepared.symm
  have output : effect.output = none := by simpa only [final] using quiet
  rw [final, stored]
  exact ⟨work.1, by simp only [finishCustody, output, work.2]⟩

private theorem QuietAppend.queue_frames {prior : Prefix input events archive}
    (value : QuietAppend prior actor event joint result) (selected : SetupEvent joint) :
    value.next.report.final.work = prior.report.final.work ∧
      value.next.report.final.custody = prior.report.final.custody := by
  rw [value.final, ← value.before]
  exact setup_frames value.actual (by rw [value.eventEq]; exact selected) value.quiet

theorem Drained.queue_frames (drained : Drained ready archive) :
    drained.next.report.final.work = report.final.work ∧ drained.next.report.final.custody = report.final.custody := by
  have quiet : drained.actual.result.output = none := by
    obtain ⟨effect, custody, computed, final⟩ := drained.actual.processed
    rw [drained.event] at computed
    simpa only [final] using (finish_work computed).2
  rw [drained.final, ← drained.before]
  exact setup_frames drained.actual (by rw [drained.event]; trivial) quiet

theorem Prepared.queue_frames {start : Prefix input events archive} (value : Prepared start bytes) :
    value.next.report.final.work = start.report.final.work ∧
      value.next.report.final.custody = start.report.final.custody := by
  have first := QuietAppend.queue_frames value.clientRecovery trivial
  have second := QuietAppend.queue_frames value.serverRecovery trivial
  have third := QuietAppend.queue_frames value.clientAck trivial
  have fourth := QuietAppend.queue_frames value.serverAck trivial
  have fifth := QuietAppend.queue_frames value.written trivial
  exact ⟨fifth.1.trans (fourth.1.trans (third.1.trans (second.1.trans first.1))),
    fifth.2.trans (fourth.2.trans (third.2.trans (second.2.trans first.2)))⟩

theorem Prepared.work_empty (drained : Drained ready archive) (value : Prepared drained.next bytes)
    (cold : ColdProfile report) : value.next.report.final.work.pending = [] := by
  rw [(Prepared.queue_frames value).1, (Drained.queue_frames drained).1]
  exact DrainReady.work_empty ready cold

theorem Prepared.packets_empty (drained : Drained ready archive) (value : Prepared drained.next bytes)
    (cold : ColdProfile report) : value.next.report.final.custody.pending = [] := by
  rw [(Prepared.queue_frames value).2, (Drained.queue_frames drained).2]
  exact DrainReady.packets_empty ready cold

theorem Prepared.outstanding_empty (drained : Drained ready archive) (value : Prepared drained.next bytes)
    (cold : ColdProfile report) (gateway : Gateway) : value.next.report.final.outstanding gateway = 0 := by
  simp only [State.outstanding, Prepared.work_empty drained value cold, List.filter_nil, List.length_nil]

theorem Prepared.primary_empty (drained : Drained ready archive) (value : Prepared drained.next bytes)
    (cold : ColdProfile report) : (CampusTCPRecoveredTwoWriteEndpoints.cut value).report.final.outstanding .primary = 0 :=
  Prepared.outstanding_empty drained value cold .primary

private theorem install_standby {id : String} (computed : installConfiguration input before gateway id = .ok effect) :
    effect.state.standby.transport = before.standby.transport := by
  unfold installConfiguration at computed
  repeat' first
    | (solve | cases computed; cases gateway <;> rfl)
    | cases computed
    | split at computed
    | dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
        throw, throwThe, MonadExceptOf.throw] at computed

private theorem stage_standby {id : String} (computed : stageAttachment input before gateway id = .ok effect) :
    effect.state.standby.transport = before.standby.transport := by
  unfold stageAttachment at computed
  repeat' first
    | (solve | cases computed; cases gateway <;> rfl)
    | cases computed
    | split at computed
    | dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure,
        throw, throwThe, MonadExceptOf.throw] at computed

private theorem guard_standby {id : String} (computed : installIngress input before gateway id = .ok effect) :
    effect.state.standby.transport = before.standby.transport := by
  unfold installIngress at computed
  repeat' first
    | (solve | cases computed; cases gateway <;> rfl)
    | cases computed
    | split at computed
    | dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
        throw, throwThe, MonadExceptOf.throw] at computed

private theorem write_primary_standby (before : State input) (gateway : Gateway) (resident : Local)
    (selected : gateway = .primary) : (before.write gateway resident).standby.transport = before.standby.transport := by
  cases gateway
  · rfl
  · cases selected

private theorem serve_standby {ticket : Nat} (computed : processCore input before (.serve ticket observed) = .ok effect)
    (primary : ∀ served, effect.service = some served → served.ticket.value.gateway = .primary) :
    effect.state.standby.transport = before.standby.transport := by
  simp only [processCore] at computed
  repeat' first
    | (solve | cases computed; rfl)
    | cases computed
    | split at computed
    | dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure,
        throw, throwThe, MonadExceptOf.throw] at computed
  have atPrimary := primary _ rfl
  dsimp only at atPrimary ⊢
  exact write_primary_standby before _ _ atPrimary

theorem Step.cold_standby (actual : Step input) (cold : ColdEvent actual.event)
    (primary : ∀ served, actual.result.service = some served → served.ticket.value.gateway = .primary) :
    actual.result.state.standby.transport = actual.before.standby.transport := by
  by_cases quiet : CampusTCPRoundEnvironment.Nonservice actual.event
  · exact congrArg Local.transport (CampusTCPRoundEnvironment.Step.resident_nonservice actual quiet .standby)
  obtain ⟨effect, custody, computed, final⟩ := actual.processed
  have selected : ∀ served, effect.service = some served → served.ticket.value.gateway = .primary := by
    intro served present
    exact primary served (by simpa only [final] using present)
  have frame : effect.state.standby.transport = actual.before.standby.transport := by
    cases event : actual.event with
    | authentication index =>
      rw [event] at computed
      simp only [processCore] at computed
      repeat' first
        | (solve | cases computed; rfl)
        | cases computed
        | split at computed
        | dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed
    | install id | installAt gateway id => rw [event] at computed; exact install_standby computed
    | stage id | stageAt gateway id => rw [event] at computed; exact stage_standby computed
    | installGuard id | installGuardAt gateway id => rw [event] at computed; exact guard_standby computed
    | serve id observed => rw [event] at computed; exact serve_standby computed selected
    | _ => simp only [event, ColdEvent, CampusTCPRoundEnvironment.Nonservice, not_true_eq_false] at cold quiet
  simpa only [final] using frame

theorem Trace.cold_standby (trace : Trace input initial selected steps final remaining)
    (cold : ∀ actual ∈ steps, ColdEvent actual.event)
    (primary : ∀ served ∈ steps.filterMap (·.result.service), served.ticket.value.gateway = .primary) :
    final.standby.transport = initial.standby.transport := by
  induction trace with
  | done state => rfl
  | stop head blocked rest =>
    exact Step.cold_standby head (cold head (by simp)) (fun served present =>
      primary served (List.mem_filterMap.mpr ⟨head, by simp, present⟩))
  | next head supported rest ih =>
    have before := Step.cold_standby head (cold head (by simp)) (fun served present =>
      primary served (List.mem_filterMap.mpr ⟨head, by simp, present⟩))
    have after := ih (fun actual member => cold actual (List.mem_cons_of_mem _ member))
      (fun served member => primary served (by
        obtain ⟨actual, inside, present⟩ := List.mem_filterMap.mp member
        exact List.mem_filterMap.mpr ⟨actual, List.mem_cons_of_mem _ inside, present⟩))
    exact after.trans before

theorem Report.standby_initial (report : Report input events) (cold : ColdProfile report)
    (primary : CampusTCPRecoveryStartupTransport.PrimaryServices report) :
    report.final.standby.transport = Checkpoint.Gateway.initial := by
  simpa only [Input.initial, Local.initial] using Trace.cold_standby report.trace cold primary

theorem Prepared.standby_initial (drained : Drained ready archive) (value : Prepared drained.next bytes)
    (cold : ColdProfile report) (primary : CampusTCPRecoveryStartupTransport.PrimaryServices report) :
    value.next.report.final.standby.transport = Checkpoint.Gateway.initial := by
  have same := (Prepared.gateway_frame value .standby).trans (Drained.gateway_frame drained .standby)
  have transport := congrArg (fun before : CampusTCPService.Before => (⟨before.tracker, before.admission⟩ : Checkpoint.Gateway)) same
  change value.next.report.final.standby.transport = report.final.standby.transport at transport
  exact transport.trans (Report.standby_initial report cold primary)

end Netlib.Check.CampusTCPRecoveredTransferFrames
