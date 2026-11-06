import Netlib.Check.CampusTCPFacts

/-!
# Primary transport from actual gateway services

Only primary packet service changes the primary tracker and admission state.
The stored service order determines that state at each actual cut.
-/

namespace Netlib.Check.CampusTCPPrimaryTransport

open CampusTCPModel

def afterService (prior : Protocol.TCP.Checkpoint.Gateway) (served : Served input) :
    Protocol.TCP.Checkpoint.Gateway :=
  match served.ticket.value.gateway with
  | .primary => ⟨served.evidence.tracker, served.evidence.admission⟩
  | .standby => prior

def serviceTransport (initial : Protocol.TCP.Checkpoint.Gateway) (services : List (Served input)) :
    Protocol.TCP.Checkpoint.Gateway := services.foldl afterService initial

private def NoService (before : State input) (effect : Effect input) : Prop :=
  effect.state.primary.transport = before.primary.transport ∧ effect.service = none

private theorem no_service_transport (before : State input) (effect : Effect input) (quiet : NoService before effect) :
    effect.state.primary.transport = serviceTransport before.primary.transport effect.service.toList := by
  rw [quiet.2]
  exact quiet.1

private theorem startup_noService (before : State input) (event : Check.TCPHandshake.Event) (effect : Effect input)
    (computed : startup input before event = .ok effect) : NoService before effect := by
  unfold startup at computed
  repeat' first
    | (solve | cases computed; exact ⟨rfl, rfl⟩)
    | (cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem application_noService (before : State input) (actor : Actor) (event : T.Event) (effect : Effect input)
    (computed : applyApplication input before actor event = .ok effect) : NoService before effect := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; exact ⟨rfl, rfl⟩)
    | (cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

private theorem enableAck_noService (before : State input) (actor : Actor) (effect : Effect input)
    (computed : enableAck input before actor = .ok effect) : NoService before effect := by
  unfold enableAck at computed
  split at computed
  · exact application_noService _ _ _ _ computed
  · cases actor <;> dsimp only at computed
    all_goals
      split at computed
      · exact application_noService _ _ _ _ computed
      · cases computed

private theorem install_noService (before : State input) (gateway : Gateway) (id : String) (effect : Effect input)
    (computed : installConfiguration input before gateway id = .ok effect) : NoService before effect := by
  unfold installConfiguration at computed
  repeat' first
    | (solve | cases computed; cases gateway <;> exact ⟨rfl, rfl⟩)
    | (cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
        throw, throwThe, MonadExceptOf.throw] at computed)

private theorem stage_noService (before : State input) (gateway : Gateway) (id : String) (effect : Effect input)
    (computed : stageAttachment input before gateway id = .ok effect) : NoService before effect := by
  unfold stageAttachment at computed
  repeat' first
    | (solve | cases computed; cases gateway <;> exact ⟨rfl, rfl⟩)
    | (cases computed)
    | (split at computed)
    | (dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure,
        throw, throwThe, MonadExceptOf.throw] at computed)

private theorem ingress_noService (before : State input) (gateway : Gateway) (id : String) (effect : Effect input)
    (computed : installIngress input before gateway id = .ok effect) : NoService before effect := by
  unfold installIngress at computed
  repeat' first
    | (solve | cases computed; cases gateway <;> exact ⟨rfl, rfl⟩)
    | (cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
        throw, throwThe, MonadExceptOf.throw] at computed)

private theorem transfer_noService (before : State input) (event : Event) (effect : Effect input)
    (computed : transferControl input before event = .ok effect) : NoService before effect := by
  unfold transferControl at computed
  repeat' first
    | (solve | cases computed; exact ⟨rfl, rfl⟩)
    | (cases computed)
    | (split at computed)
    | (dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure,
        throw, throwThe, MonadExceptOf.throw] at computed)

private theorem service_write (before : State input) (gateway : Gateway)
    (tracker : Protocol.ConntrackLifecycle.State) (admission : Protocol.TCP.Admission.State)
    (history : Protocol.TCP.Checkpoint.History ⟨tracker, admission⟩) :
    (before.write gateway { before.resident gateway with transport := ⟨tracker, admission⟩, history }).primary.transport =
      match gateway with | .primary => ⟨tracker, admission⟩ | .standby => before.primary.transport := by
  cases gateway <;> rfl

private theorem process_transport (before : State input) (event : Event) (effect : Effect input)
    (computed : processCore input before event = .ok effect) :
    effect.state.primary.transport = serviceTransport before.primary.transport effect.service.toList := by
  cases event with
  | «open» remote policy => exact no_service_transport _ _ (startup_noService _ _ _ computed)
  | write actor bytes | send actor bytes policy | read actor bytes | emitAck actor policy =>
    exact no_service_transport _ _ (application_noService _ _ _ _ computed)
  | enableRecovery actor | advanceClock actor millis | timeout actor policy | dispatchAck actor policy =>
    exact no_service_transport _ _ (application_noService _ _ _ _ computed)
  | enableAck actor => exact no_service_transport _ _ (enableAck_noService _ _ _ computed)
  | copyPacket id | dropPacket id => cases computed; rfl
  | install id => exact no_service_transport _ _ (install_noService _ _ _ _ computed)
  | installAt gateway id => exact no_service_transport _ _ (install_noService _ _ _ _ computed)
  | stage id => exact no_service_transport _ _ (stage_noService _ _ _ _ computed)
  | stageAt gateway id => exact no_service_transport _ _ (stage_noService _ _ _ _ computed)
  | installGuard id => exact no_service_transport _ _ (ingress_noService _ _ _ _ computed)
  | installGuardAt gateway id => exact no_service_transport _ _ (ingress_noService _ _ _ _ computed)
  | pause | stageCheckpoint | installCheckpoint ns | switchRoute actor gateway | fencePrimary | resume =>
    simp only [processCore] at computed
    exact no_service_transport _ _ (transfer_noService _ _ _ computed)
  | authentication index | assign index ingress =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed; rfl)
      | (cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)
  | serve index observed =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed; rfl)
      | (solve | cases computed; exact service_write before _ _ _ _)
      | (cases computed)
      | (split at computed)
      | (dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)
  | deliver index bytes policy =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed; apply no_service_transport; simpa only [NoService] using startup_noService before _ _ (by assumption))
      | (solve | cases computed; apply no_service_transport; simpa only [NoService] using application_noService before _ _ _ (by assumption))
      | (cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)

theorem Step.primary_transport (actual : Step input) :
    actual.result.state.primary.transport = serviceTransport actual.before.primary.transport actual.result.service.toList := by
  obtain ⟨effect, custody, computed, same⟩ := actual.processed
  have updated := process_transport actual.before actual.event effect computed
  simpa only [same] using updated

theorem Trace.primary_transport (trace : Trace input initial events steps final remaining) :
    final.primary.transport = serviceTransport initial.primary.transport (steps.filterMap (·.result.service)) := by
  induction trace with
  | done state => rfl
  | stop head blocked tail =>
    have updated := Step.primary_transport head
    cases selected : head.result.service <;>
      simpa only [List.filterMap_cons, List.filterMap_nil, selected, Option.toList, serviceTransport, List.foldl_cons,
        List.foldl_nil] using updated
  | next head supported rest ih =>
    rw [ih, Step.primary_transport head]
    cases selected : head.result.service <;>
      simp only [selected, List.filterMap_cons, serviceTransport, Option.toList, List.foldl_cons, List.foldl_nil]

theorem Trace.services (trace : Trace input initial events steps final remaining) :
    final.services = initial.services ++ steps.filterMap (·.result.service) := by
  induction trace with
  | done state => simp
  | stop head blocked tail =>
    rw [CampusTCPOrigins.service_history head]
    cases selected : head.result.service <;> simp [selected]
  | next head supported rest ih =>
    rw [ih, CampusTCPOrigins.service_history head]
    cases selected : head.result.service <;> simp [selected, List.append_assoc]

theorem Report.primary_transport (report : Report input events) :
    report.final.primary.transport = serviceTransport .initial (report.steps.filterMap (·.result.service)) :=
  Trace.primary_transport report.trace

theorem Report.services (report : Report input events) :
    report.final.services = report.steps.filterMap (·.result.service) :=
  Trace.services report.trace

theorem Report.before_service (report : Report input events) (joint : Step input) (member : joint ∈ report.steps)
    (served : Served input) (recorded : joint.result.service = some served) :
    ∃ priorServices laterServices, report.steps.filterMap (·.result.service) = priorServices ++ served :: laterServices ∧
      joint.before.primary.transport = serviceTransport .initial priorServices := by
  obtain ⟨prior, later, steps, preceding, _, _⟩ := CampusTCPFacts.step_origin report joint member
  refine ⟨prior.filterMap (fun actual : Step input => actual.result.service),
    later.filterMap (fun actual : Step input => actual.result.service), ?_, ?_⟩
  · simp only [steps, List.filterMap_append, List.filterMap_cons, recorded]
  · simpa only [Input.initial, Local.initial] using Trace.primary_transport preceding

end Netlib.Check.CampusTCPPrimaryTransport
