import Netlib.Check.CampusTCPStartupJobs
import Netlib.Check.CampusTCPOrigins

/-!
# Queue cardinality without packet copies

Assignment and service move one existing job between queues.
Only an actual endpoint output can increase the total.
-/

namespace Netlib.Check.CampusTCPStartupQueueBound

open CampusTCPModel CampusTCPStartupJobs

variable {input : Input}

def queued (state : State input) : Nat := state.custody.pending.length + state.work.pending.length

private def assigned : Event → Nat
  | .assign .. => 1
  | _ => 0

private def Quiet (before : State input) (effect : Effect input) : Prop :=
  effect.state.work = before.work ∧ effect.service = none

private theorem quiet_bound (quiet : Quiet before effect) :
    effect.state.work.pending.length + effect.service.toList.length ≤ before.work.pending.length + assigned event := by
  rw [quiet.1, quiet.2]
  simp only [Option.toList_none, List.length_nil, Nat.add_zero]
  omega

private theorem startup_quiet (computed : startup input before event = .ok effect) : Quiet before effect := by
  unfold startup at computed
  repeat' first
    | (solve | cases computed; exact ⟨rfl, rfl⟩)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [pure, Except.pure] at computed)

private theorem application_quiet (computed : applyApplication input before actor event = .ok effect) : Quiet before effect := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; exact ⟨rfl, rfl⟩)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

private theorem recovery_quiet (computed : runRecovery input before event = .ok effect) : Quiet before effect := by
  unfold runRecovery at computed
  split at computed
  · cases computed; exact ⟨rfl, rfl⟩
  · cases computed; exact ⟨rfl, rfl⟩
  · split at computed
    · cases computed
    · rename_i current connected result evaluated
      cases result with
      | mk state decision output receipt application =>
        cases output <;> simp only [pure, Except.pure, Except.ok.injEq] at computed
        all_goals subst effect; exact ⟨rfl, rfl⟩

private theorem open_quiet (computed : openRecovering input before remote policy = .ok effect) : Quiet before effect := by
  unfold openRecovering at computed
  repeat' first
    | (solve | simpa only [Quiet] using (recovery_quiet computed))
    | (solve | cases computed; exact ⟨rfl, rfl⟩)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem finish_quiet (computed : finishStartup input before = .ok effect) : Quiet before effect := by
  unfold finishStartup at computed
  repeat' first
    | (solve | cases computed; exact ⟨rfl, rfl⟩)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem ack_quiet (computed : enableAck input before actor = .ok effect) : Quiet before effect := by
  unfold enableAck at computed
  repeat' first
    | (solve | exact application_quiet computed)
    | (solve | cases computed; exact ⟨rfl, rfl⟩)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem enable_quiet (computed : enableStartupRecovery input before actor = .ok effect) : Quiet before effect := by
  unfold enableStartupRecovery at computed
  split at computed
  · cases computed; exact ⟨rfl, rfl⟩
  · exact application_quiet computed

private theorem process_work (computed : processCore input before event = .ok effect) :
    effect.state.work.pending.length + effect.service.toList.length ≤ before.work.pending.length + assigned event := by
  cases event with
  | «open» remote policy => exact quiet_bound (startup_quiet computed)
  | openRecovering remote policy => exact quiet_bound (open_quiet computed)
  | startupClock actor millis | startupTimeout actor generation policy => exact quiet_bound (recovery_quiet computed)
  | finishStartup => exact quiet_bound (finish_quiet computed)
  | enableStartupRecovery actor => exact quiet_bound (enable_quiet computed)
  | write actor bytes | send actor count policy | read actor count | emitAck actor policy
  | enableRecovery actor | advanceClock actor millis | timeout actor policy | dispatchAck actor policy =>
    exact quiet_bound (application_quiet computed)
  | enableAck actor => exact quiet_bound (ack_quiet computed)
  | copyPacket id | dropPacket id =>
    cases computed
    exact quiet_bound ⟨rfl, rfl⟩
  | authentication index =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed; exact quiet_bound ⟨rfl, rfl⟩)
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | install id | stage id | installGuard id | installAt gateway id | stageAt gateway id | installGuardAt gateway id =>
    simp only [processCore, installConfiguration, stageAttachment, installIngress] at computed
    repeat' first
      | (solve | cases computed; cases gateway <;> exact quiet_bound ⟨rfl, rfl⟩)
      | (solve | cases computed; exact quiet_bound ⟨rfl, rfl⟩)
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | pause | stageCheckpoint | installCheckpoint ns | switchRoute actor gateway | fencePrimary | resume =>
    simp only [processCore, transferControl] at computed
    repeat' first
      | (solve | cases computed; exact quiet_bound ⟨rfl, rfl⟩)
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | assign index ingress =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed; simp only [assigned, Work.enqueue, Option.toList_none,
          List.length_nil, List.length_append, List.length_cons, Nat.add_zero, List.length_nil, Nat.le_refl])
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | serve id observed =>
    simp only [processCore] at computed
    cases completed : Work.complete before.work id with
    | error reason => simp only [completed, Except.mapError, bind, Except.bind] at computed; cases computed
    | ok value =>
      have length := value.pendingPerm.length_eq
      simp only [List.length_cons] at length
      simp only [completed, Except.mapError, bind, Except.bind] at computed
      repeat' first
        | (solve | cases computed; exact quiet_bound ⟨rfl, rfl⟩)
        | (solve | cases computed; change value.state.pending.length + 1 ≤ before.work.pending.length + 0; omega)
        | (solve | cases computed)
        | (split at computed)
        | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | deliver index bytes policy =>
    simp only [processCore] at computed
    repeat' first
      | (solve |
        have quiet := startup_quiet (input := input) (before := before) (by assumption)
        cases computed
        exact quiet_bound ⟨quiet.1, quiet.2⟩)
      | (solve |
        have quiet := application_quiet (input := input) (before := before) (by assumption)
        cases computed
        exact quiet_bound ⟨quiet.1, quiet.2⟩)
      | (solve |
        have quiet := recovery_quiet (input := input) (before := before) (by assumption)
        cases computed
        exact quiet_bound ⟨quiet.1, quiet.2⟩)
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

private theorem prepared_bound (nocopy : ∀ id, event ≠ .copyPacket id)
    (computed : prepareCustody before event = .ok custody) :
    custody.pending.length + assigned event ≤ before.custody.pending.length := by
  cases event <;> simp only [prepareCustody] at computed
  all_goals repeat' first
    | (solve | cases computed; simp only [assigned, Nat.add_zero, Nat.le_refl])
    | (solve | exact False.elim (nocopy _ rfl))
    | (solve | cases computed)
    | (solve |
      cases computed
      have length := (by assumption : Theory.PacketCustody.Resolved _ _ _).pending_length
      simp only [assigned]
      omega)
    | (split at computed)
    | (dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

private theorem finish_bound (before : State input) (effect : Effect input) (custody : Custody input) :
    (finishCustody before effect custody).pending.length ≤
      custody.pending.length + effect.output.toList.length + effect.service.toList.length := by
  cases output : effect.output <;> cases service : effect.service <;> simp only [finishCustody, output, service]
  all_goals repeat' first
    | (solve | simp only [Option.toList_none, Option.toList_some, List.length_nil, List.length_cons,
        Theory.PacketCustody.mint_pending, List.length_append, Nat.add_zero]; omega)
    | split

theorem Step.queued_le (actual : Step input) (nocopy : ∀ id, actual.event ≠ .copyPacket id) :
    queued actual.result.state ≤ queued actual.before + actual.result.output.toList.length := by
  obtain ⟨effect, custody, computed, prepared, final⟩ := actual.transaction
  have work := process_work computed
  have packets := prepared_bound nocopy prepared
  have finished := finish_bound actual.before effect custody
  rw [final]
  change (finishCustody actual.before effect custody).pending.length + effect.state.work.pending.length ≤
    actual.before.custody.pending.length + actual.before.work.pending.length + effect.output.toList.length
  omega


theorem Trace.queued_le_outputs (trace : Trace input initial events steps final remaining)
    (nocopy : ∀ actual ∈ steps, ∀ id, actual.event ≠ .copyPacket id)
    (prior : queued initial ≤ initial.outputs.length) : queued final ≤ final.outputs.length := by
  induction trace with
  | done state => exact prior
  | stop head blocked tail =>
    have bound := Step.queued_le head (nocopy head (by simp))
    have outputs := congrArg List.length (CampusTCPOrigins.output_history head)
    simp only [List.length_append] at outputs
    omega
  | next head accepted rest ih =>
    apply ih (fun actual member => nocopy actual (List.mem_cons_of_mem _ member))
    have bound := Step.queued_le head (nocopy head (by simp))
    have outputs := congrArg List.length (CampusTCPOrigins.output_history head)
    simp only [List.length_append] at outputs
    omega

theorem Trace.outputs_le_steps (trace : Trace input initial events steps final remaining) :
    final.outputs.length ≤ initial.outputs.length + steps.length := by
  induction trace with
  | done state => simp
  | stop head blocked tail =>
    have outputs := congrArg List.length (CampusTCPOrigins.output_history head)
    have single : head.result.output.toList.length ≤ 1 := by cases head.result.output <;> simp
    simp only [List.length_append] at outputs
    simp only [List.length_cons, List.length_nil]
    omega
  | next head accepted rest ih =>
    have outputs := congrArg List.length (CampusTCPOrigins.output_history head)
    have single : head.result.output.toList.length ≤ 1 := by cases head.result.output <;> simp
    simp only [List.length_append] at outputs
    simp only [List.length_cons]
    omega

theorem Report.queued_le_outputs (report : Report input events)
    (nocopy : ∀ actual ∈ report.steps, ∀ id, actual.event ≠ .copyPacket id) :
    queued report.final ≤ report.final.outputs.length :=
  Trace.queued_le_outputs report.trace nocopy (by simp [queued, Input.initial,
    Theory.PacketCustody.State.pending, Theory.PacketCustody.State.initial,
    Theory.Outstanding.State.initial])

theorem Report.outputs_le_steps (report : Report input events) : report.final.outputs.length ≤ report.steps.length := by
  simpa only [Input.initial, List.length_nil, Nat.zero_add] using Trace.outputs_le_steps report.trace

theorem inventory_le_queued (state : State input) : (inventory state).length ≤ queued state := by
  unfold inventory queued
  rw [List.length_append]
  exact Nat.add_le_add (List.length_filterMap_le _ _) (List.length_filterMap_le _ _)

theorem Report.queued_le_steps (report : Report input events)
    (nocopy : ∀ actual ∈ report.steps, ∀ id, actual.event ≠ .copyPacket id) :
    queued report.final ≤ report.steps.length :=
  Nat.le_trans (Report.queued_le_outputs report nocopy) (Report.outputs_le_steps report)

theorem Report.potential_le_steps (report : Report input events)
    (nocopy : ∀ actual ∈ report.steps, ∀ id, actual.event ≠ .copyPacket id) :
    potential report.final ≤ 6 * report.steps.length := by
  exact Nat.le_trans potential_le_six_length
    (Nat.mul_le_mul_left 6 (Nat.le_trans (inventory_le_queued report.final) (Report.queued_le_steps report nocopy)))

end Netlib.Check.CampusTCPStartupQueueBound
