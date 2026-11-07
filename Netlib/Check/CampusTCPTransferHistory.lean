import Netlib.Check.CampusTCPOrigins

/-!
# Actual planned-transfer history

Stored checkpoints retain their actual earlier capture operation.
Sealing keeps the source transport cut and its transfer records fixed.
-/

namespace Netlib.Check.CampusTCPTransferHistory

open Packet Protocol
namespace M
export Check.CampusTCPModel (Input State Step Trace Report Effect Event CachedCheckpoint)
end M

private def Keeps (before : M.State input) (effect : M.Effect input) : Prop :=
  effect.state.primarySealed = before.primarySealed ∧
  effect.state.primaryFenced = before.primaryFenced ∧
  effect.state.primary.transport = before.primary.transport ∧
  effect.state.cache = before.cache ∧
  effect.state.installation = before.installation ∧ effect.checkpoint = none

@[simp] private theorem write_cache (before : M.State input) (gateway) (resident) :
    (before.write gateway resident).cache = before.cache := by cases gateway <;> rfl

@[simp] private theorem write_fenced (before : M.State input) (gateway) (resident) :
    (before.write gateway resident).primaryFenced = before.primaryFenced := by cases gateway <;> rfl

@[simp] private theorem write_installation (before : M.State input) (gateway) (resident) :
    (before.write gateway resident).installation = before.installation := by cases gateway <;> rfl

private theorem startup_keeps (input : M.Input) (before : M.State input)
    (event : Check.TCPHandshake.Event) (effect : M.Effect input)
    (accepted : Check.CampusTCPModel.startup input before event = .ok effect) : Keeps before effect := by
  unfold Check.CampusTCPModel.startup at accepted
  repeat' first
    | (solve | cases accepted)
    | (solve | cases accepted; simp [Keeps, Check.CampusTCPModel.unsupported, Check.CampusTCPModel.publish])
    | (split at accepted)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted)

private theorem application_keeps (input : M.Input) (before : M.State input)
    (actor : Check.CampusTCPModel.Actor) (event : TCP.ApplicationTrace.Event) (effect : M.Effect input)
    (accepted : Check.CampusTCPModel.applyApplication input before actor event = .ok effect) : Keeps before effect := by
  unfold Check.CampusTCPModel.applyApplication at accepted
  split at accepted
  · cases accepted
    simp [Keeps, Check.CampusTCPModel.unsupported]
  · cases accepted
    simp [Keeps, Check.CampusTCPModel.unsupported]
  · cases actor <;> simp only at accepted
    all_goals
      repeat' first
        | (solve | cases accepted)
        | (solve | cases accepted; simp [Keeps, Check.CampusTCPModel.publish])
        | (split at accepted)
        | (dsimp only [Check.CampusTCPModel.parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at accepted)

private theorem recovery_keeps (input : M.Input) (before : M.State input)
    (event : Check.TCPHandshakeRecovery.Event) (effect : M.Effect input)
    (accepted : Check.CampusTCPModel.runRecovery input before event = .ok effect) : Keeps before effect := by
  unfold Check.CampusTCPModel.runRecovery at accepted
  split at accepted
  · cases accepted
    simp [Keeps, Check.CampusTCPModel.unsupported]
  · cases accepted
    simp [Keeps, Check.CampusTCPModel.unsupported]
  · split at accepted
    · cases accepted
    · rename_i current connected result evaluated
      cases result with
      | mk state decision output receipt application =>
        cases output <;> simp only [pure, Except.pure, Except.ok.injEq] at accepted
        all_goals subst effect; simp [Keeps, Check.CampusTCPModel.publish]

private theorem openRecovery_keeps (input : M.Input) (before : M.State input)
    (remote : TCP.Handshake.Socket) (policy : Bool) (effect : M.Effect input)
    (accepted : Check.CampusTCPModel.openRecovering input before remote policy = .ok effect) : Keeps before effect := by
  unfold Check.CampusTCPModel.openRecovering at accepted
  repeat' first
    | (solve |
      exact recovery_keeps input { before with connection := .recovering .initial }
        (.activeOpen remote policy) effect accepted)
    | (solve | cases accepted)
    | (solve | cases accepted; simp [Keeps, Check.CampusTCPModel.unsupported])
    | (split at accepted)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted)

private theorem drain_keeps (input : M.Input) (before : M.State input) (effect : M.Effect input)
    (accepted : Check.CampusTCPModel.finishStartup input before = .ok effect) : Keeps before effect := by
  unfold Check.CampusTCPModel.finishStartup at accepted
  repeat' first
    | (solve | cases accepted)
    | (solve | cases accepted; simp [Keeps, Check.CampusTCPModel.unsupported])
    | (split at accepted)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted)

private structure Changes (before : M.State input) (effect : M.Effect input) : Prop where
  cache : ∀ checkpoint, effect.state.cache = some checkpoint →
    before.cache = some checkpoint ∨ effect.checkpoint = some checkpoint ∧ checkpoint.time = before.time
  sealed : before.primarySealed = true → effect.state.primarySealed = true
  fenced : before.primaryFenced = true → effect.state.primaryFenced = true
  transport : before.primarySealed = true → effect.state.primary.transport = before.primary.transport
  cacheStable : before.primarySealed = true → effect.state.cache = before.cache
  installation : before.primarySealed = true → effect.state.installation = before.installation

private theorem enableAck_keeps (input : M.Input) (before : M.State input) (actor : Check.CampusTCPModel.Actor)
    (effect : M.Effect input) (accepted : Check.CampusTCPModel.enableAck input before actor = .ok effect) :
    Keeps before effect := by
  unfold Check.CampusTCPModel.enableAck at accepted
  repeat' first
    | (solve | exact application_keeps _ _ _ _ _ accepted)
    | (solve | cases accepted)
    | (split at accepted)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at accepted)

private theorem enableRecovery_keeps (input : M.Input) (before : M.State input) (actor : Check.CampusTCPModel.Actor)
    (effect : M.Effect input) (accepted : Check.CampusTCPModel.enableRecovery input before actor = .ok effect) :
    Keeps before effect := by
  unfold Check.CampusTCPModel.enableRecovery at accepted
  exact application_keeps _ _ _ _ _ accepted

private theorem enableStartupRecovery_keeps (input : M.Input) (before : M.State input) (actor : Check.CampusTCPModel.Actor)
    (effect : M.Effect input) (accepted : Check.CampusTCPModel.enableStartupRecovery input before actor = .ok effect) :
    Keeps before effect := by
  unfold Check.CampusTCPModel.enableStartupRecovery at accepted
  split at accepted
  · cases accepted
    simp [Keeps, Check.CampusTCPModel.unsupported]
  · exact application_keeps _ _ _ _ _ accepted

private theorem keeps_changes (kept : Keeps before effect) : Changes before effect := by
  obtain ⟨sealed, fenced, transport, cache, installation, _⟩ := kept
  exact ⟨fun checkpoint selected => .inl (cache ▸ selected), fun prior => sealed.trans prior,
    fun prior => fenced.trans prior, fun _ => transport, fun _ => cache, fun _ => installation⟩

private theorem process_changes (input : M.Input) (before : M.State input) (event : M.Event)
    (effect : M.Effect input) (accepted : Check.CampusTCPModel.processCore input before event = .ok effect) :
    Changes before effect := by
  cases event with
  | «open» remote policy => exact keeps_changes (startup_keeps _ _ _ _ accepted)
  | openRecovering remote policy => exact keeps_changes (openRecovery_keeps _ _ _ _ _ accepted)
  | startupClock actor millis | startupTimeout actor generation policy =>
    exact keeps_changes (recovery_keeps _ _ _ _ accepted)
  | finishStartup => exact keeps_changes (drain_keeps _ _ _ accepted)
  | write actor bytes | send actor bytes policy | read actor bytes | emitAck actor policy =>
    exact keeps_changes (application_keeps _ _ _ _ _ accepted)
  | advanceClock actor millis | timeout actor policy =>
    exact keeps_changes (application_keeps _ _ _ _ _ accepted)
  | enableRecovery actor => exact keeps_changes (enableRecovery_keeps _ _ _ _ accepted)
  | enableStartupRecovery actor => exact keeps_changes (enableStartupRecovery_keeps _ _ _ _ accepted)
  | dispatchAck actor policy => exact keeps_changes (application_keeps _ _ _ _ _ accepted)
  | enableAck actor => exact keeps_changes (enableAck_keeps _ _ _ _ accepted)
  | copyPacket id | dropPacket id =>
    cases accepted
    exact keeps_changes (by simp [Keeps])
  | authentication index =>
    simp only [Check.CampusTCPModel.processCore] at accepted
    repeat' first
      | (solve | cases accepted)
      | (solve | cases accepted; exact keeps_changes (by simp [Keeps]))
      | (split at accepted)
      | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted)
  | install id | stage id | installGuard id | installAt gateway id | stageAt gateway id | installGuardAt gateway id =>
    simp only [Check.CampusTCPModel.processCore, Check.CampusTCPModel.installConfiguration,
      Check.CampusTCPModel.stageAttachment, Check.CampusTCPModel.installIngress] at accepted
    repeat' first
      | (solve | cases accepted)
      | (solve | cases accepted; apply keeps_changes; cases gateway <;> simp [Keeps, Check.CampusTCPModel.State.write, Check.CampusTCPModel.State.resident])
      | (solve | cases accepted; apply keeps_changes; simp [Keeps, Check.CampusTCPModel.State.write, Check.CampusTCPModel.State.resident])
      | (split at accepted)
      | (dsimp only [Check.CampusTCPModel.parsed, Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted)
  | pause | stageCheckpoint | installCheckpoint ns | switchRoute actor gateway | fencePrimary | resume =>
    simp only [Check.CampusTCPModel.processCore, Check.CampusTCPModel.transferControl] at accepted
    repeat' first
      | (solve | cases accepted)
      | (solve | cases accepted; apply keeps_changes; simp [Keeps])
      | (solve | cases accepted; constructor <;> simp_all)
      | (split at accepted)
      | (dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted)
  | assign index ingress =>
    simp only [Check.CampusTCPModel.processCore] at accepted
    repeat' first
      | (solve | cases accepted)
      | (solve | cases accepted; apply keeps_changes; simp [Keeps])
      | (split at accepted)
      | (dsimp only [Check.CampusTCPModel.get, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted)
  | serve id observed =>
    simp only [Check.CampusTCPModel.processCore] at accepted
    cases completed : Theory.Outstanding.complete before.work id with
    | error reason => simp [completed, Except.mapError, bind, Except.bind] at accepted
    | ok work =>
      simp only [completed, Except.mapError, bind, Except.bind] at accepted
      split at accepted
      · simp [throw] at accepted
      · rename_i permitted
        have target : before.primarySealed = true → work.item.value.gateway = .standby := by
          intro sealed
          cases gateway : work.item.value.gateway with
          | primary => simp [gateway, sealed] at permitted <;> cases permitted
          | standby => rfl
        repeat' first
          | (solve | cases accepted)
          | (solve | cases accepted; apply keeps_changes; simp [Keeps, Check.CampusTCPModel.unsupported])
          | (cases accepted)
          | (split at accepted)
          | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted)
        all_goals
          constructor
          · intro checkpoint selected
            exact .inl (write_cache before _ _ ▸ selected)
          · intro sealed
            simp [Check.CampusTCPModel.State.write, target sealed, sealed]
          · intro fenced
            exact (write_fenced before _ _).trans fenced
          · intro sealed
            simp [target sealed, Check.CampusTCPModel.State.write]
          · intro sealed
            exact write_cache before _ _
          · intro sealed
            exact write_installation before _ _
  | deliver index bytes policy =>
    simp only [Check.CampusTCPModel.processCore] at accepted
    repeat' first
      | (solve | cases accepted)
      | (solve | apply keeps_changes; simpa only [Keeps] using (startup_keeps input before _ _ (by assumption)))
      | (solve | apply keeps_changes; simpa only [Keeps] using (application_keeps input before _ _ _ (by assumption)))
      | (solve | apply keeps_changes; simpa only [Keeps] using (recovery_keeps input before _ _ (by assumption)))
      | (cases accepted)
      | (split at accepted)
      | (dsimp only [Check.CampusTCPModel.get, Check.CampusTCPModel.parsed, Except.mapError,
          bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted)

private theorem step_changes (step : M.Step input) : Changes step.before step.result := by
  obtain ⟨effect, custody, computed, same⟩ := step.processed
  have changes := process_changes input step.before step.event effect computed
  rw [same]
  exact ⟨changes.cache, changes.sealed, changes.fenced, changes.transport, changes.cacheStable, changes.installation⟩

namespace Step

theorem sealed (step : M.Step input) (prior : step.before.primarySealed = true) :
    step.result.state.primarySealed = true :=
  (step_changes step).sealed prior

theorem fenced (step : M.Step input) (prior : step.before.primaryFenced = true) :
    step.result.state.primaryFenced = true :=
  (step_changes step).fenced prior

theorem source_stable (step : M.Step input) (prior : step.before.primarySealed = true) :
    step.result.state.primary.transport = step.before.primary.transport :=
  (step_changes step).transport prior

theorem cache_stable (step : M.Step input) (prior : step.before.primarySealed = true) :
    step.result.state.cache = step.before.cache :=
  (step_changes step).cacheStable prior

theorem installation_stable (step : M.Step input) (prior : step.before.primarySealed = true) :
    step.result.state.installation = step.before.installation :=
  (step_changes step).installation prior

end Step

namespace Trace

theorem sealed_state (trace : M.Trace input initial events steps final remaining)
    (sealed : initial.primarySealed = true) :
    final.primarySealed = true ∧ final.primary.transport = initial.primary.transport ∧
      final.cache = initial.cache ∧ final.installation = initial.installation := by
  induction trace with
  | done state => exact ⟨sealed, rfl, rfl, rfl⟩
  | stop head blocked tail =>
    exact ⟨Step.sealed head sealed, Step.source_stable head sealed,
      Step.cache_stable head sealed, Step.installation_stable head sealed⟩
  | next head supported rest ih =>
    obtain ⟨later, transport, cache, installation⟩ := ih (Step.sealed head sealed)
    exact ⟨later, transport.trans (Step.source_stable head sealed),
      cache.trans (Step.cache_stable head sealed), installation.trans (Step.installation_stable head sealed)⟩

theorem sealed (trace : M.Trace input initial events steps final remaining)
    (prior : initial.primarySealed = true) : final.primarySealed = true :=
  (sealed_state trace prior).1

theorem fenced (trace : M.Trace input initial events steps final remaining)
    (prior : initial.primaryFenced = true) : final.primaryFenced = true := by
  induction trace with
  | done state => exact prior
  | stop head blocked tail => exact Step.fenced head prior
  | next head supported rest ih => exact ih (Step.fenced head prior)

theorem source_stable (trace : M.Trace input initial events steps final remaining)
    (prior : initial.primarySealed = true) : final.primary.transport = initial.primary.transport :=
  (sealed_state trace prior).2.1

theorem cache_stable (trace : M.Trace input initial events steps final remaining)
    (prior : initial.primarySealed = true) : final.cache = initial.cache :=
  (sealed_state trace prior).2.2.1

theorem installation_stable (trace : M.Trace input initial events steps final remaining)
    (prior : initial.primarySealed = true) : final.installation = initial.installation :=
  (sealed_state trace prior).2.2.2

theorem member_sealed_state (trace : M.Trace input initial events steps final remaining)
    (step : M.Step input) (member : step ∈ steps) (sealed : step.result.state.primarySealed = true) :
    final.primarySealed = true ∧ final.primary.transport = step.result.state.primary.transport ∧
      final.cache = step.result.state.cache ∧ final.installation = step.result.state.installation := by
  induction trace with
  | done state => simp at member
  | stop head blocked tail =>
    have same : step = head := by simpa using member
    subst step
    exact ⟨sealed, rfl, rfl, rfl⟩
  | next head supported rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst step
      exact sealed_state rest sealed
    · exact ih later

theorem member_fenced (trace : M.Trace input initial events steps final remaining)
    (step : M.Step input) (member : step ∈ steps) (fenced : step.result.state.primaryFenced = true) :
    final.primaryFenced = true := by
  induction trace with
  | done state => simp at member
  | stop head blocked tail =>
    have same : step = head := by simpa using member
    subst step
    exact fenced
  | next head supported rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst step
      exact Trace.fenced rest fenced
    · exact ih later

theorem cache_origin (trace : M.Trace input initial events steps final remaining)
    (checkpoint : M.CachedCheckpoint) (selected : final.cache = some checkpoint) :
    initial.cache = some checkpoint ∨ ∃ step, step ∈ steps ∧ step.result.checkpoint = some checkpoint ∧
      checkpoint.time = step.before.time ∧ step.before.time < final.time := by
  induction trace with
  | done state => exact .inl selected
  | stop head blocked tail =>
    rcases (step_changes head).cache checkpoint selected with prior | created
    · exact .inl prior
    · exact .inr ⟨head, by simp, created.1, created.2, by have clock := head.clock; omega⟩
  | next head supported rest ih =>
    rcases ih selected with prior | created
    · rcases (step_changes head).cache checkpoint prior with old | new
      · exact .inl old
      · refine .inr ⟨head, by simp, new.1, new.2, ?_⟩
        have clock := head.clock
        have elapsed := CampusTCPOrigins.Trace.time rest
        omega
    · obtain ⟨step, member, present, stamped, earlier⟩ := created
      exact .inr ⟨step, by simp [member], present, stamped, earlier⟩

end Trace

namespace Report

theorem source_after_seal (report : M.Report input events) (step : M.Step input)
    (member : step ∈ report.steps) (sealed : step.result.state.primarySealed = true) :
    report.final.primary.transport = step.result.state.primary.transport :=
  (Trace.member_sealed_state report.trace step member sealed).2.1

theorem state_after_seal (report : M.Report input events) (step : M.Step input)
    (member : step ∈ report.steps) (sealed : step.result.state.primarySealed = true) :
    report.final.primarySealed = true ∧ report.final.primary.transport = step.result.state.primary.transport ∧
      report.final.cache = step.result.state.cache ∧ report.final.installation = step.result.state.installation :=
  Trace.member_sealed_state report.trace step member sealed

theorem fenced_after (report : M.Report input events) (step : M.Step input)
    (member : step ∈ report.steps) (fenced : step.result.state.primaryFenced = true) :
    report.final.primaryFenced = true :=
  Trace.member_fenced report.trace step member fenced

end Report

end Netlib.Check.CampusTCPTransferHistory
