import Netlib.Check.CampusTCPEnabled

/-!
# Actual endpoint histories in the campus model

Recovery ACKs enter the current history when they occur.
The drain retains both endpoint histories and their current states.
-/

namespace Netlib.Check.CampusTCPApplicationHistory

open Protocol.TCP CampusTCPModel CampusTCPEnabled

variable {input : Input}

def connectionSteps (connection : Connection active passive) (actor : Actor) : List T.Step :=
  match connection with
  | .startup .. => []
  | .application _ endpoints => applicationSteps endpoints actor
  | .recovering current => current.applicationSteps actor.recoverySide

def localSteps (application : Option (Actor × T.Step)) (actor : Actor) : List T.Step :=
  match application with
  | some (selected, operation) => if selected = actor then [operation] else []
  | none => []

private def Updates (before : State input) (effect : Effect input) : Prop :=
  ∀ actor, connectionSteps effect.state.connection actor = connectionSteps before.connection actor ++ localSteps effect.application actor

private theorem application_updates (before : State input) (actor : Actor) (event : T.Event)
    (effect : Effect input) (computed : applyApplication input before actor event = .ok effect) : Updates before effect := by
  unfold applyApplication at computed
  split at computed
  · cases computed
    intro actor
    simp only [unsupported, connectionSteps, localSteps, List.append_nil]
  · cases computed
    intro actor
    simp only [unsupported, connectionSteps, localSteps, List.append_nil]
  · rename_i complete endpoints connected
    cases actor
    all_goals
      simp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed
      split at computed
      · cases computed
      · rename_i applied accepted
        repeat' first
          | (solve
            | cases computed
              intro receiver
              cases receiver <;> simp [connectionSteps, applicationSteps, connected, localSteps, applied.history, publish])
          | (cases computed)
          | (split at computed)
          | (dsimp only [bind, Except.bind, pure, Except.pure, parsed, Except.mapError] at computed)

private theorem ofStage_steps (stage : H.Stage input.active input.passive) (actor : Actor) :
    connectionSteps (Connection.ofStage stage) actor = [] := by cases stage <;> cases actor <;> rfl

private theorem startup_updates (before : State input) (event : TCPHandshake.Event) (effect : Effect input)
    (computed : startup input before event = .ok effect) : Updates before effect := by
  unfold startup at computed
  split at computed
  · cases computed
    intro actor
    simp only [unsupported, localSteps, List.append_nil]
  · cases computed
    intro actor
    simp only [unsupported, localSteps, List.append_nil]
  · rename_i stage pending connected
    repeat' first
      | (solve
        | cases computed
          intro actor
          change connectionSteps (Connection.ofStage _) actor = connectionSteps before.connection actor ++ []
          rw [ofStage_steps, connected]
          rfl)
      | (cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem mapped_steps (record : Option (TCPHandshakeRecovery.Side × T.Step)) (actor : Actor) :
    localSteps (record.map (fun pair => (Actor.ofRecovery pair.1, pair.2))) actor =
      (TCPHandshakeRecovery.applicationFor actor.recoverySide record).toList := by
  cases record with
  | none => rfl
  | some pair =>
    obtain ⟨side, operation⟩ := pair
    cases side <;> cases actor <;> rfl

private theorem recovery_updates (before : State input) (event : TCPHandshakeRecovery.Event) (effect : Effect input)
    (computed : runRecovery input before event = .ok effect) : Updates before effect := by
  unfold runRecovery at computed
  split at computed
  · cases computed
    intro actor
    simp [unsupported, localSteps]
  · cases computed
    intro actor
    simp [unsupported, localSteps]
  · split at computed
    · cases computed
    · rename_i current connected result evaluated
      have history := TCPHandshakeRecovery.evaluate_application_steps evaluated
      cases result with
      | mk state decision output receipt application =>
        cases output <;> simp only [pure, Except.pure, Except.ok.injEq] at computed
        all_goals
          subst effect
          intro actor
          simpa only [connectionSteps, connected, publish, mapped_steps] using history actor.recoverySide

private theorem openRecovery_updates (before : State input) (remote : Handshake.Socket)
    (policy : Bool) (effect : Effect input) (computed : openRecovering input before remote policy = .ok effect) :
    Updates before effect := by
  unfold openRecovering at computed
  repeat' first
    | (solve | cases computed; intro actor; simp [unsupported, localSteps])
    | (solve
      | have history := recovery_updates _ _ _ computed
        intro actor
        have ready := history actor
        simp_all only [connectionSteps, TCPHandshakeRecovery.State.applicationSteps, TCPHandshakeRecovery.State.initial])
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

private theorem drain_updates (before : State input) (effect : Effect input)
    (computed : finishStartup input before = .ok effect) : Updates before effect := by
  unfold finishStartup at computed
  repeat' first
    | (solve | cases computed; intro actor; cases actor <;> simp_all [unsupported, connectionSteps,
        TCPHandshakeRecovery.State.applicationSteps, applicationSteps, Cursor.ofPreData, localSteps, Actor.recoverySide])
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

private theorem handoff_updates (before : State input) (actor : Actor) (effect : Effect input)
    (computed : enableStartupRecovery input before actor = .ok effect) : Updates before effect := by
  unfold enableStartupRecovery at computed
  split at computed
  · cases computed
    intro receiver
    simp [unsupported, localSteps]
  · exact application_updates _ _ _ _ computed

private theorem enableAck_updates (before : State input) (actor : Actor) (effect : Effect input)
    (computed : enableAck input before actor = .ok effect) : Updates before effect := by
  unfold enableAck at computed
  repeat' first
    | (solve | exact application_updates _ _ _ _ computed)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

@[simp] private theorem write_connection (before : State input) (gateway : Gateway) (resident : Local) :
    (before.write gateway resident).connection = before.connection := by cases gateway <;> rfl

private theorem process_updates (before : State input) (event : Event) (effect : Effect input)
    (computed : processCore input before event = .ok effect) : Updates before effect := by
  cases event with
  | «open» remote policy => exact startup_updates _ _ _ computed
  | openRecovering remote policy => exact openRecovery_updates _ _ _ _ computed
  | startupClock actor millis | startupTimeout actor generation policy => exact recovery_updates _ _ _ computed
  | finishStartup => exact drain_updates _ _ computed
  | enableStartupRecovery actor => exact handoff_updates _ _ _ computed
  | write actor bytes | send actor count policy | read actor count | emitAck actor policy | enableRecovery actor | advanceClock actor millis | timeout actor policy | dispatchAck actor policy =>
    exact application_updates _ _ _ _ computed
  | enableAck actor => exact enableAck_updates _ _ _ computed
  | deliver index bytes policy =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed; simpa only [Updates] using startup_updates _ _ _ (by assumption))
      | (solve | cases computed; simpa only [Updates] using application_updates _ _ _ _ (by assumption))
      | (solve | cases computed; simpa only [Updates] using recovery_updates _ _ _ (by assumption))
      | (cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)
  | authentication index | install id | stage id | installGuard id | installAt gateway id | stageAt gateway id | installGuardAt gateway id | assign index ingress | serve id observed | copyPacket id | dropPacket id | pause | stageCheckpoint | installCheckpoint ns | switchRoute actor gateway | fencePrimary | resume =>
    simp only [processCore, installConfiguration, stageAttachment, installIngress, transferControl] at computed
    repeat' first
      | (solve | cases computed; intro actor; simp only [unsupported, localSteps, write_connection, List.append_nil])
      | (cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)

theorem Step.application_history (actual : Step input) (actor : Actor) :
    connectionSteps actual.result.state.connection actor =
      connectionSteps actual.before.connection actor ++ localSteps actual.result.application actor := by
  obtain ⟨effect, custody, computed, same⟩ := actual.processed
  simpa only [same] using process_updates actual.before actual.event effect computed actor

theorem mem_localSteps (application : Option (Actor × T.Step)) (actor : Actor) (operation : T.Step) :
    operation ∈ localSteps application actor ↔ application = some (actor, operation) := by
  cases application with
  | none => simp [localSteps]
  | some pair =>
    rcases pair with ⟨selected, actual⟩
    cases selected <;> cases actor <;> simp [localSteps, eq_comm]

theorem Trace.application_prefix (trace : Trace input before events steps after remaining) (actor : Actor) :
    connectionSteps before.connection actor <+: connectionSteps after.connection actor := by
  induction trace with
  | done state => exact List.prefix_refl _
  | stop head blocked rest => rw [Step.application_history head]; exact List.prefix_append _ _
  | next head supported rest ih =>
    apply List.IsPrefix.trans _ ih
    rw [Step.application_history head]
    exact List.prefix_append _ _

theorem Trace.application_origin (trace : Trace input before events steps after remaining) (actor : Actor)
    (operation : T.Step) (member : operation ∈ connectionSteps after.connection actor) :
    operation ∈ connectionSteps before.connection actor ∨
      ∃ actual ∈ steps, actual.result.application = some (actor, operation) := by
  induction trace with
  | done state => exact .inl member
  | stop head blocked rest =>
    rw [Step.application_history head] at member
    rcases List.mem_append.mp member with old | fresh
    · exact .inl old
    · exact .inr ⟨head, List.mem_cons_self, (mem_localSteps _ _ _).mp fresh⟩
  | next head supported rest ih =>
    rcases ih member with member | later
    · rw [Step.application_history head] at member
      rcases List.mem_append.mp member with old | fresh
      · exact .inl old
      · exact .inr ⟨head, List.mem_cons_self, (mem_localSteps _ _ _).mp fresh⟩
    · obtain ⟨actual, inside, recorded⟩ := later
      exact .inr ⟨actual, List.mem_cons_of_mem _ inside, recorded⟩

theorem Trace.application_member (trace : Trace input before events steps after remaining)
    (actual : Step input) (member : actual ∈ steps) (actor : Actor) (operation : T.Step)
    (recorded : actual.result.application = some (actor, operation)) : operation ∈ connectionSteps after.connection actor := by
  induction trace with
  | done state => simp at member
  | stop head blocked rest =>
    have same : actual = head := by simpa using member
    subst actual
    rw [Step.application_history head]
    exact List.mem_append_right _ ((mem_localSteps _ _ _).mpr recorded)
  | next head supported rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst actual
      apply (Trace.application_prefix rest actor).subset
      rw [Step.application_history head]
      exact List.mem_append_right _ ((mem_localSteps _ _ _).mpr recorded)
    · exact ih later

theorem Report.application_origin (report : Report input events) (actor : Actor) (operation : T.Step)
    (member : operation ∈ connectionSteps report.final.connection actor) :
    ∃ actual ∈ report.steps, actual.result.application = some (actor, operation) := by
  rcases Trace.application_origin report.trace actor operation member with old | created
  · simp only [Input.initial, connectionSteps, List.not_mem_nil] at old
  · exact created

theorem Report.application_member (report : Report input events) (actual : Step input) (member : actual ∈ report.steps)
    (actor : Actor) (operation : T.Step) (recorded : actual.result.application = some (actor, operation)) :
    operation ∈ connectionSteps report.final.connection actor :=
  Trace.application_member report.trace actual member actor operation recorded


theorem Trace.application_steps (trace : Trace input before events steps after remaining) (actor : Actor) :
    connectionSteps after.connection actor = connectionSteps before.connection actor ++
      steps.flatMap (fun actual => localSteps actual.result.application actor) := by
  induction trace with
  | done state => simp
  | stop head blocked rest => simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using Step.application_history head actor
  | next head supported rest ih =>
    rw [ih, Step.application_history head actor]
    simp only [List.flatMap_cons, List.append_assoc]

theorem Report.application_steps (report : Report input events) (actor : Actor) :
    connectionSteps report.final.connection actor = report.steps.flatMap (fun actual => localSteps actual.result.application actor) := by
  simpa only [Input.initial, connectionSteps, List.nil_append] using Trace.application_steps report.trace actor

end Netlib.Check.CampusTCPApplicationHistory
