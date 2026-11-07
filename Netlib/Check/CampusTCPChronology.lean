import Netlib.Check.CampusTCPModel

/-!
# Endpoint operation times in the joint campus history

Every stored endpoint operation precedes the next joint slot.
This supplies the cursor time guard from an actual checked history.
-/

namespace Netlib.Check.CampusTCPChronology

open CampusTCPModel

variable {input : Input}

def Earlier (connection : Connection active passive) (limit : Nat) : Prop :=
  match connection with
  | .startup .. => True
  | .recovering current => ∀ actor step, step ∈ current.applicationSteps actor → step.stamp < limit
  | .application _ endpoints =>
      (∀ step ∈ endpoints.client.steps, step.stamp < limit) ∧
      (∀ step ∈ endpoints.server.steps, step.stamp < limit)

def Chronological (state : State input) : Prop := Earlier state.connection state.time

theorem earlier_mono (connection : Connection active passive) (first last : Nat) (order : first ≤ last)
    (prior : Earlier connection first) : Earlier connection last := by
  cases connection with
  | startup => trivial
  | recovering current =>
    intro actor step member
    exact Nat.lt_of_lt_of_le (prior actor step member) order
  | application complete endpoints =>
    constructor
    · intro step member
      exact Nat.lt_of_lt_of_le (prior.1 step member) order
    · intro step member
      exact Nat.lt_of_lt_of_le (prior.2 step member) order

private theorem mapError_ok (value : Except ε α) (map : ε → ε') (output : α)
    (computed : value.mapError map = .ok output) : value = .ok output := by
  cases value <;> simp_all [Except.mapError]

private theorem ofStage_earlier (stage : H.Stage active passive) (limit : Nat) :
    Earlier (Connection.ofStage stage) limit := by
  cases stage <;> simp [Connection.ofStage, Earlier, Applications.initial, Cursor.initial]

private theorem startup_earlier (before : State input) (event : Check.TCPHandshake.Event) (effect : Effect input)
    (computed : startup input before event = .ok effect) (prior : Chronological before) :
    Earlier effect.state.connection (before.time + 1) := by
  unfold startup at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    cases computed
    exact earlier_mono _ _ _ (Nat.le_succ _) prior
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    cases computed
    exact earlier_mono _ _ _ (Nat.le_succ _) prior
  · split at computed
    · cases computed
    · split at computed
      · simp only [pure, Except.pure, Except.ok.injEq] at computed
        cases computed
        exact ofStage_earlier _ _
      · simp only [pure, Except.pure, Except.ok.injEq] at computed
        cases computed
        exact ofStage_earlier _ _

private theorem application_for_selected (selected : TCPHandshakeRecovery.applicationFor actor record = some operation) :
    record = some (actor, operation) := by
  cases record with
  | none => cases selected
  | some pair =>
    obtain ⟨side, retained⟩ := pair
    by_cases same : side = actor
    · subst side
      simp only [TCPHandshakeRecovery.applicationFor, Option.bind_some, ite_true, Option.some.injEq] at selected
      subst retained
      rfl
    · simp only [TCPHandshakeRecovery.applicationFor, Option.bind_some, same, ite_false, reduceCtorEq] at selected

private theorem recovery_state_earlier (computed : TCPHandshakeRecovery.evaluate current stamp event = .ok result)
    (prior : ∀ actor step, step ∈ current.applicationSteps actor → step.stamp < stamp) :
    ∀ actor step, step ∈ result.state.applicationSteps actor → step.stamp < stamp + 1 := by
  intro actor step member
  rw [TCPHandshakeRecovery.evaluate_application_steps computed actor] at member
  rcases List.mem_append.mp member with retained | fresh
  · have old := prior actor step retained
    omega
  · have selected : TCPHandshakeRecovery.applicationFor actor result.application = some step :=
      by simpa only [Option.mem_toList] using fresh
    have recorded := application_for_selected selected
    have same := (TCPHandshakeRecovery.evaluate_records computed).applicationIndex actor step recorded
    rw [same]
    exact Nat.lt_succ_self _

private theorem recovery_earlier (before : State input) (event : C.Event) (effect : Effect input)
    (computed : runRecovery input before event = .ok effect) (prior : Chronological before) :
    Earlier effect.state.connection (before.time + 1) := by
  unfold runRecovery at computed
  split at computed
  · cases computed
    exact earlier_mono _ _ _ (Nat.le_succ _) prior
  · cases computed
    exact earlier_mono _ _ _ (Nat.le_succ _) prior
  · split at computed
    · cases computed
    · rename_i current connected result evaluated
      have old := prior
      simp only [Chronological, Earlier, *] at old
      have fresh := recovery_state_earlier evaluated old
      cases result with
      | mk state decision output receipt application =>
        cases output <;> simp only [pure, Except.pure, Except.ok.injEq] at computed
        all_goals subst effect; exact fresh

private theorem openRecovery_earlier (before : State input) (remote : Protocol.TCP.Handshake.Socket) (policy : Bool)
    (effect : Effect input) (computed : openRecovering input before remote policy = .ok effect) (prior : Chronological before) :
    Earlier effect.state.connection (before.time + 1) := by
  unfold openRecovering at computed
  repeat' first
    | (solve |
      exact recovery_earlier { before with connection := .recovering .initial }
        (.activeOpen remote policy) effect computed (by
        intro actor step member
        cases actor <;> cases member))
    | (solve | cases computed; exact earlier_mono _ _ _ (Nat.le_succ _) prior)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem drain_earlier (before : State input) (effect : Effect input)
    (computed : finishStartup input before = .ok effect) (prior : Chronological before) :
    Earlier effect.state.connection (before.time + 1) := by
  unfold finishStartup at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | (solve | exact earlier_mono _ _ _ (Nat.le_succ _) prior)
      | (solve |
        have old := prior
        simp only [Chronological, Earlier, TCPHandshakeRecovery.State.applicationSteps, *] at old
        constructor
        · intro step member
          have bound := old .active step member
          exact Nat.lt_trans bound (Nat.lt_succ_self _)
        · intro step member
          have bound := old .passive step member
          exact Nat.lt_trans bound (Nat.lt_succ_self _))

private theorem applied_earlier (before : Cursor seed) (event : T.Event) (stamp : Nat) (applied : Applied before)
    (computed : before.apply event stamp = .ok applied) :
    ∀ step ∈ applied.cursor.steps, step.stamp < stamp + 1 := by
  unfold Cursor.apply at computed
  split at computed
  · rename_i earlier
    simp only [pure, Except.pure, Except.ok.injEq] at computed
    cases computed
    intro step member
    rcases List.mem_append.mp member with old | fresh
    · have bound := List.all_eq_true.mp earlier step old
      have beforeStamp : step.stamp < stamp := of_decide_eq_true bound
      omega
    · have same := List.mem_singleton.mp fresh
      rw [same]
      exact Nat.lt_succ_self _
  · cases computed

private theorem application_earlier (before : State input) (actor : Actor) (event : T.Event) (effect : Effect input)
    (computed : applyApplication input before actor event = .ok effect) (prior : Chronological before) :
    Earlier effect.state.connection (before.time + 1) := by
  unfold applyApplication at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    cases computed
    exact earlier_mono _ _ _ (Nat.le_succ _) prior
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    cases computed
    exact earlier_mono _ _ _ (Nat.le_succ _) prior
  · rename_i complete endpoints connection
    have old : Earlier (.application complete endpoints) (before.time + 1) :=
      earlier_mono _ _ _ (Nat.le_succ _) (by simpa only [Chronological, connection] using prior)
    cases actor <;> simp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed
    all_goals
      split at computed
      · cases computed
      · rename_i applied accepted
        have fresh := applied_earlier _ event before.time applied (mapError_ok _ _ _ accepted)
        repeat' first
          | (solve | cases computed; exact ⟨fresh, old.2⟩)
          | (solve | cases computed; exact ⟨old.1, fresh⟩)
          | (solve | cases computed)
          | (split at computed)
          | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)


@[simp] private theorem write_connection (before : State input) (gateway) (resident) :
    (before.write gateway resident).connection = before.connection := by cases gateway <;> rfl

private theorem enableAck_earlier (before : State input) (actor : Actor) (effect : Effect input)
    (computed : enableAck input before actor = .ok effect) (prior : Chronological before) :
    Earlier effect.state.connection (before.time + 1) := by
  unfold enableAck at computed
  repeat' first
    | (solve | exact application_earlier _ _ _ _ computed prior)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem enableRecovery_earlier (before : State input) (actor : Actor) (effect : Effect input)
    (computed : enableRecovery input before actor = .ok effect) (prior : Chronological before) :
    Earlier effect.state.connection (before.time + 1) := by
  unfold enableRecovery at computed
  exact application_earlier _ _ _ _ computed prior

private theorem enableStartupRecovery_earlier (before : State input) (actor : Actor) (effect : Effect input)
    (computed : enableStartupRecovery input before actor = .ok effect) (prior : Chronological before) :
    Earlier effect.state.connection (before.time + 1) := by
  unfold enableStartupRecovery at computed
  split at computed
  · cases computed
    exact earlier_mono _ _ _ (Nat.le_succ _) prior
  · exact application_earlier _ _ _ _ computed prior

private theorem process_earlier (before : State input) (event : Event) (effect : Effect input)
    (computed : processCore input before event = .ok effect) (prior : Chronological before) :
    Earlier effect.state.connection (before.time + 1) := by
  cases event with
  | «open» remote policy => exact startup_earlier _ _ _ computed prior
  | openRecovering remote policy => exact openRecovery_earlier _ _ _ _ computed prior
  | startupClock actor millis | startupTimeout actor generation policy => exact recovery_earlier _ _ _ computed prior
  | finishStartup => exact drain_earlier _ _ computed prior
  | write actor bytes | send actor bytes policy | read actor bytes | emitAck actor policy =>
    exact application_earlier _ _ _ _ computed prior
  | advanceClock actor millis | timeout actor policy | dispatchAck actor policy =>
    exact application_earlier _ _ _ _ computed prior
  | enableRecovery actor => exact enableRecovery_earlier _ _ _ computed prior
  | enableStartupRecovery actor => exact enableStartupRecovery_earlier _ _ _ computed prior
  | enableAck actor => exact enableAck_earlier _ _ _ computed prior
  | copyPacket id | dropPacket id =>
    cases computed
    exact earlier_mono _ _ _ (Nat.le_succ _) prior
  | authentication index =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed)
      | (solve | cases computed; exact earlier_mono _ _ _ (Nat.le_succ _) prior)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | install id | stage id | installGuard id | installAt gateway id | stageAt gateway id | installGuardAt gateway id =>
    simp only [processCore, installConfiguration, stageAttachment, installIngress] at computed
    repeat' first
      | (solve | cases computed)
      | (solve | cases computed; simpa only [write_connection] using earlier_mono before.connection _ _ (Nat.le_succ _) prior)
      | (split at computed)
      | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | pause | stageCheckpoint | installCheckpoint ns | switchRoute actor gateway | fencePrimary | resume =>
    simp only [processCore, transferControl] at computed
    repeat' first
      | (solve | cases computed)
      | (solve | cases computed; exact earlier_mono _ _ _ (Nat.le_succ _) prior)
      | (split at computed)
      | (dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | assign index ingress | serve index observed =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed)
      | (solve | cases computed; simpa only [write_connection, unsupported] using earlier_mono before.connection _ _ (Nat.le_succ _) prior)
      | (cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | deliver index bytes policy =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed; have fresh := startup_earlier before _ _ (by assumption) prior; exact fresh)
      | (solve | cases computed; have fresh := application_earlier before _ _ _ (by assumption) prior; exact fresh)
      | (solve | cases computed; have fresh := recovery_earlier before _ _ (by assumption) prior; exact fresh)
      | (solve | cases computed)
      | (cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)

theorem Step.chronological (actual : Step input) (prior : Chronological actual.before) :
    Chronological actual.result.state := by
  obtain ⟨effect, custody, core, result⟩ := actual.processed
  have times := process_earlier actual.before actual.event effect core prior
  simpa only [result, Chronological] using times

theorem Trace.chronological (trace : Trace input initial events steps final remaining) (prior : Chronological initial) :
    Chronological final := by
  induction trace with
  | done state => exact prior
  | stop head _ _ => exact Step.chronological head prior
  | next head _ _ ih => exact ih (Step.chronological head prior)

theorem Trace.each_chronological (trace : Trace input initial events steps final remaining)
    (prior : Chronological initial) (selected : Step input) (member : selected ∈ steps) : Chronological selected.before := by
  induction trace with
  | done state => simp at member
  | stop head blocked tail =>
    have same : selected = head := by simpa only [List.mem_singleton] using member
    exact same ▸ prior
  | next head supported rest ih =>
    rcases List.mem_cons.mp member with same | later
    · exact same ▸ prior
    · exact ih (Step.chronological head prior) later

theorem Report.chronological (report : Report input events) : Chronological report.final :=
  Trace.chronological report.trace (by trivial)

theorem Report.each_chronological (report : Report input events) (selected : Step input)
    (member : selected ∈ report.steps) : Chronological selected.before :=
  Trace.each_chronological report.trace (by trivial) selected member

theorem Report.application_before (report : Report input events) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : report.final.connection = .application complete endpoints) :
    (∀ step ∈ endpoints.client.steps, step.stamp < report.final.time) ∧
      (∀ step ∈ endpoints.server.steps, step.stamp < report.final.time) := by
  simpa only [Chronological, connection, Earlier] using Report.chronological report

end Netlib.Check.CampusTCPChronology
