import Netlib.Check.CampusTCPModel

/-!
# Fixed environment for a TCP round

Packet service changes transport state and history.
The installed policy and ingress checks remain valid when their inputs stay fixed.
-/

namespace Netlib.Check.CampusTCPService

open Protocol

structure Before.Environment where
  after : Nat
  configuration : Config
  guard : Import.NftablesIngress.Snapshot
  live : List I.InterfaceRef
  attachments : List I.ExpectedAttachment

def Before.environment (before : Before) : Before.Environment :=
  ⟨before.after, before.configuration, before.guard, before.live, before.attachments⟩

def Checks.reframe_transport (checks : Checks context before ingress)
    (tracker : ConntrackLifecycle.State) (admission : TCP.Admission.State) :
    Checks context { before with tracker, admission } ingress :=
  ⟨checks.afterBound, checks.currentLive, checks.namespaceEq, checks.budget,
    checks.forward, checks.forwardComputed, checks.guard, checks.guardComputed, checks.guardSource⟩

@[simp] theorem Checks.reframe_transport_budget (checks : Checks context before ingress)
    (tracker : ConntrackLifecycle.State) (admission : TCP.Admission.State) :
    (checks.reframe_transport tracker admission).budget = checks.budget := rfl

@[simp] theorem Checks.reframe_transport_forward_passed (checks : Checks context before ingress)
    (tracker : ConntrackLifecycle.State) (admission : TCP.Admission.State) :
    (checks.reframe_transport tracker admission).forward.passed = checks.forward.passed := rfl

@[simp] theorem Checks.reframe_transport_guard_passed (checks : Checks context before ingress)
    (tracker : ConntrackLifecycle.State) (admission : TCP.Admission.State) :
    (checks.reframe_transport tracker admission).guard.passed = checks.guard.passed := rfl

@[simp] theorem Checks.reframe_transport_decision (checks : Checks context before ingress)
    (tracker : ConntrackLifecycle.State) (admission : TCP.Admission.State) (source : W.Source) :
    (checks.reframe_transport tracker admission).decision source = checks.decision source := rfl

def Checks.reframe (checks : Checks context before ingress) (after : Before)
    (same : before.environment = after.environment) : Checks context after ingress := by
  cases before
  cases after
  simp only [Before.environment, Before.Environment.mk.injEq] at same
  rcases same with ⟨rfl, rfl, rfl, rfl, rfl⟩
  exact checks.reframe_transport _ _

@[simp] theorem Checks.reframe_budget (checks : Checks context before ingress) (after : Before)
    (same : before.environment = after.environment) :
    (checks.reframe after same).budget = checks.budget := by
  cases before
  cases after
  simp only [Before.environment, Before.Environment.mk.injEq] at same
  rcases same with ⟨rfl, rfl, rfl, rfl, rfl⟩
  rfl

@[simp] theorem Checks.reframe_forward_passed (checks : Checks context before ingress) (after : Before)
    (same : before.environment = after.environment) :
    (checks.reframe after same).forward.passed = checks.forward.passed := by
  cases before
  cases after
  simp only [Before.environment, Before.Environment.mk.injEq] at same
  rcases same with ⟨rfl, rfl, rfl, rfl, rfl⟩
  rfl

@[simp] theorem Checks.reframe_guard_passed (checks : Checks context before ingress) (after : Before)
    (same : before.environment = after.environment) :
    (checks.reframe after same).guard.passed = checks.guard.passed := by
  cases before
  cases after
  simp only [Before.environment, Before.Environment.mk.injEq] at same
  rcases same with ⟨rfl, rfl, rfl, rfl, rfl⟩
  rfl

@[simp] theorem Checks.reframe_decision (checks : Checks context before ingress) (after : Before)
    (same : before.environment = after.environment) (source : W.Source) :
    (checks.reframe after same).decision source = checks.decision source := by
  cases before
  cases after
  simp only [Before.environment, Before.Environment.mk.injEq] at same
  rcases same with ⟨rfl, rfl, rfl, rfl, rfl⟩
  rfl

end Netlib.Check.CampusTCPService

namespace Netlib.Check.CampusTCPRoundEnvironment

open CampusTCPModel

structure LocalEnvironment where
  configuration : Check.ConntrackLifecycle.Config
  guard : Guard
  live : List I.InterfaceRef
  attachments : List Staged

def localEnvironment (resident : Local) : LocalEnvironment :=
  ⟨resident.configuration, resident.guard, resident.live, resident.attachments⟩

structure Environment where
  authentication : Nat
  primary : LocalEnvironment
  standby : LocalEnvironment
  owners : Protocol.StatefulFailover.Owners
  routeEpoch : Nat
  assignmentPaused : Bool
  primarySealed : Bool
  primaryFenced : Bool
  installed : Bool

def environment (state : State input) : Environment :=
  ⟨state.authentication, localEnvironment state.primary, localEnvironment state.standby,
    state.owners, state.routeEpoch, state.assignmentPaused, state.primarySealed, state.primaryFenced,
    state.installation.isSome⟩

def TransportOnly : Event → Prop
  | .open .. | .write .. | .send .. | .enableRecovery .. | .enableAck .. | .dispatchAck ..
  | .advanceClock .. | .timeout .. | .read .. | .emitAck .. | .assign .. | .serve ..
  | .deliver .. | .copyPacket .. | .dropPacket .. => True
  | _ => False

theorem service_environment (before after : State input) (same : environment before = environment after)
    (gateway : Gateway) :
    (beforeService input before gateway).environment = (beforeService input after gateway).environment := by
  have authentication := congrArg Environment.authentication same
  have primary := congrArg Environment.primary same
  have standby := congrArg Environment.standby same
  change before.authentication = after.authentication at authentication
  let project (resident : LocalEnvironment) : CampusTCPService.Before.Environment :=
    ⟨after.authentication, resident.configuration, resident.guard.source, resident.live,
      resident.attachments.map (·.value)⟩
  cases gateway
  · simp only [beforeService, State.resident, CampusTCPService.Before.environment]
    rw [authentication]
    exact congrArg project primary
  · simp only [beforeService, State.resident, CampusTCPService.Before.environment]
    rw [authentication]
    exact congrArg project standby

private theorem startup_environment (before : State input) (event : Check.TCPHandshake.Event) (effect : Effect input)
    (computed : startup input before event = .ok effect) : environment before = environment effect.state := by
  unfold startup at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem application_environment (before : State input) (actor : Actor) (event : T.Event) (effect : Effect input)
    (computed : applyApplication input before actor event = .ok effect) : environment before = environment effect.state := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

private theorem enableAck_environment (before : State input) (actor : Actor) (effect : Effect input)
    (computed : enableAck input before actor = .ok effect) : environment before = environment effect.state := by
  unfold enableAck at computed
  split at computed
  · exact application_environment _ _ _ _ computed
  · cases actor <;> dsimp only at computed
    all_goals
      split at computed
      · exact application_environment _ _ _ _ computed
      · cases computed

private theorem service_write (before : State input) (gateway : Gateway)
    (tracker : Protocol.ConntrackLifecycle.State) (admission : Protocol.TCP.Admission.State)
    (history : Protocol.TCP.Checkpoint.History ⟨tracker, admission⟩) :
    environment before = environment (before.write gateway
      { before.resident gateway with transport := ⟨tracker, admission⟩, history }) := by
  cases gateway <;> rfl

private theorem process_environment (before : State input) (event : Event) (effect : Effect input)
    (computed : processCore input before event = .ok effect) (selected : TransportOnly event) :
    environment before = environment effect.state := by
  cases event with
  | «open» remote policy => exact startup_environment _ _ _ computed
  | write actor bytes | send actor bytes policy | read actor bytes | emitAck actor policy =>
    exact application_environment _ _ _ _ computed
  | enableRecovery actor | advanceClock actor millis | timeout actor policy | dispatchAck actor policy =>
    exact application_environment _ _ _ _ computed
  | enableAck actor => exact enableAck_environment _ _ _ computed
  | copyPacket id | dropPacket id => cases computed; rfl
  | authentication index | install id | stage id | installGuard id | installAt gateway id
  | stageAt gateway id | installGuardAt gateway id | pause | stageCheckpoint | installCheckpoint ns
  | switchRoute actor gateway | fencePrimary | resume => cases selected
  | assign index ingress =>
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
      | (solve | cases computed; simpa only [environment] using startup_environment before _ _ (by assumption))
      | (solve | cases computed; simpa only [environment] using application_environment before _ _ _ (by assumption))
      | (cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)

theorem Step.environment (actual : Step input) (selected : TransportOnly actual.event) :
    environment actual.before = environment actual.result.state := by
  obtain ⟨effect, custody, computed, same⟩ := actual.processed
  have fixed := process_environment actual.before actual.event effect computed selected
  simpa only [same, CampusTCPRoundEnvironment.environment] using fixed

theorem Step.service_environment (actual : Step input) (selected : TransportOnly actual.event) (gateway : Gateway) :
    (beforeService input actual.before gateway).environment =
      (beforeService input actual.result.state gateway).environment :=
  CampusTCPRoundEnvironment.service_environment _ _ (Step.environment actual selected) gateway

def Step.reframe_checks (actual : Step input) (selected : TransportOnly actual.event) (gateway : Gateway)
    (checks : CampusTCPService.Checks (input.contextFor gateway) (beforeService input actual.before gateway) ingress) :
    CampusTCPService.Checks (input.contextFor gateway) (beforeService input actual.result.state gateway) ingress :=
  checks.reframe _ (Step.service_environment actual selected gateway)

theorem Trace.environment (trace : Trace input initial events steps final remaining)
    (selected : ∀ actual ∈ steps, TransportOnly actual.event) : environment initial = environment final := by
  induction trace with
  | done state => rfl
  | stop head blocked tail => exact Step.environment head (selected head (by simp))
  | next head supported rest ih =>
    exact (Step.environment head (selected head (by simp))).trans
      (ih (fun actual member => selected actual (List.mem_cons_of_mem _ member)))

theorem Trace.each_environment (trace : Trace input initial events steps final remaining)
    (selected : ∀ actual ∈ steps, TransportOnly actual.event) (actual : Step input) (member : actual ∈ steps) :
    CampusTCPRoundEnvironment.environment initial = CampusTCPRoundEnvironment.environment actual.before := by
  induction trace with
  | done state => simp at member
  | stop head blocked tail =>
    have same : actual = head := by simpa only [List.mem_singleton] using member
    exact same ▸ rfl
  | next head supported rest ih =>
    rcases List.mem_cons.mp member with same | later
    · exact same ▸ rfl
    · exact (Step.environment head (selected head (by simp))).trans
        (ih (fun next present => selected next (List.mem_cons_of_mem _ present)) later)

theorem Trace.service_environment (trace : Trace input initial events steps final remaining)
    (selected : ∀ actual ∈ steps, TransportOnly actual.event) (gateway : Gateway) :
    (beforeService input initial gateway).environment = (beforeService input final gateway).environment :=
  CampusTCPRoundEnvironment.service_environment _ _ (Trace.environment trace selected) gateway

def Trace.reframe_checks (trace : Trace input initial events steps final remaining)
    (selected : ∀ actual ∈ steps, TransportOnly actual.event) (gateway : Gateway)
    (checks : CampusTCPService.Checks (input.contextFor gateway) (beforeService input initial gateway) ingress) :
    CampusTCPService.Checks (input.contextFor gateway) (beforeService input final gateway) ingress :=
  checks.reframe _ (Trace.service_environment trace selected gateway)

def Nonservice : Event → Prop
  | .open .. | .write .. | .send .. | .enableRecovery .. | .enableAck .. | .dispatchAck ..
  | .advanceClock .. | .timeout .. | .read .. | .emitAck .. | .assign ..
  | .deliver .. | .copyPacket .. | .dropPacket .. => True
  | _ => False

private theorem startup_resident (before : State input) (event : Check.TCPHandshake.Event) (effect : Effect input)
    (computed : startup input before event = .ok effect) (gateway : Gateway) :
    effect.state.resident gateway = before.resident gateway := by
  unfold startup at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem application_resident (before : State input) (actor : Actor) (event : T.Event) (effect : Effect input)
    (computed : applyApplication input before actor event = .ok effect) (gateway : Gateway) :
    effect.state.resident gateway = before.resident gateway := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

private theorem enableAck_resident (before : State input) (actor : Actor) (effect : Effect input)
    (computed : enableAck input before actor = .ok effect) (gateway : Gateway) :
    effect.state.resident gateway = before.resident gateway := by
  unfold enableAck at computed
  split at computed
  · exact application_resident _ _ _ _ computed gateway
  · cases actor <;> dsimp only at computed
    all_goals
      split at computed
      · exact application_resident _ _ _ _ computed gateway
      · cases computed

private theorem process_resident (before : State input) (event : Event) (effect : Effect input)
    (computed : processCore input before event = .ok effect) (selected : Nonservice event) (gateway : Gateway) :
    effect.state.resident gateway = before.resident gateway := by
  cases event with
  | «open» remote policy => exact startup_resident _ _ _ computed gateway
  | write actor bytes | send actor bytes policy | read actor bytes | emitAck actor policy =>
    exact application_resident _ _ _ _ computed gateway
  | enableRecovery actor | advanceClock actor millis | timeout actor policy | dispatchAck actor policy =>
    exact application_resident _ _ _ _ computed gateway
  | enableAck actor => exact enableAck_resident _ _ _ computed gateway
  | copyPacket id | dropPacket id => cases computed; rfl
  | authentication index | install id | stage id | installGuard id | installAt owner id
  | stageAt owner id | installGuardAt owner id | pause | stageCheckpoint | installCheckpoint ns
  | switchRoute actor owner | fencePrimary | resume | serve id observed => cases selected
  | assign index ingress =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed; rfl)
      | (cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)
  | deliver index bytes policy =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed; simpa only [State.resident] using startup_resident before _ _ (by assumption) gateway)
      | (solve | cases computed; simpa only [State.resident] using application_resident before _ _ _ (by assumption) gateway)
      | (cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)

theorem Step.resident_nonservice (actual : Step input) (selected : Nonservice actual.event) (gateway : Gateway) :
    actual.result.state.resident gateway = actual.before.resident gateway := by
  obtain ⟨effect, custody, computed, same⟩ := actual.processed
  have fixed := process_resident actual.before actual.event effect computed selected gateway
  simpa only [same, State.resident] using fixed

theorem Trace.resident_nonservice (trace : Trace input initial events steps final remaining)
    (selected : ∀ actual ∈ steps, Nonservice actual.event) (gateway : Gateway) :
    final.resident gateway = initial.resident gateway := by
  induction trace with
  | done state => rfl
  | stop head blocked tail => exact Step.resident_nonservice head (selected head (by simp)) gateway
  | next head supported rest ih =>
    exact (ih (fun actual member => selected actual (List.mem_cons_of_mem _ member))).trans
      (Step.resident_nonservice head (selected head (by simp)) gateway)

end Netlib.Check.CampusTCPRoundEnvironment
