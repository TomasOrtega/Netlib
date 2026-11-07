import Netlib.Check.CampusTCPTransferFacts
import Netlib.Check.CampusTCPRoundPhaseBase
import Netlib.Check.CampusTCPRoundEnvironment

/-!
# Planned transfer from current guards

Control operations retain endpoint and packet histories.
Their policy frame excludes route and transfer-control fields.
-/

namespace Netlib.Check.CampusTCPTransferEnabled

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)

local notation "Event" => CampusTCPModel.Event

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {current : Cut input complete}

structure CaptureReady (gateway : Checkpoint.Gateway) : Prop where
  selected : ∃ session record, gateway.admission.phase = .data session ∧
    record ∈ gateway.tracker.records ∧ record.entry = session.entry ∧ record.entry.flow.original.protocol = .tcp

structure PauseReady (state : State input) : Prop where
  configured : input.configured .standby = true
  unpaused : state.assignmentPaused = false
  unsealed : state.primarySealed = false
  unfenced : state.primaryFenced = false

structure StageReady (state : State input) : Prop where
  configured : input.configured .standby = true
  unsealed : state.primarySealed = false
  unfenced : state.primaryFenced = false
  capture : CaptureReady state.primary.transport

structure InstallReady (state : State input) : Prop where
  configured : input.configured .standby = true
  paused : state.assignmentPaused = true
  unsealed : state.primarySealed = false
  unfenced : state.primaryFenced = false
  drained : state.outstanding .primary = 0
  namespaceEq : state.standby.guard.source.ns = (input.deployment .standby).executionNS
  empty : state.standby.transport = Checkpoint.Gateway.initial
  fresh : ∃ checkpoint, state.cache = some checkpoint ∧ state.primary.transport = checkpoint.snapshot.source ∧
    state.primary.history.length = checkpoint.snapshot.cut

structure RouteReady (state : State input) : Prop where
  configured : input.configured .standby = true
  paused : state.assignmentPaused = true
  sealed : state.primarySealed = true
  consistent : ∃ installed, state.installation = some installed ∧
    state.primary.transport = installed.checkpoint.snapshot.source ∧ state.standby.transport = installed.installed.state

structure FenceReady (state : State input) : Prop where
  configured : input.configured .standby = true
  paused : state.assignmentPaused = true
  sealed : state.primarySealed = true
  installed : state.installation.isSome = true
  client : state.owners.client = .standby
  server : state.owners.server = .standby
  drained : state.outstanding .primary = 0

structure ResumeReady (state : State input) : Prop where
  configured : input.configured .standby = true
  paused : state.assignmentPaused = true
  fenced : state.primaryFenced = true
  client : state.owners.client = .standby
  server : state.owners.server = .standby
  consistent : ∃ installed, state.installation = some installed ∧
    state.primary.transport = installed.checkpoint.snapshot.source ∧ state.standby.transport = installed.installed.state

structure Ready (state : State input) : Prop extends PauseReady state where
  capture : CaptureReady state.primary.transport
  drained : state.outstanding .primary = 0
  namespaceEq : state.standby.guard.source.ns = (input.deployment .standby).executionNS
  empty : state.standby.transport = Checkpoint.Gateway.initial

def pausedAfter (state : State input) : Event → Bool
  | .pause => true
  | .resume => false
  | _ => state.assignmentPaused

def sealedAfter (state : State input) : Event → Bool
  | .installCheckpoint _ => true
  | _ => state.primarySealed

def fencedAfter (state : State input) : Event → Bool
  | .fencePrimary => true
  | _ => state.primaryFenced

def ownersAfter (state : State input) : Event → StatefulFailover.Owners
  | .switchRoute actor gateway => state.owners.set actor.leg gateway
  | _ => state.owners

def epochAfter (state : State input) : Event → Nat
  | .switchRoute .. => state.routeEpoch + 1
  | _ => state.routeEpoch

structure Frame (before after : State input) (event : Event) : Prop where
  connection : after.connection = before.connection
  authentication : after.authentication = before.authentication
  work : after.work = before.work
  custody : after.custody = before.custody
  outputs : after.outputs = before.outputs
  services : after.services = before.services
  receipts : after.receipts = before.receipts
  primary : after.primary = before.primary
  policy : ∀ gateway, (beforeService input after gateway).environment = (beforeService input before gateway).environment
  paused : after.assignmentPaused = pausedAfter before event
  sealed : after.primarySealed = sealedAfter before event
  fenced : after.primaryFenced = fencedAfter before event
  owners : after.owners = ownersAfter before event
  epoch : after.routeEpoch = epochAfter before event
  standby : (∀ ns, event ≠ .installCheckpoint ns) → after.standby = before.standby
  cache : event ≠ .stageCheckpoint → after.cache = before.cache
  checkpoints : event ≠ .stageCheckpoint → after.checkpoints = before.checkpoints
  installation : (∀ ns, event ≠ .installCheckpoint ns) → after.installation = before.installation

structure Quiet (effect : Effect input) : Prop where
  supported : effect.supported = true
  passed : effect.passed = true
  output : effect.output = none
  service : effect.service = none
  receipt : effect.receipt = none
  startup : effect.startup = none
  application : effect.application = none
  read : effect.read = []

structure Control (current : Cut input complete) (event : Event) (actual : Step input) where
  move : Move current actual
  eventEq : actual.event = event
  endpoints : move.after.endpoints = current.endpoints
  frame : Frame current.report.final move.after.report.final event
  quiet : Quiet actual.result

private theorem capture_enabled (history : Checkpoint.History gateway) (ready : CaptureReady gateway) :
    ∃ snapshot, Checkpoint.capture history = .ok snapshot := by
  obtain ⟨session, record, phase, member, entry, tcp⟩ := ready.selected
  cases found : gateway.tracker.records.find? (fun candidate => decide (candidate.entry = session.entry)) with
  | none => exact False.elim ((List.find?_eq_none.mp found) record member (decide_eq_true entry))
  | some chosen =>
    have same : chosen.entry = session.entry := of_decide_eq_true
      (List.find?_some (p := fun candidate : ConntrackLifecycle.Record => decide (candidate.entry = session.entry)) found)
    have chosenTCP : chosen.entry.flow.original.protocol = .tcp := by rw [same, ← entry]; exact tcp
    cases captured : Checkpoint.capture history with
    | ok snapshot => exact ⟨snapshot, rfl⟩
    | error reason =>
      unfold Checkpoint.capture at captured
      repeat' first
        | (split at captured)
        | (dsimp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at captured)
        | (cases captured)
      all_goals simp_all [Checkpoint.dataPhase, Admission.Phase.entry]

private theorem install_enabled (checkpoint : CachedCheckpoint) (state : State input)
    (source : state.primary.transport = checkpoint.snapshot.source)
    (cut : state.primary.history.length = checkpoint.snapshot.cut) (empty : state.standby.transport = Checkpoint.Gateway.initial) :
    ∃ copied, Checkpoint.install checkpoint.snapshot state.primary.history state.standby.transport = .ok copied := by
  have sourceSame : state.primary.transport.same checkpoint.snapshot.source = true := (Checkpoint.Gateway.same_correct _ _).mpr source
  have targetSame : state.standby.transport.same Checkpoint.Gateway.initial = true := (Checkpoint.Gateway.same_correct _ _).mpr empty
  unfold Checkpoint.install
  simp only [sourceSame, cut, targetSame, dite_true]
  exact ⟨_, rfl⟩

private theorem finish (before : State input) (event : Event) (effect : Effect input)
    (computed : processCore input before event = .ok effect) (custody : prepareCustody before event = .ok before.custody)
    (quiet : Quiet effect) :
    step input before event = .ok { effect with state := { effect.state with custody := before.custody, time := before.time + 1 } } := by
  simp only [step, process, computed, custody, bind, Except.bind, pure, Except.pure, finishCustody,
    quiet.output, quiet.service]

private def append (event : Event) (effect : Effect input) (computed : step input current.report.final event = .ok effect)
    (frame : Frame current.report.final effect.state event) (quiet : Quiet effect) :
    Control current event ⟨current.report.final, event, effect, computed⟩ := by
  let actual : Step input := ⟨current.report.final, event, effect, computed⟩
  let report := CampusTCPSchedule.Report.appendStep current.report current.supported current.finished actual rfl quiet.supported
  let next : Cut input complete := ⟨_, report, CampusTCPSchedule.Report.appendStep_supported _ _ _ _ _ _, rfl,
    current.endpoints, frame.connection.trans current.connection⟩
  exact ⟨⟨next, rfl, quiet.supported, quiet.passed, rfl, rfl⟩, rfl, rfl, frame, quiet⟩

private theorem core_at (event : Event) (effect : Effect input)
    (computed : processCore input current.report.final event = .ok effect)
    (custody : prepareCustody current.report.final event = .ok current.report.final.custody)
    (frame : Frame current.report.final effect.state event) (quiet : Quiet effect) :
    ∃ actual : Step input,
      actual.result = { effect with state := { effect.state with custody := current.report.final.custody, time := current.report.final.time + 1 } } ∧
      Nonempty (Control current event actual) := by
  let result : Effect input := { effect with state := { effect.state with custody := current.report.final.custody, time := current.report.final.time + 1 } }
  have checked : step input current.report.final event = .ok result := finish _ _ _ computed custody quiet
  have same : Frame current.report.final result.state event := {
    connection := frame.connection, authentication := frame.authentication, work := frame.work, custody := rfl
    outputs := frame.outputs, services := frame.services, receipts := frame.receipts, primary := frame.primary
    policy := frame.policy, paused := frame.paused, sealed := frame.sealed, fenced := frame.fenced
    owners := frame.owners, epoch := frame.epoch, standby := frame.standby, cache := frame.cache
    checkpoints := frame.checkpoints, installation := frame.installation }
  have silent : Quiet result := {
    supported := quiet.supported, passed := quiet.passed, output := quiet.output, service := quiet.service
    receipt := quiet.receipt, startup := quiet.startup, application := quiet.application, read := quiet.read }
  exact ⟨_, rfl, ⟨append event result checked same silent⟩⟩

theorem pause_at (ready : PauseReady current.report.final) :
    ∃ actual, Nonempty (Control current .pause actual) := by
  let effect : Effect input := { state := { current.report.final with assignmentPaused := true } }
  have computed : processCore input current.report.final .pause = .ok effect := by
    simp [processCore, transferControl, ready.configured, ready.unpaused, ready.unsealed, ready.unfenced, effect,
      pure, Except.pure]
  have frame : Frame current.report.final effect.state .pause := by
    constructor <;> try rfl
    all_goals first
      | (intro _; rfl)
      | (intro gateway; cases gateway <;> rfl)
  obtain ⟨actual, _, value⟩ := core_at .pause effect computed rfl frame (by constructor <;> rfl)
  exact ⟨actual, value⟩

theorem stage_at (ready : StageReady current.report.final) :
    ∃ actual checkpoint, Nonempty (Control current .stageCheckpoint actual) ∧ actual.result.checkpoint = some checkpoint := by
  obtain ⟨snapshot, captured⟩ := capture_enabled current.report.final.primary.history ready.capture
  let checkpoint : CachedCheckpoint := ⟨current.report.final.checkpoints.length, current.report.final.time, snapshot⟩
  let effect : Effect input := { state := { current.report.final with
    checkpoints := current.report.final.checkpoints ++ [checkpoint], cache := some checkpoint }, checkpoint := some checkpoint }
  have computed : processCore input current.report.final .stageCheckpoint = .ok effect := by
    simp [processCore, transferControl, ready.configured, ready.unsealed, ready.unfenced, current.connection, captured,
      checkpoint, effect, pure, Except.pure, Except.mapError, bind, Except.bind]
  have frame : Frame current.report.final effect.state .stageCheckpoint := by
    constructor <;> try rfl
    all_goals first
      | (intro _; rfl)
      | (intro gateway; cases gateway <;> rfl)
      | (intro impossible; exact False.elim (impossible rfl))
  obtain ⟨actual, result, value⟩ := core_at .stageCheckpoint effect computed rfl frame (by constructor <;> rfl)
  exact ⟨actual, checkpoint, value, by rw [result]⟩

theorem install_at (ready : InstallReady current.report.final) :
    ∃ actual installed, Nonempty (Control current (.installCheckpoint (input.deployment .standby).executionNS) actual) ∧
      actual.result.installation = some installed := by
  obtain ⟨checkpoint, cached, source, cut⟩ := ready.fresh
  obtain ⟨copied, installedEq⟩ := install_enabled checkpoint current.report.final source cut ready.empty
  let installed : InstalledCheckpoint := ⟨current.report.final.time, checkpoint, current.report.final.primary.transport,
    current.report.final.primary.history, current.report.final.standby.transport, copied, installedEq⟩
  let standby : Local := { current.report.final.standby with transport := copied.state, history := copied.history }
  let effect : Effect input := { state := { current.report.final with
    standby := standby, primarySealed := true, installation := some installed }, installation := some installed }
  have computed : processCore input current.report.final (.installCheckpoint (input.deployment .standby).executionNS) = .ok effect := by
    simp [processCore, transferControl, ready.configured, ready.paused, ready.unsealed, ready.unfenced, ready.drained,
      ready.namespaceEq, cached, effect, installed, standby, pure, Except.pure]
    split
    · rename_i reason failed
      rw [installedEq] at failed
      cases failed
    · rename_i actual succeeded
      have same : actual = copied := Except.ok.inj (succeeded.symm.trans installedEq)
      subst actual
      rfl
  have frame : Frame current.report.final effect.state (.installCheckpoint (input.deployment .standby).executionNS) := by
    constructor <;> try rfl
    all_goals first
      | (intro _; rfl)
      | (intro gateway; cases gateway <;> rfl)
      | (intro impossible; exact False.elim (impossible _ rfl))
  obtain ⟨actual, result, value⟩ := core_at (.installCheckpoint (input.deployment .standby).executionNS)
    effect computed rfl frame (by constructor <;> rfl)
  exact ⟨actual, installed, value, by rw [result]⟩

theorem route_at (ready : RouteReady current.report.final) (actor : Actor) :
    ∃ actual, Nonempty (Control current (.switchRoute actor .standby) actual) := by
  obtain ⟨installed, stored, source, target⟩ := ready.consistent
  have sourceSame : current.report.final.primary.transport.same installed.checkpoint.snapshot.source = true :=
    (Checkpoint.Gateway.same_correct _ _).mpr source
  have targetSame : current.report.final.standby.transport.same installed.installed.state = true :=
    (Checkpoint.Gateway.same_correct _ _).mpr target
  let effect : Effect input := { state := { current.report.final with
    owners := current.report.final.owners.set actor.leg .standby, routeEpoch := current.report.final.routeEpoch + 1 } }
  have computed : processCore input current.report.final (.switchRoute actor .standby) = .ok effect := by
    simp [processCore, transferControl, ready.configured, ready.paused, ready.sealed, stored, sourceSame, targetSame, effect,
      pure, Except.pure, bne, show (StatefulFailover.Gateway.standby == .standby) = true by rfl]
  have frame : Frame current.report.final effect.state (.switchRoute actor .standby) := by
    constructor <;> try rfl
    all_goals first
      | (intro _; rfl)
      | (intro gateway; cases gateway <;> rfl)
  obtain ⟨actual, _, value⟩ := core_at (.switchRoute actor .standby) effect computed rfl frame (by constructor <;> rfl)
  exact ⟨actual, value⟩

theorem fence_at (ready : FenceReady current.report.final) :
    ∃ actual, Nonempty (Control current .fencePrimary actual) := by
  have installed : current.report.final.installation.isNone = false := by
    have present := ready.installed
    cases selected : current.report.final.installation <;> simp_all
  let effect : Effect input := { state := { current.report.final with primaryFenced := true } }
  have computed : processCore input current.report.final .fencePrimary = .ok effect := by
    simp [processCore, transferControl, ready.configured, ready.paused, ready.sealed, installed, ready.client, ready.server,
      ready.drained, effect, pure, Except.pure, bne, show (StatefulFailover.Gateway.standby == .standby) = true by rfl]
  have frame : Frame current.report.final effect.state .fencePrimary := by
    constructor <;> try rfl
    all_goals first
      | (intro _; rfl)
      | (intro gateway; cases gateway <;> rfl)
  obtain ⟨actual, _, value⟩ := core_at .fencePrimary effect computed rfl frame (by constructor <;> rfl)
  exact ⟨actual, value⟩

theorem resume_at (ready : ResumeReady current.report.final) :
    ∃ actual, Nonempty (Control current .resume actual) := by
  obtain ⟨installed, stored, source, target⟩ := ready.consistent
  have sourceSame : current.report.final.primary.transport.same installed.checkpoint.snapshot.source = true :=
    (Checkpoint.Gateway.same_correct _ _).mpr source
  have targetSame : current.report.final.standby.transport.same installed.installed.state = true :=
    (Checkpoint.Gateway.same_correct _ _).mpr target
  let effect : Effect input := { state := { current.report.final with assignmentPaused := false } }
  have computed : processCore input current.report.final .resume = .ok effect := by
    simp [processCore, transferControl, ready.configured, ready.paused, ready.fenced, ready.client, ready.server,
      stored, sourceSame, targetSame, effect, pure, Except.pure, bne,
      show (StatefulFailover.Gateway.standby == .standby) = true by rfl]
  have frame : Frame current.report.final effect.state .resume := by
    constructor <;> try rfl
    all_goals first
      | (intro _; rfl)
      | (intro gateway; cases gateway <;> rfl)
  obtain ⟨actual, _, value⟩ := core_at .resume effect computed rfl frame (by constructor <;> rfl)
  exact ⟨actual, value⟩

end Netlib.Check.CampusTCPTransferEnabled
