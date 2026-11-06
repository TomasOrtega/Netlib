import Netlib.Check.CampusTCPRoundClock
import Netlib.Check.CampusTCPRoundStutter
import Netlib.Protocol.TCP.EndpointClockEnabled

/-!
# Actual advancing clocks in a campus TCP history

Each accepted clock operation retains the current recovery ledger and sets its time.
Packet work, gateway state, and the peer endpoint stay fixed.
-/

namespace Netlib.Check.CampusTCPTimedClock

open CampusTCPModel CampusTCPEnabled Protocol.TCP

variable {input : Input} {events : List Event}
variable {complete : H.Completed input.active input.passive}
variable {before middle after : State input}
variable {endpoints next last : Applications complete}

structure Frame (before : State input) (endpoints : Applications complete)
    (after : State input) (updated : Applications complete) : Prop where
  beforeConnection : before.connection = .application complete endpoints
  afterConnection : after.connection = .application complete updated
  fixed : CampusTCPRoundStutter.snapshot before = CampusTCPRoundStutter.snapshot after
  endpointFrame : ∀ actor, Endpoint.ClockFrame (endpoint endpoints actor) (endpoint updated actor)
  history : ∀ actor, applicationSteps endpoints actor <+: applicationSteps updated actor
  slot : before.time ≤ after.time

theorem Frame.refl (state : State input) (endpoints : Applications complete)
    (connection : state.connection = .application complete endpoints) : Frame state endpoints state endpoints :=
  ⟨connection, connection, rfl, fun actor => Endpoint.ClockFrame.refl (endpoint endpoints actor),
    fun _ => List.prefix_refl _, Nat.le_refl _⟩

theorem Frame.trans (first : Frame before endpoints middle next) (second : Frame middle next after last) :
    Frame before endpoints after last :=
  ⟨first.beforeConnection, second.afterConnection, first.fixed.trans second.fixed,
    fun actor => (first.endpointFrame actor).trans (second.endpointFrame actor),
    fun actor => (first.history actor).trans (second.history actor), Nat.le_trans first.slot second.slot⟩

theorem Frame.work (frame : Frame before endpoints after next) : after.work = before.work :=
  (congrArg State.work frame.fixed).symm

theorem Frame.outputs (frame : Frame before endpoints after next) : after.outputs = before.outputs :=
  (congrArg State.outputs frame.fixed).symm

theorem Frame.services (frame : Frame before endpoints after next) : after.services = before.services :=
  (congrArg State.services frame.fixed).symm

theorem Frame.receipts (frame : Frame before endpoints after next) : after.receipts = before.receipts :=
  (congrArg State.receipts frame.fixed).symm

theorem Frame.custody (frame : Frame before endpoints after next) : after.custody = before.custody :=
  (congrArg State.custody frame.fixed).symm

theorem Frame.primary (frame : Frame before endpoints after next) : after.primary = before.primary :=
  (congrArg State.primary frame.fixed).symm

theorem Frame.standby (frame : Frame before endpoints after next) : after.standby = before.standby :=
  (congrArg State.standby frame.fixed).symm

theorem Frame.authentication (frame : Frame before endpoints after next) : after.authentication = before.authentication :=
  (congrArg State.authentication frame.fixed).symm

theorem Frame.owners (frame : Frame before endpoints after next) : after.owners = before.owners :=
  (congrArg State.owners frame.fixed).symm

theorem Frame.routeEpoch (frame : Frame before endpoints after next) : after.routeEpoch = before.routeEpoch :=
  (congrArg State.routeEpoch frame.fixed).symm

theorem Frame.assignmentPaused (frame : Frame before endpoints after next) : after.assignmentPaused = before.assignmentPaused :=
  (congrArg State.assignmentPaused frame.fixed).symm

theorem Frame.primarySealed (frame : Frame before endpoints after next) : after.primarySealed = before.primarySealed :=
  (congrArg State.primarySealed frame.fixed).symm

theorem Frame.primaryFenced (frame : Frame before endpoints after next) : after.primaryFenced = before.primaryFenced :=
  (congrArg State.primaryFenced frame.fixed).symm

theorem Frame.checkpoints (frame : Frame before endpoints after next) : after.checkpoints = before.checkpoints :=
  (congrArg State.checkpoints frame.fixed).symm

theorem Frame.cache (frame : Frame before endpoints after next) : after.cache = before.cache :=
  (congrArg State.cache frame.fixed).symm

theorem Frame.installation (frame : Frame before endpoints after next) : after.installation = before.installation :=
  (congrArg State.installation frame.fixed).symm

theorem Frame.resident (frame : Frame before endpoints after next) (gateway : Gateway) :
    after.resident gateway = before.resident gateway := by
  cases gateway
  · exact frame.primary
  · exact frame.standby

theorem Frame.beforeService (frame : Frame before endpoints after next) (gateway : Gateway) :
    CampusTCPModel.beforeService input after gateway = CampusTCPModel.beforeService input before gateway :=
  (congrArg (fun state => CampusTCPModel.beforeService input state gateway) frame.fixed).symm

theorem Frame.environment (frame : Frame before endpoints after next) :
    CampusTCPRoundEnvironment.environment after = CampusTCPRoundEnvironment.environment before :=
  (congrArg CampusTCPRoundEnvironment.environment frame.fixed).symm

private theorem application_quiet_frame (before : State input) (actor : Actor) (event : T.Event)
    (effect : Effect input) (computed : applyApplication input before actor event = .ok effect)
    (quiet : effect.output = none) :
    effect.state = { before with connection := effect.state.connection } ∧ effect.passed = true ∧
      effect.service = none ∧ effect.receipt = none := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; exact ⟨rfl, rfl, rfl, rfl⟩)
    | (solve | cases computed; cases quiet)
    | (cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

structure ClockStep (before : State input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (actor : Actor) (millis : Nat) where
  actual : Step input
  beforeEq : actual.before = before
  eventEq : actual.event = .advanceClock actor millis
  supported : actual.result.supported = true
  passed : actual.result.passed = true
  output : actual.result.output = none
  read : actual.result.read = []
  service : actual.result.service = none
  receipt : actual.result.receipt = none
  after : Applications complete
  stateEq : actual.result.state =
    { before with connection := .application complete after, time := before.time + 1 }
  selected : endpoint after actor = Endpoint.clockState (endpoint endpoints actor) millis
  selectedFrame : Endpoint.ClockFrame (endpoint endpoints actor) (endpoint after actor)
  selectedNow : (endpoint after actor).now = millis
  selectedCoherent : Endpoint.RecoveryCoherent (endpoint after actor)
  selectedPrepared : Endpoint.AckPrepared (endpoint after actor)
  peer : endpoint after actor.other = endpoint endpoints actor.other
  operation : T.Step
  recorded : actual.result.application = some (actor, operation)
  localBefore : operation.before = endpoint endpoints actor
  localEvent : operation.event = .advanceClock millis
  localStamp : operation.stamp = before.time
  selectedSteps : applicationSteps after actor = applicationSteps endpoints actor ++ [operation]
  peerSteps : applicationSteps after actor.other = applicationSteps endpoints actor.other

theorem clock_enabled (before : State input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : before.connection = .application complete endpoints)
    (actor : Actor) (millis : Nat)
    (earlier : ∀ old ∈ applicationSteps endpoints actor, old.stamp < before.time)
    (coherent : Endpoint.RecoveryCoherent (endpoint endpoints actor))
    (prepared : Endpoint.AckPrepared (endpoint endpoints actor))
    (recovery : Recovery.State) (runtime : (endpoint endpoints actor).recovery = some recovery)
    (monotone : recovery.now ≤ millis) (timely : Endpoint.AckTimeReady (endpoint endpoints actor) millis) :
    Nonempty (ClockStep before complete endpoints actor millis) := by
  let state := endpoint endpoints actor
  let event : T.Event := .advanceClock millis
  let result : Endpoint.Result := ⟨Endpoint.clockState state millis, .accepted .advanceClock, none, [], none⟩
  have evaluated : ApplicationTrace.evaluate state event = result :=
    Endpoint.advanceClock_of_monotone state millis (endpoint_valid endpoints actor) coherent runtime monotone timely
  obtain ⟨effect, computed, supported, output, read, recorded⟩ := application_quiet before complete endpoints
    connection actor event earlier result .advanceClock evaluated rfl rfl
  have frames := application_quiet_frame before actor event effect computed output
  let operation := ApplicationTrace.Step.make state (endpoint_valid endpoints actor) event before.time
  have localState : operation.result.state = Endpoint.clockState state millis := congrArg Endpoint.Result.state evaluated
  obtain ⟨after, nextConnection, selected, peer, selectedSteps, peerSteps, localBefore, localEvent, localStamp⟩ :=
    application_frame before complete endpoints connection actor event effect operation computed recorded
  have core : processCore input before (.advanceClock actor millis) = .ok effect := computed
  let actual : Step input := ⟨before, .advanceClock actor millis,
    { effect with state := { effect.state with custody := before.custody, time := before.time + 1 } }, by
      simp only [step, process, core, prepareCustody, bind, Except.bind, pure, Except.pure,
        finishCustody, output, frames.2.2.1]⟩
  have endpointEq : endpoint after actor = Endpoint.clockState state millis := selected.trans localState
  have clockFrame : Endpoint.ClockFrame state (endpoint after actor) := by
    rw [endpointEq]
    exact Endpoint.clockState_frame state millis runtime monotone
  have now : (endpoint after actor).now = millis := by rw [endpointEq]; exact Endpoint.clockState_now _ _ runtime
  refine ⟨⟨actual, rfl, rfl, supported, frames.2.1, output, read, frames.2.2.1, frames.2.2.2,
    after, ?_, endpointEq, clockFrame, now, clockFrame.recovery_coherent coherent,
    clockFrame.ack_prepared prepared (by simpa only [now] using timely), peer,
    operation, recorded, localBefore, localEvent, localStamp, selectedSteps, peerSteps⟩⟩
  change { effect.state with custody := before.custody, time := before.time + 1 } = _
  rw [frames.1, nextConnection]

theorem Report.clock_enabled (report : Report input events) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : report.final.connection = .application complete endpoints)
    (actor : Actor) (millis : Nat)
    (coherent : Endpoint.RecoveryCoherent (endpoint endpoints actor))
    (prepared : Endpoint.AckPrepared (endpoint endpoints actor))
    (recovery : Recovery.State) (runtime : (endpoint endpoints actor).recovery = some recovery)
    (monotone : recovery.now ≤ millis) (timely : Endpoint.AckTimeReady (endpoint endpoints actor) millis) :
    Nonempty (ClockStep report.final complete endpoints actor millis) := by
  apply CampusTCPTimedClock.clock_enabled report.final complete endpoints connection actor millis _ coherent prepared recovery runtime monotone timely
  have earlier := CampusTCPChronology.Report.application_before report complete endpoints connection
  cases actor
  · exact earlier.1
  · exact earlier.2

theorem ClockStep.frame (value : ClockStep before complete endpoints actor millis)
    (connection : before.connection = .application complete endpoints) :
    Frame before endpoints value.actual.result.state value.after := by
  refine ⟨connection, ?_, ?_, ?_, ?_, ?_⟩
  · rw [value.stateEq]
  · rw [value.stateEq]
    rfl
  · intro receiver
    by_cases selected : receiver = actor
    · subst receiver
      exact value.selectedFrame
    · have peer : receiver = actor.other := by cases receiver <;> cases actor <;> simp_all [Actor.other]
      rw [peer, value.peer]
      exact Endpoint.ClockFrame.refl _
  · intro receiver
    by_cases selected : receiver = actor
    · subst receiver
      rw [value.selectedSteps]
      exact List.prefix_append _ _
    · have peer : receiver = actor.other := by cases receiver <;> cases actor <;> simp_all [Actor.other]
      rw [peer, value.peerSteps]
      exact List.prefix_refl _
  · rw [value.stateEq]
    exact Nat.le_add_right _ _

def ClockStep.report (value : ClockStep before complete endpoints actor millis) (report : Report input events)
    (same : before = report.final) (supported : report.supported = true) (finished : report.remaining = []) :
    Report input (events ++ [value.actual.event]) :=
  CampusTCPSchedule.Report.appendStep report supported finished value.actual (value.beforeEq.trans same) value.supported

theorem ClockStep.report_supported (value : ClockStep before complete endpoints actor millis) (report : Report input events)
    (same : before = report.final) (supported : report.supported = true) (finished : report.remaining = []) :
    (value.report report same supported finished).supported = true :=
  CampusTCPSchedule.Report.appendStep_supported report supported finished value.actual
    (value.beforeEq.trans same) value.supported

private theorem step_eq (left right : Step input) (before : left.before = right.before)
    (event : left.event = right.event) (result : left.result = right.result) : left = right := by
  cases left
  cases right
  simp_all only

theorem Step.clock (actual : Step input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : actual.before.connection = .application complete endpoints)
    (actor : Actor) (millis : Nat) (event : actual.event = .advanceClock actor millis)
    (earlier : ∀ old ∈ applicationSteps endpoints actor, old.stamp < actual.before.time)
    (coherent : Endpoint.RecoveryCoherent (endpoint endpoints actor))
    (prepared : Endpoint.AckPrepared (endpoint endpoints actor))
    (recovery : Recovery.State) (runtime : (endpoint endpoints actor).recovery = some recovery)
    (monotone : recovery.now ≤ millis) (timely : Endpoint.AckTimeReady (endpoint endpoints actor) millis) :
    ∃ value : ClockStep actual.before complete endpoints actor millis, value.actual = actual := by
  obtain ⟨value⟩ := clock_enabled actual.before complete endpoints connection actor millis earlier
    coherent prepared recovery runtime monotone timely
  have sameResult : value.actual.result = actual.result := by
    have computed := value.actual.computed
    rw [value.beforeEq, value.eventEq, ← event, actual.computed] at computed
    exact (Except.ok.inj computed).symm
  exact ⟨value, step_eq value.actual actual value.beforeEq (value.eventEq.trans event.symm) sameResult⟩

theorem Step.frame (actual : Step input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : actual.before.connection = .application complete endpoints)
    (actor : Actor) (millis : Nat) (event : actual.event = .advanceClock actor millis)
    (earlier : ∀ old ∈ applicationSteps endpoints actor, old.stamp < actual.before.time)
    (coherent : Endpoint.RecoveryCoherent (endpoint endpoints actor))
    (prepared : Endpoint.AckPrepared (endpoint endpoints actor))
    (recovery : Recovery.State) (runtime : (endpoint endpoints actor).recovery = some recovery)
    (monotone : recovery.now ≤ millis) (timely : Endpoint.AckTimeReady (endpoint endpoints actor) millis) :
    ∃ updated : Applications complete, Frame actual.before endpoints actual.result.state updated := by
  obtain ⟨value, same⟩ := Step.clock actual complete endpoints connection actor millis event earlier
    coherent prepared recovery runtime monotone timely
  refine ⟨value.after, ?_⟩
  simpa only [same] using value.frame connection

structure ClockAppend (report : Report input events) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (actual : Step input) (actor : Actor) (millis : Nat) where
  next : Report input (events ++ [actual.event])
  supported : next.supported = true
  finished : next.remaining = []
  history : next.steps = report.steps ++ [actual]
  final : next.final = actual.result.state
  clock : ClockStep report.final complete endpoints actor millis
  actualEq : clock.actual = actual
  frame : Frame report.final endpoints next.final clock.after

theorem Report.append_clock (report : Report input events) (supported : report.supported = true)
    (finished : report.remaining = []) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : report.final.connection = .application complete endpoints)
    (actual : Step input) (before : actual.before = report.final)
    (actor : Actor) (millis : Nat) (event : actual.event = .advanceClock actor millis)
    (coherent : Endpoint.RecoveryCoherent (endpoint endpoints actor))
    (prepared : Endpoint.AckPrepared (endpoint endpoints actor))
    (recovery : Recovery.State) (runtime : (endpoint endpoints actor).recovery = some recovery)
    (monotone : recovery.now ≤ millis) (timely : Endpoint.AckTimeReady (endpoint endpoints actor) millis) :
    Nonempty (ClockAppend report complete endpoints actual actor millis) := by
  obtain ⟨value⟩ := Report.clock_enabled report complete endpoints connection actor millis
    coherent prepared recovery runtime monotone timely
  have sameResult : value.actual.result = actual.result := by
    have computed := value.actual.computed
    simp only [value.beforeEq, value.eventEq] at computed
    have selected := actual.computed
    rw [before, event] at selected
    exact Except.ok.inj (computed.symm.trans selected)
  have same : value.actual = actual :=
    step_eq value.actual actual (value.beforeEq.trans before.symm) (value.eventEq.trans event.symm) sameResult
  let next := CampusTCPSchedule.Report.appendStep report supported finished actual before (same ▸ value.supported)
  refine ⟨⟨next, CampusTCPSchedule.Report.appendStep_supported _ _ _ _ _ _, rfl, rfl, rfl, value, same, ?_⟩⟩
  change Frame report.final endpoints actual.result.state value.after
  simpa only [same] using value.frame connection

end Netlib.Check.CampusTCPTimedClock
