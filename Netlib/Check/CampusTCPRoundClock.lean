import Netlib.Check.CampusTCPRoundLocal

/-!
# Actual same-clock slots in a campus round

Each wait appends a real checked endpoint operation.
Both endpoint states and all packet work stay fixed.
-/

namespace Netlib.Check.CampusTCPRoundClock

open CampusTCPModel CampusTCPEnabled Protocol.TCP

variable {input : Input}

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
    (endpoints : Applications complete) (actor : Actor) where
  actual : Step input
  beforeEq : actual.before = before
  eventEq : actual.event = .advanceClock actor (endpoint endpoints actor).now
  supported : actual.result.supported = true
  passed : actual.result.passed = true
  output : actual.result.output = none
  read : actual.result.read = []
  service : actual.result.service = none
  receipt : actual.result.receipt = none
  after : Applications complete
  stateEq : actual.result.state =
    { before with connection := .application complete after, time := before.time + 1 }
  selected : endpoint after actor = endpoint endpoints actor
  peer : endpoint after actor.other = endpoint endpoints actor.other
  operation : T.Step
  recorded : actual.result.application = some (actor, operation)
  localBefore : operation.before = endpoint endpoints actor
  localEvent : operation.event = .advanceClock (endpoint endpoints actor).now
  localStamp : operation.stamp = before.time
  selectedSteps : applicationSteps after actor = applicationSteps endpoints actor ++ [operation]
  peerSteps : applicationSteps after actor.other = applicationSteps endpoints actor.other

theorem same_clock_enabled (before : State input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : before.connection = .application complete endpoints)
    (actor : Actor) (earlier : ∀ old ∈ applicationSteps endpoints actor, old.stamp < before.time)
    (coherent : Endpoint.RecoveryCoherent (endpoint endpoints actor))
    (prepared : Endpoint.AckPrepared (endpoint endpoints actor))
    (runtime : (endpoint endpoints actor).recovery.isSome = true) :
    Nonempty (ClockStep before complete endpoints actor) := by
  let state := endpoint endpoints actor
  let event : T.Event := .advanceClock state.now
  let result : Endpoint.Result := ⟨state, .accepted .advanceClock, none, [], none⟩
  have evaluated : ApplicationTrace.evaluate state event = result :=
    CampusTCPRoundLocal.advance_same state (endpoint_valid endpoints actor) coherent prepared runtime
  obtain ⟨effect, computed, supported, output, read, recorded⟩ := application_quiet before complete endpoints
    connection actor event earlier result .advanceClock evaluated rfl rfl
  have frames := application_quiet_frame before actor event effect computed output
  let operation := ApplicationTrace.Step.make state (endpoint_valid endpoints actor) event before.time
  have localState : operation.result.state = state := congrArg Endpoint.Result.state evaluated
  obtain ⟨after, nextConnection, selected, peer, selectedSteps, peerSteps, localBefore, localEvent, localStamp⟩ :=
    application_frame before complete endpoints connection actor event effect operation computed recorded
  have core : processCore input before (.advanceClock actor state.now) = .ok effect := computed
  let actual : Step input := ⟨before, .advanceClock actor state.now,
    { effect with state := { effect.state with custody := before.custody, time := before.time + 1 } }, by
      simp only [step, process, core, prepareCustody, bind, Except.bind, pure, Except.pure,
        finishCustody, output, frames.2.2.1]⟩
  refine ⟨⟨actual, rfl, rfl, supported, frames.2.1, output, read, frames.2.2.1, frames.2.2.2,
    after, ?_, selected.trans localState, peer, operation, recorded, localBefore, localEvent, localStamp,
    selectedSteps, peerSteps⟩⟩
  change { effect.state with custody := before.custody, time := before.time + 1 } = _
  rw [frames.1, nextConnection]

theorem Report.same_clock_enabled (report : Report input events) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : report.final.connection = .application complete endpoints)
    (actor : Actor) (coherent : Endpoint.RecoveryCoherent (endpoint endpoints actor))
    (prepared : Endpoint.AckPrepared (endpoint endpoints actor))
    (runtime : (endpoint endpoints actor).recovery.isSome = true) :
    Nonempty (ClockStep report.final complete endpoints actor) := by
  apply CampusTCPRoundClock.same_clock_enabled report.final complete endpoints connection actor _ coherent prepared runtime
  have earlier := CampusTCPChronology.Report.application_before report complete endpoints connection
  cases actor
  · exact earlier.1
  · exact earlier.2

private theorem step_eq (left right : Step input) (before : left.before = right.before)
    (event : left.event = right.event) (result : left.result = right.result) : left = right := by
  cases left
  cases right
  simp_all only

theorem Step.same_clock (actual : Step input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : actual.before.connection = .application complete endpoints)
    (actor : Actor) (event : actual.event = .advanceClock actor (endpoint endpoints actor).now)
    (earlier : ∀ old ∈ applicationSteps endpoints actor, old.stamp < actual.before.time)
    (coherent : Endpoint.RecoveryCoherent (endpoint endpoints actor))
    (prepared : Endpoint.AckPrepared (endpoint endpoints actor))
    (runtime : (endpoint endpoints actor).recovery.isSome = true) :
    ∃ value : ClockStep actual.before complete endpoints actor, value.actual = actual := by
  obtain ⟨value⟩ := same_clock_enabled actual.before complete endpoints connection actor earlier coherent prepared runtime
  have sameResult : value.actual.result = actual.result := by
    have computed := value.actual.computed
    rw [value.beforeEq, value.eventEq, ← event, actual.computed] at computed
    exact (Except.ok.inj computed).symm
  have same : value.actual = actual := step_eq value.actual actual value.beforeEq
    (value.eventEq.trans event.symm) sameResult
  exact ⟨value, same⟩

def ClockStep.report (value : ClockStep before complete endpoints actor) (report : Report input events)
    (same : before = report.final) (supported : report.supported = true) (finished : report.remaining = []) :
    Report input (events ++ [value.actual.event]) :=
  CampusTCPSchedule.Report.appendStep report supported finished value.actual (value.beforeEq.trans same) value.supported

theorem ClockStep.report_supported (value : ClockStep before complete endpoints actor) (report : Report input events)
    (same : before = report.final) (supported : report.supported = true) (finished : report.remaining = []) :
    (value.report report same supported finished).supported = true :=
  CampusTCPSchedule.Report.appendStep_supported report supported finished value.actual
    (value.beforeEq.trans same) value.supported

private theorem write_connection (before : State input) (gateway : Gateway) (resident : Local) :
    (before.write gateway resident).connection = before.connection := by
  cases gateway <;> rfl

inductive NetworkAction : Event → Prop where
  | assign (index : Nat) (ingress : I.InterfaceRef) : NetworkAction (.assign index ingress)
  | serve (id : Nat) (observed : Option (List UInt8 × Option (List UInt8))) : NetworkAction (.serve id observed)

private theorem process_connection (before : State input) (event : Event) (effect : Effect input)
    (computed : processCore input before event = .ok effect) (network : NetworkAction event) :
    effect.state.connection = before.connection := by
  cases network
  all_goals
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed; rfl)
      | (solve | cases computed; exact write_connection before _ _)
      | (cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, Except.mapError, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)

theorem Step.connection_frame (actual : Step input) (network : NetworkAction actual.event) :
    actual.result.state.connection = actual.before.connection := by
  obtain ⟨effect, custody, computed, result⟩ := actual.processed
  have unchanged := process_connection actual.before actual.event effect computed network
  simpa only [result] using unchanged

end Netlib.Check.CampusTCPRoundClock
