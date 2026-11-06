import Netlib.Check.CampusTCPTwoProgressState
import Netlib.Check.CampusTCPTwoProgressSenderWindow
import Netlib.Check.CampusTCPRoundEndpointGuards
import Netlib.Check.CampusTCPRoundPhaseHistory

namespace Netlib.Check.CampusTCPTwoProgressRead

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPGapProgressPhaseBase (Anchor)
open CampusTCPTwoProgressStart (TwoWriteInitial)

namespace S
export CampusTCPTwoProgressSender (Original Flight)
end S
namespace R
export CampusTCPTwoProgressReceiver (Facts)
end R
namespace G
export CampusTCPTwoProgressGatewayState (View)
export CampusTCPTwoProgressGatewayWindow (Reserved)
end G

variable {input : Input} {complete : TCPHandshake.Completed input.active input.passive}
variable {cut current next : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {first : S.Original initial .lower} {second : S.Original initial .upper} {timeouts : Nat}

private theorem read_storage (state : Endpoint.State) (count : Nat)
    (storage : Endpoint.StorageCoherent state) : Endpoint.StorageCoherent (Endpoint.readState state count) := by
  have room : state.core.window ≤ (Endpoint.readState state count).core.window := by
    simp only [Endpoint.readState, EstablishedReceive.State.window, List.length_drop]
    omega
  refine ⟨Endpoint.readState_storage_valid state count storage.1, ?_⟩
  cases selected : state.ackReaction with
  | none => simp only [Endpoint.readState, selected, Option.map_none]
  | some reaction =>
    have before : reaction.advertisement.frontier = state.receiveStore.frontier ∧
        state.receiveStore.Valid (state.receiveStore.frontier + reaction.window) state.core.window := by
      simpa only [selected] using storage.2
    have after : state.receiveStore.Valid (state.receiveStore.frontier + reaction.window)
        (Endpoint.readState state count).core.window :=
      ReceiveStore.State.valid_mono state.receiveStore _ _ _ _ before.2 (Nat.le_refl _) room
        (Nat.le_trans before.2.2.1 room)
    have advertisement :
        (AckReaction.read reaction state.now state.core.receiveNext state.core.capacity
          state.core.window (Endpoint.readState state count).core.window state.effectiveMSS).advertisement =
            reaction.advertisement := by
      unfold AckReaction.read
      dsimp only
      split <;> rfl
    simp only [Endpoint.readState, selected, Option.map_some]
    change (AckReaction.read reaction state.now state.core.receiveNext state.core.capacity
      state.core.window (Endpoint.readState state count).core.window state.effectiveMSS).advertisement.frontier =
        state.receiveStore.frontier ∧
      state.receiveStore.Valid (state.receiveStore.frontier +
        (AckReaction.read reaction state.now state.core.receiveNext state.core.capacity
          state.core.window (Endpoint.readState state count).core.window state.effectiveMSS).window)
        (Endpoint.readState state count).core.window
    simpa only [AckReaction.State.window, advertisement] using And.intro before.1 after

structure ReceiverClosed (initial : TwoWriteInitial cut sender gateway lower upper) (state : Endpoint.State) where
  before : Endpoint.State
  facts : R.Facts initial before .allReleased
  frame : Endpoint.ClockFrame (Endpoint.readState before (lower ++ upper).length) state
  valid : state.Valid
  coherent : Endpoint.RecoveryCoherent state
  prepared : Endpoint.AckPrepared state
  storage : Endpoint.StorageCoherent state

variable {state after : Endpoint.State}

theorem ReceiverClosed.core (closed : ReceiverClosed initial state) :
    state.core = (Endpoint.readState closed.before (lower ++ upper).length).core := closed.frame.core

theorem ReceiverClosed.store (closed : ReceiverClosed initial state) :
    state.receiveStore = closed.before.receiveStore := closed.frame.receiveStore

theorem ReceiverClosed.pending (closed : ReceiverClosed initial state) : state.pending = closed.before.pending := closed.frame.pending

theorem ReceiverClosed.runtime (closed : ReceiverClosed initial state) :
    state.recovery = some { closed.facts.recovery with now := state.now } :=
  closed.frame.runtime closed.facts.runtime

theorem ReceiverClosed.recovery_fields (closed : ReceiverClosed initial state) :
    { closed.facts.recovery with now := state.now } = { initial.receiverState.idle.recovery with now := state.now } := by
  rw [closed.facts.recoveryState]

theorem ReceiverClosed.ackRuntime (closed : ReceiverClosed initial state) :
    state.ackReaction = some (AckReaction.read closed.facts.reaction closed.before.now closed.before.core.receiveNext
      closed.before.core.capacity closed.before.core.window
      (Endpoint.readState closed.before (lower ++ upper).length).core.window closed.before.effectiveMSS) := by
  rw [closed.frame.ackReaction]
  simp only [Endpoint.readState, closed.facts.ackRuntime, Option.map_some]

theorem ReceiverClosed.empty (closed : ReceiverClosed initial state) : state.core.received = [] := by
  rw [closed.core]
  simp only [Endpoint.readState, closed.facts.received, CampusTCPTwoProgressReceiver.Stage.bytes, List.drop_length]

theorem ReceiverClosed.held (closed : ReceiverClosed initial state) : state.receiveStore.held = [] := by
  rw [closed.store]
  exact closed.facts.empty_held (by decide)

theorem ReceiverClosed.frontier (closed : ReceiverClosed initial state) :
    state.receiveStore.frontier = (CampusTCPTwoProgressReceiver.source initial).receiveStore.frontier + (lower ++ upper).length := by
  rw [closed.store]
  exact closed.facts.frontier

theorem ReceiverClosed.nextID (closed : ReceiverClosed initial state) :
    state.receiveStore.nextID = (CampusTCPTwoProgressReceiver.source initial).receiveStore.nextID + 2 := by
  rw [closed.store]
  exact closed.facts.nextID

theorem ReceiverClosed.sendWindow_floor (closed : ReceiverClosed initial state) :
    CampusTCPTwoProgressReceiver.windowFloor initial ≤ state.sendWindow := by
  rw [closed.frame.sendWindow]
  exact closed.facts.sendWindowFloor

def ReceiverClosed.clock (closed : ReceiverClosed initial state) (frame : Endpoint.ClockFrame state after)
    (timely : Endpoint.AckTimeReady state after.now) : ReceiverClosed initial after where
  before := closed.before
  facts := closed.facts
  frame := closed.frame.trans frame
  valid := frame.valid closed.valid
  coherent := frame.recovery_coherent closed.coherent
  prepared := frame.ack_prepared closed.prepared timely
  storage := frame.storage_coherent closed.storage

structure Completed (initial : TwoWriteInitial cut sender gateway lower upper) (current : Cut input complete)
    (first : S.Original initial .lower) (second : S.Original initial .upper) (timeouts : Nat) where
  anchor : Anchor cut current
  reader : Step input
  member : reader ∈ current.report.steps
  event : reader.event = .read sender.other (lower ++ upper).length
  returned : reader.result.read = lower ++ upper
  operation : T.Step
  recorded : reader.result.application = some (sender.other, operation)
  readerBefore : Cut input complete
  beforeEq : reader.before = readerBefore.report.final
  localBefore : operation.before = endpoint readerBefore.endpoints sender.other
  localEvent : operation.event = .read (lower ++ upper).length
  localStamp : operation.stamp = reader.before.time
  localRead : operation.readBytes = lower ++ upper
  accepted : operation.result.decision = .accepted (.read (lower ++ upper).length)
  readerFacts : R.Facts initial operation.before .allReleased
  history : CampusTCPTwoProgressHistory.Complete cut current sender.other (lower ++ upper) operation
  senderFlight : S.Flight initial (endpoint current.endpoints sender) (.retired first second) timeouts
  receiver : ReceiverClosed initial (endpoint current.endpoints sender.other)
  receiverBefore : receiver.before = operation.before
  gatewayState : G.View initial current
  gatewayWindow : G.Reserved gatewayState

private theorem guards (flight : S.Flight initial (endpoint current.endpoints sender) (.retired first second) timeouts)
    (closed : ReceiverClosed initial (endpoint current.endpoints sender.other)) : CampusTCPRoundGuards.Guards current.endpoints := by
  intro actor
  by_cases selected : actor = sender
  · rw [selected]
    exact ⟨flight.coherent, flight.prepared, congrArg Option.isSome flight.runtime⟩
  · have peer : actor = sender.other := by cases actor <;> cases sender <;> simp_all [Actor.other]
    rw [peer]
    exact ⟨closed.coherent, closed.prepared, congrArg Option.isSome closed.runtime⟩

def Completed.clock (done : Completed initial current first second timeouts)
    (placement : CampusTCPRecoveryRoundPhaseBase.At current next)
    (senderTime : Endpoint.AckTimeReady (endpoint current.endpoints sender) (endpoint next.endpoints sender).now)
    (receiverTime : Endpoint.AckTimeReady (endpoint current.endpoints sender.other) (endpoint next.endpoints sender.other).now) :
    Completed initial next first second timeouts := by
  let flight := done.senderFlight.clock (placement.frame.endpointFrame sender) senderTime
  let receiver := done.receiver.clock (placement.frame.endpointFrame sender.other) receiverTime
  exact {
    anchor := ⟨guards flight receiver, done.anchor.retained.trans placement.retained,
      done.anchor.environment.trans placement.frame.environment.symm⟩
    reader := done.reader
    member := placement.retained.subset done.member
    event := done.event
    returned := done.returned
    operation := done.operation
    recorded := done.recorded
    readerBefore := done.readerBefore
    beforeEq := done.beforeEq
    localBefore := done.localBefore
    localEvent := done.localEvent
    localStamp := done.localStamp
    localRead := done.localRead
    accepted := done.accepted
    readerFacts := done.readerFacts
    history := done.history.clock placement
    senderFlight := flight
    receiver
    receiverBefore := done.receiverBefore
    gatewayState := done.gatewayState.reframe (placement.frame.beforeService gateway)
    gatewayWindow := done.gatewayWindow }

structure ReadMove (initial : TwoWriteInitial cut sender gateway lower upper) (current : Cut input complete)
    (first : S.Original initial .lower) (second : S.Original initial .upper) (timeouts : Nat) (actual : Step input) where
  move : Move current actual
  event : actual.event = .read sender.other (lower ++ upper).length
  operation : T.Step
  recorded : actual.result.application = some (sender.other, operation)
  localBefore : operation.before = endpoint current.endpoints sender.other
  localEvent : operation.event = .read (lower ++ upper).length
  localStamp : operation.stamp = current.report.final.time
  accepted : operation.result.decision = .accepted (.read (lower ++ upper).length)
  returned : actual.result.read = lower ++ upper
  localRead : operation.readBytes = lower ++ upper
  selected : endpoint move.after.endpoints sender.other = Endpoint.readState (endpoint current.endpoints sender.other) (lower ++ upper).length
  peer : endpoint move.after.endpoints sender = endpoint current.endpoints sender
  receiverSteps : applicationSteps move.after.endpoints sender.other = applicationSteps current.endpoints sender.other ++ [operation]
  gateway : ∀ selected, beforeService input move.after.report.final selected = beforeService input current.report.final selected
  environment : CampusTCPRoundEnvironment.environment current.report.final = CampusTCPRoundEnvironment.environment move.after.report.final
  completed : Completed initial move.after first second timeouts
  completedReader : completed.reader = actual
  completedOperation : completed.operation = operation

theorem read_at (live : CampusTCPTwoProgressState.Live initial current (.retired first second) timeouts .allReleased) :
    ∃ actual : Step input, Nonempty (ReadMove initial current first second timeouts actual) := by
  have payload : (endpoint current.endpoints sender.other).core.received = lower ++ upper := live.receiverFacts.received
  have fits : (lower ++ upper).length ≤ (endpoint current.endpoints sender.other).core.received.length := by
    rw [payload]
    exact Nat.le_refl _
  have earlier : ∀ old ∈ applicationSteps current.endpoints sender.other, old.stamp < current.report.final.time := by
    have clocks := CampusTCPChronology.Report.application_before current.report complete current.endpoints current.connection
    cases sender
    · exact clocks.2
    · exact clocks.1
  obtain ⟨effect, computed, supported, _, returned, application⟩ := read_enabled current.report.final complete
    current.endpoints current.connection sender.other (lower ++ upper).length earlier fits
  let actual : Step input := ⟨_, _, effect, computed⟩
  let operation := ApplicationTrace.Step.make (endpoint current.endpoints sender.other) (endpoint_valid current.endpoints sender.other)
    (.read (lower ++ upper).length) current.report.final.time
  have recorded : actual.result.application = some (sender.other, operation) := application
  obtain ⟨appended⟩ := current.appendLocal actual rfl supported sender.other (.read (lower ++ upper).length)
    (.read (lower ++ upper).length) operation recorded
  have passed := CampusTCPRoundLocal.step_local_passed actual sender.other (.read (lower ++ upper).length) (.read _)
  let move : Move current actual := ⟨appended.next, rfl, supported, passed, appended.history, appended.final⟩
  have evaluated : operation.result =
      ⟨Endpoint.readState (endpoint current.endpoints sender.other) (lower ++ upper).length,
        .accepted (.read (lower ++ upper).length), none, lower ++ upper, none⟩ := by
    change Endpoint.read (endpoint current.endpoints sender.other) (lower ++ upper).length = _
    simpa only [payload, List.take_length] using Endpoint.read_of_fits _ _ (endpoint_valid _ _) fits
  have selected : endpoint move.after.endpoints sender.other =
      Endpoint.readState (endpoint current.endpoints sender.other) (lower ++ upper).length :=
    appended.selected.trans (congrArg Endpoint.Result.state evaluated)
  have other : sender.other.other = sender := by cases sender <;> rfl
  have peer : endpoint move.after.endpoints sender = endpoint current.endpoints sender := by
    simpa only [other] using appended.peer
  have read : actual.result.read = lower ++ upper := by simpa only [payload, List.take_length] using returned
  have environment : CampusTCPRoundEnvironment.environment current.report.final =
      CampusTCPRoundEnvironment.environment move.after.report.final := by
    rw [move.final]
    exact CampusTCPRoundEnvironment.Step.environment actual trivial
  have guarded := (live.anchor.guards sender.other).readState (lower ++ upper).length live.receiverFacts.valid fits
  let receiver : ReceiverClosed initial (endpoint move.after.endpoints sender.other) := {
    before := endpoint current.endpoints sender.other
    facts := live.receiverFacts
    frame := by rw [selected]; exact Endpoint.ClockFrame.refl _
    valid := by rw [selected]; exact Endpoint.readState_valid _ _ live.receiverFacts.valid
    coherent := by rw [selected]; exact guarded.recoveryCoherent
    prepared := by rw [selected]; exact guarded.prepared
    storage := by rw [selected]; exact read_storage _ _ live.receiverFacts.storage }
  have flight : S.Flight initial (endpoint move.after.endpoints sender) (.retired first second) timeouts := by
    rw [peer]
    exact live.senderFlight
  have receiverSteps : applicationSteps move.after.endpoints sender.other =
      applicationSteps current.endpoints sender.other ++ [operation] := by
    simpa only [ite_true] using CampusTCPRoundPhaseHistory.Move.local_history move sender.other
      (.read (lower ++ upper).length) (.read _) operation recorded sender.other
  have gatewayFrame (selected) : beforeService input move.after.report.final selected = beforeService input current.report.final selected := by
    rw [move.final]
    exact CampusTCPRoundLocal.step_service_nonservice actual trivial selected
  have nonempty : lower ++ upper ≠ [] := by
    intro empty
    have length := congrArg List.length empty
    have positive := List.length_pos_iff.mpr initial.lowerNonempty
    simp only [List.length_append, List.length_nil] at length
    omega
  let done : Completed initial move.after first second timeouts := {
    anchor := ⟨guards flight receiver, live.anchor.retained.trans move.retained, live.anchor.environment.trans environment⟩
    reader := actual
    member := move.member
    event := rfl
    returned := read
    operation
    recorded
    readerBefore := current
    beforeEq := rfl
    localBefore := rfl
    localEvent := rfl
    localStamp := rfl
    localRead := congrArg Endpoint.Result.read evaluated
    accepted := congrArg Endpoint.Result.decision evaluated
    readerFacts := live.receiverFacts
    history := live.history.read operation receiverSteps nonempty rfl (congrArg Endpoint.Result.read evaluated)
    senderFlight := flight
    receiver
    receiverBefore := rfl
    gatewayState := live.gatewayState.reframe (gatewayFrame gateway)
    gatewayWindow := live.gatewayWindow }
  exact ⟨actual, ⟨{
    move
    event := rfl
    operation
    recorded
    localBefore := rfl
    localEvent := rfl
    localStamp := rfl
    accepted := congrArg Endpoint.Result.decision evaluated
    returned := read
    localRead := congrArg Endpoint.Result.read evaluated
    selected
    peer
    receiverSteps
    gateway := gatewayFrame
    environment
    completed := done
    completedReader := rfl
    completedOperation := rfl }⟩⟩

theorem ReadMove.step_eq {chosen : Step input} (read : ReadMove initial current first second timeouts chosen)
    (actual : Step input) (before : actual.before = current.report.final)
    (event : actual.event = .read sender.other (lower ++ upper).length) : chosen = actual :=
  CampusTCPRoundPhaseBase.Step.eq_of_before_event chosen actual
    (read.move.beforeEq.trans before.symm) (read.event.trans event.symm)

theorem ReadMove.sender_reserved {actual : Step input} (read : ReadMove initial current first second timeouts actual)
    (space : CampusTCPTwoProgressSenderWindow.Reserved initial (endpoint current.endpoints sender) (.retired first second)) :
    CampusTCPTwoProgressSenderWindow.Reserved initial (endpoint read.move.after.endpoints sender) (.retired first second) := by
  rw [read.peer]
  exact space

end Netlib.Check.CampusTCPTwoProgressRead
