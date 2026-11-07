import Netlib.Check.CampusTCPTwoTransferLocatedCore
import Netlib.Check.CampusTCPTwoProgressRead
import Netlib.Check.CampusTCPTwoTransferAccounting
import Netlib.Check.CampusTCPTwoTransferControlObserve

/-!
# Actual forward read at the current gateway location

Completion retains the pre-read core and its selected source history.
The post-read receiver uses a closed-store predicate.
-/

namespace Netlib.Check.CampusTCPTwoTransferLocatedRead

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart (TwoWriteInitial)
open CampusTCPTwoTransferState (LiveAt AnchorAt)
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoProgressRead (ReceiverClosed)

namespace S
export CampusTCPTwoProgressSender (Original Flight)
end S
namespace L
export CampusTCPTwoProgressMonitor (Monitor Allowed observe nextDemand)
end L
namespace W
export CampusTCPTwoTransferMonitor (Monitor Allowed observe)
end W

variable {input : Input} {complete : TCPHandshake.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {first : S.Original initial .lower} {second : S.Original initial .upper} {timeouts : Nat}
variable {actual : Step input}

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

private theorem guards (flight : S.Flight initial (endpoint current.endpoints sender) (.retired first second) timeouts)
    (closed : ReceiverClosed initial (endpoint current.endpoints sender.other)) : CampusTCPRoundGuards.Guards current.endpoints := by
  intro actor
  by_cases selected : actor = sender
  · rw [selected]
    exact ⟨flight.coherent, flight.prepared, congrArg Option.isSome flight.runtime⟩
  · have peer : actor = sender.other := by cases actor <;> cases sender <;> simp_all [Actor.other]
    rw [peer]
    exact ⟨closed.coherent, closed.prepared, congrArg Option.isSome closed.runtime⟩


structure ReadMove (initial : TwoWriteInitial cut sender gateway lower upper) (current : Cut input complete)
    (location : Gateway) (first : S.Original initial .lower) (second : S.Original initial .upper)
    (timeouts : Nat) (actual : Step input) where
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
  anchor : AnchorAt cut move.after
  history : CampusTCPTwoProgressHistory.Complete cut move.after sender.other (lower ++ upper) operation
  senderFlight : S.Flight initial (endpoint move.after.endpoints sender) (.retired first second) timeouts
  receiver : ReceiverClosed initial (endpoint move.after.endpoints sender.other)
  receiverBefore : receiver.before = endpoint current.endpoints sender.other

theorem read_move_at (live : LiveAt initial current location (.retired first second) timeouts .allReleased) :
    ∃ actual, Nonempty (ReadMove initial current location first second timeouts actual) := by
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
  let anchor : AnchorAt cut move.after :=
    ⟨⟨live.anchor.retained.trans move.retained, fun selected => (live.anchor.policy selected).trans
      (congrArg CampusTCPService.Before.environment (gatewayFrame selected)).symm⟩, guards flight receiver⟩
  exact ⟨actual, ⟨{
    move, event := rfl, operation, recorded, localBefore := rfl, localEvent := rfl, localStamp := rfl
    accepted := congrArg Endpoint.Result.decision evaluated
    returned := read
    localRead := congrArg Endpoint.Result.read evaluated
    selected, peer, receiverSteps, gateway := gatewayFrame, environment, anchor
    history := live.history.read operation receiverSteps nonempty rfl (congrArg Endpoint.Result.read evaluated)
    senderFlight := flight, receiver, receiverBefore := rfl }⟩⟩

variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8} {monitor : W.Monitor}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

private theorem local_read_allowed (mode : monitor.exchange.forward.mode = .needRead) :
    L.Allowed ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward
      (.read sender.other (lower ++ upper).length) := by
  apply (CampusTCPTwoProgressMonitorFacts.allowed_iff _ _ _ _).mpr
  refine ⟨by rw [mode]; decide, .inl ⟨.single (.operation (.read sender.other (lower ++ upper).length)), ?_, ?_⟩, rfl⟩
  · rw [L.nextDemand, mode]
    rfl
  · exact (CampusTCPTwoProgressMonitorFacts.serves_operation _ _).mpr rfl

private theorem read_allowed (finished : monitor.mode = .finished) (forward : monitor.exchange.mode = .forward)
    (mode : monitor.exchange.forward.mode = .needRead) :
    W.Allowed cfg current.report.final monitor (.read sender.other (lower ++ upper).length) := by
  have noDrain := CampusTCPTwoTransferControlObserve.noDrain_of_non_capture current.report.final monitor
    (by rw [finished]; decide)
  have control : CampusTCPTwoTransferMonitor.controlDemand monitor = none := by
    rw [CampusTCPTwoTransferMonitor.controlDemand, finished]
  have valid : monitor.mode ≠ .invalid := by rw [finished]; decide
  rw [W.Allowed, CampusTCPTwoTransferMonitor.allowed,
    ite_eq_right (by simpa only [decide_eq_true_eq] using valid), noDrain, control]
  simpa only [CampusTCPTwoExchangeMonitor.allowed, forward, L.Allowed] using local_read_allowed (checks := checks) (routing := routing)
    (quantum := quantum) (allowance := allowance) (reverseLower := reverseLower) (reverseUpper := reverseUpper) mode

def afterRead (monitor : W.Monitor) (stamp : Nat) (bytes : List UInt8) : W.Monitor :=
  { monitor with exchange := { monitor.exchange with
    mode := .needWrite
    forward := { monitor.exchange.forward with mode := .done, waiting := false, readStamp := some stamp, readBytes := bytes }
    slots := monitor.exchange.slots + 1
    forwardReadSlot := some monitor.exchange.slots } }

private theorem observe_read (value : ReadMove initial current location first second timeouts actual)
    (finished : monitor.mode = .finished) (forward : monitor.exchange.mode = .forward)
    (mode : monitor.exchange.forward.mode = .needRead) :
    W.observe cfg monitor actual = afterRead monitor value.operation.stamp (lower ++ upper) := by
  have allowed : W.Allowed cfg current.report.final monitor actual.event := by rw [value.event]; exact read_allowed finished forward mode
  have localAllowed : L.Allowed ((cfg).at actual.before).forward actual.before monitor.exchange.forward actual.event := by
    rw [value.move.beforeEq, value.event]
    exact local_read_allowed mode
  have localStep : L.observe ((cfg).at actual.before).forward monitor.exchange.forward actual =
      { monitor.exchange.forward with
        mode := .done
        waiting := false
        readStamp := some value.operation.stamp
        readBytes := lower ++ upper } := by
    rw [CampusTCPTwoProgressMonitorFacts.observe_action _ _ _ value.move.supported value.move.passed localAllowed
      (.read sender.other (lower ++ upper).length) value.event]
    have actor : (sender.other == sender.other) = true := by cases sender <;> rfl
    simp only [CampusTCPTwoProgressMonitor.observeOrdinary, mode, CampusTCPTwoProgressMonitor.observeRead,
      value.recorded, value.returned, config, CampusTCPTwoTransferMonitor.Config.at,
      CampusTCPTwoExchangeSetup.config, CampusTCPTwoProgressSetup.config, CampusTCPTwoTransferNative.Checks.monitorConfig,
      actor, beq_self_eq_true, Bool.and_self, ite_true]
  have exchangeAllowed : CampusTCPTwoExchangeMonitor.allowed ((cfg).at actual.before) actual.before monitor.exchange actual.event = true := by
    simpa only [CampusTCPTwoExchangeMonitor.allowed, forward, L.Allowed] using localAllowed
  have exchangeChecked : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoExchangeMonitor.allowed ((cfg).at actual.before) actual.before monitor.exchange actual.event) = true := by
    rw [value.move.supported, value.move.passed]
    exact exchangeAllowed
  have exchangeStep : CampusTCPTwoExchangeMonitor.observe ((cfg).at actual.before) monitor.exchange actual =
      (afterRead monitor value.operation.stamp (lower ++ upper)).exchange := by
    rw [CampusTCPTwoExchangeMonitor.observe, ite_eq_left exchangeChecked]
    simp only [forward, localStep, afterRead, CampusTCPTwoProgressMonitorFacts.mode_beq,
      reduceCtorEq, decide_false, decide_true, ite_false, ite_true]
    congr 1
    · change (match actual.event with | .dropPacket id => monitor.exchange.drops ++ [id] | _ => monitor.exchange.drops) = _
      rw [value.event]
    · change (match actual.event with | .timeout _ true => monitor.exchange.timeouts + 1 | _ => monitor.exchange.timeouts) = _
      rw [value.event]
  have noDrain := CampusTCPTwoTransferControlObserve.noDrain_of_non_capture actual.before monitor
    (by rw [finished]; decide)
  have control : CampusTCPTwoTransferMonitor.controlDemand monitor = none := by rw [CampusTCPTwoTransferMonitor.controlDemand, finished]
  have checked : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoTransferMonitor.allowed cfg actual.before monitor actual.event) = true := by
    rw [value.move.supported, value.move.passed, value.move.beforeEq]
    exact allowed
  rw [W.observe, ite_eq_left checked, noDrain, control, CampusTCPTwoTransferMonitor.ordinary, exchangeStep]
  rfl

private theorem sender_steps (value : ReadMove initial current location first second timeouts actual) :
    applicationSteps value.move.after.endpoints sender = applicationSteps current.endpoints sender := by
  have steps := CampusTCPRoundPhaseHistory.Move.local_history value.move sender.other (.read (lower ++ upper).length)
    (by rw [value.event]; exact .read _) value.operation value.recorded sender
  have different : sender ≠ sender.other := by cases sender <;> decide
  simpa only [different, ite_false, List.append_nil] using steps

structure Complete (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location (.retired first second) .allReleased) (actual : Step input) where
  value : ReadMove initial current location first second monitor.exchange.forward.retries actual
  finished : monitor.mode = .finished
  forward : monitor.exchange.mode = .forward
  needRead : monitor.exchange.forward.mode = .needRead
  allowed : W.Allowed cfg current.report.final monitor actual.event
  observed : W.observe cfg monitor actual = afterRead monitor value.operation.stamp (lower ++ upper)
  healthy : (W.observe cfg monitor actual).mode ≠ .invalid
  losses : CampusTCPTwoTransferLossHistory.History initial cfg value.move.after (W.observe cfg monitor actual)
  book : losses.book = core.losses.book
  suffix : losses.suffix = core.losses.suffix ++ [actual]
  lossBound : (W.observe cfg monitor actual).exchange.forward.drops.length ≤ allowance
  originals : CampusTCPTwoProgressSourceHistory.Originals initial value.move.after (.retired first second)
  writer : CampusTCPTwoProgressWriteHistory.History initial value.move.after (lower ++ upper)
  sources : CampusTCPTwoProgressReceiptSources.History initial value.move.after

theorem read_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location (.retired first second) .allReleased)
    (finished : monitor.mode = .finished) (forward : monitor.exchange.mode = .forward)
    (mode : monitor.exchange.forward.mode = .needRead)
    (sources : CampusTCPTwoProgressReceiptSources.History initial current) :
    ∃ actual, Nonempty (Complete core actual) := by
  obtain ⟨actual, ⟨value⟩⟩ := read_move_at core.live
  have allowed : W.Allowed cfg current.report.final monitor actual.event := by rw [value.event]; exact read_allowed finished forward mode
  have observed := observe_read (checks := checks) (routing := routing) (quantum := quantum) (allowance := allowance)
    (reverseLower := reverseLower) (reverseUpper := reverseUpper) value finished forward mode
  let losses := core.losses.append value.move
    (by simp only [CampusTCPTwoProgressLossHistory.isDrop, value.event])
    (by simp only [CampusTCPTwoExchangeLoss.isTimeoutOutput, value.event])
    (by rw [observed]; rfl) (by rw [observed]; rfl) (by rw [observed]; rfl) (by rw [observed]; rfl)
  exact ⟨actual, ⟨{
    value, finished, forward, needRead := mode, allowed, observed
    healthy := by rw [observed]; exact (by simpa only [afterRead, finished] using (show CampusTCPTwoTransferMonitor.Mode.finished ≠ .invalid by decide))
    losses, book := rfl, suffix := rfl
    lossBound := by rw [observed]; exact core.lossBound
    originals := core.originals.retain_steps value.move.retained
    writer := core.writer.same (sender_steps value)
    sources := sources.non_delivery value.move (by rw [value.event]; trivial) }⟩⟩

end Netlib.Check.CampusTCPTwoTransferLocatedRead
