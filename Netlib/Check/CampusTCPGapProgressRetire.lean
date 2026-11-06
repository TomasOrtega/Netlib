import Netlib.Check.CampusTCPGapProgressState

/-!
# Actual retirement and read in a held-gap task

The covering ACK retires both actual sender records.
The read records only the selected suffix's stream change.
-/

namespace Netlib.Check.CampusTCPGapProgressRetire

open Packet Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPGapProgressStart (GapInitial)
open CampusTCPGapProgressState (Live gateway_reframe)
open CampusTCPGapProgressPhaseBase (Anchor)

variable {input : Input} {complete : H.Completed input.active input.passive}
  {cut current next : Cut input complete} {sender : Actor} {lower upper : List UInt8}
  {initial : GapInitial cut sender lower upper} {retries : Nat}

structure Retirement (initial : GapInitial cut sender lower upper) (retries : Nat) (state : Endpoint.State) where
  recovery : Recovery.State
  runtime : state.recovery = some recovery
  sent : state.core.sent = []
  cursor : state.core.sendUna = state.core.sendNext
  outstanding : recovery.outstanding = []
  deadline : recovery.deadline = none
  lastTimedOut : recovery.lastTimedOut = none
  timeoutCount : recovery.timeoutCount = 0
  nextID : recovery.nextId = initial.flight.recovery.nextId
  frontier : recovery.frontier = initial.flight.recovery.frontier
  valid : state.Valid
  coherent : Endpoint.RecoveryCoherent state
  prepared : Endpoint.AckPrepared state
  storage : Endpoint.StorageCoherent state
  karn : 0 < retries → recovery.rto = 2 ^ retries * 1000 ∧
    recovery.estimator = initial.flight.recovery.estimator ∧ recovery.lastSample = initial.flight.recovery.lastSample

def Retirement.clock (retired : Retirement initial retries state) (frame : Endpoint.ClockFrame state after)
    (timely : Endpoint.AckTimeReady state after.now) : Retirement initial retries after where
  recovery := { retired.recovery with now := after.now }
  runtime := frame.runtime retired.runtime
  sent := by rw [frame.core]; exact retired.sent
  cursor := by rw [frame.core]; exact retired.cursor
  outstanding := retired.outstanding
  deadline := retired.deadline
  lastTimedOut := retired.lastTimedOut
  timeoutCount := retired.timeoutCount
  nextID := retired.nextID
  frontier := retired.frontier
  valid := frame.valid retired.valid
  coherent := frame.recovery_coherent retired.coherent
  prepared := frame.ack_prepared retired.prepared timely
  storage := frame.storage_coherent retired.storage
  karn := retired.karn

structure ReceiverClosed (initial : GapInitial cut sender lower upper) (state : Endpoint.State) where
  recovery : Recovery.State
  runtime : state.recovery = some recovery
  recoveryState : recovery = { initial.receiver.recovery with now := recovery.now, duplicateAcks := 0 }
  valid : state.Valid
  coherent : Endpoint.RecoveryCoherent state
  prepared : Endpoint.AckPrepared state
  storage : Endpoint.StorageCoherent state
  empty : state.core.received = []
  held : state.receiveStore.held = []

def ReceiverClosed.clock (closed : ReceiverClosed initial state) (frame : Endpoint.ClockFrame state after)
    (timely : Endpoint.AckTimeReady state after.now) : ReceiverClosed initial after where
  recovery := { closed.recovery with now := after.now }
  runtime := frame.runtime closed.runtime
  recoveryState := by rw [closed.recoveryState]
  valid := frame.valid closed.valid
  coherent := frame.recovery_coherent closed.coherent
  prepared := frame.ack_prepared closed.prepared timely
  storage := frame.storage_coherent closed.storage
  empty := by rw [frame.core]; exact closed.empty
  held := by rw [frame.receiveStore]; exact closed.held

structure Retired (initial : GapInitial cut sender lower upper) (current : Cut input complete) (retries : Nat) where
  anchor : Anchor cut current
  retirement : Retirement initial retries (endpoint current.endpoints sender)
  receiverFacts : CampusTCPGapProgressReceiver.Facts initial (endpoint current.endpoints sender.other) true
  gateway : CampusTCPGapProgressGateway.Current initial.gateway current
  history : CampusTCPGapProgressHistory.History cut current sender.other (lower ++ upper) true
  bound : retries ≤ 2

structure Completed (initial : GapInitial cut sender lower upper) (current : Cut input complete) (retries : Nat) where
  anchor : Anchor cut current
  reader : Step input
  member : reader ∈ current.report.steps
  event : reader.event = .read sender.other (lower ++ upper).length
  bytes : reader.result.read = lower ++ upper
  operation : T.Step
  recorded : reader.result.application = some (sender.other, operation)
  readerBefore : Cut input complete
  beforeEq : reader.before = readerBefore.report.final
  localBefore : operation.before = endpoint readerBefore.endpoints sender.other
  stamp : operation.stamp = reader.before.time
  readerFacts : CampusTCPGapProgressReceiver.Facts initial operation.before true
  history : CampusTCPGapProgressHistory.Complete cut current sender.other (lower ++ upper) operation
  retirement : Retirement initial retries (endpoint current.endpoints sender)
  receiver : ReceiverClosed initial (endpoint current.endpoints sender.other)
  gateway : CampusTCPGapProgressGateway.Current initial.gateway current
  bound : retries ≤ 2

private theorem guards (retired : Retirement initial retries (endpoint current.endpoints sender))
    (valid : Endpoint.RecoveryCoherent (endpoint current.endpoints sender.other))
    (prepared : Endpoint.AckPrepared (endpoint current.endpoints sender.other))
    (runtime : (endpoint current.endpoints sender.other).recovery.isSome = true) : CampusTCPRoundGuards.Guards current.endpoints := by
  intro actor
  by_cases selected : actor = sender
  · rw [selected]
    exact ⟨retired.coherent, retired.prepared, congrArg Option.isSome retired.runtime⟩
  · have peer : actor = sender.other := by cases actor <;> cases sender <;> simp_all [Actor.other]
    rw [peer]
    exact ⟨valid, prepared, runtime⟩

def Retired.clock (retired : Retired initial current retries) (placement : CampusTCPRecoveryRoundPhaseBase.At current next)
    (senderTime : Endpoint.AckTimeReady (endpoint current.endpoints sender) (endpoint next.endpoints sender).now)
    (receiverTime : Endpoint.AckTimeReady (endpoint current.endpoints sender.other) (endpoint next.endpoints sender.other).now) :
    Retired initial next retries := by
  let retirement := retired.retirement.clock (placement.frame.endpointFrame sender) senderTime
  let receiver := retired.receiverFacts.clock (placement.frame.endpointFrame sender.other) receiverTime
  exact ⟨⟨guards retirement receiver.coherent receiver.prepared (congrArg Option.isSome receiver.runtime),
    retired.anchor.retained.trans placement.retained, retired.anchor.environment.trans placement.frame.environment.symm⟩,
    retirement, receiver, gateway_reframe retired.gateway (placement.frame.beforeService .standby),
    retired.history.clock placement, retired.bound⟩

def Completed.clock (done : Completed initial current retries) (placement : CampusTCPRecoveryRoundPhaseBase.At current next)
    (senderTime : Endpoint.AckTimeReady (endpoint current.endpoints sender) (endpoint next.endpoints sender).now)
    (receiverTime : Endpoint.AckTimeReady (endpoint current.endpoints sender.other) (endpoint next.endpoints sender.other).now) :
    Completed initial next retries := by
  let retirement := done.retirement.clock (placement.frame.endpointFrame sender) senderTime
  let receiver := done.receiver.clock (placement.frame.endpointFrame sender.other) receiverTime
  exact ⟨⟨guards retirement receiver.coherent receiver.prepared (congrArg Option.isSome receiver.runtime),
    done.anchor.retained.trans placement.retained, done.anchor.environment.trans placement.frame.environment.symm⟩,
    done.reader, placement.member done.member, done.event, done.bytes, done.operation, done.recorded,
    done.readerBefore, done.beforeEq, done.localBefore, done.stamp, done.readerFacts,
    done.history.clock placement, retirement, receiver, gateway_reframe done.gateway (placement.frame.beforeService .standby), done.bound⟩

structure AckMove (initial : GapInitial cut sender lower upper) (current : Cut input complete) (retries : Nat)
    (index : Nat) (served : Served input) (emission : WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission) (actual : Step input) where
  move : Move current actual
  delivery : CampusTCPRoundDelivery.AckDelivered current.report complete current.endpoints index served emission emitted
  actualEq : delivery.step = actual
  senderEq : endpoint move.after.endpoints sender = delivery.after
  peer : endpoint move.after.endpoints sender.other = endpoint current.endpoints sender.other
  receiverFacts : CampusTCPGapProgressReceiver.Facts initial (endpoint move.after.endpoints sender.other) true
  retirement : Retirement initial retries (endpoint move.after.endpoints sender)
  accepted : delivery.localStep.result.decision = .accepted (.receive (lower.length + upper.length) 0)
  receiverSteps : applicationSteps move.after.endpoints sender.other = applicationSteps current.endpoints sender.other
  gateway : ∀ selected, beforeService input move.after.report.final selected = beforeService input current.report.final selected
  environment : CampusTCPRoundEnvironment.environment current.report.final = CampusTCPRoundEnvironment.environment move.after.report.final
  anchor : Anchor cut move.after

def Retired.ofAck (live : Live initial current retries true)
    (ack : AckMove initial current retries index served emission emitted actual) : Retired initial ack.move.after retries :=
  ⟨ack.anchor, ack.retirement, ack.receiverFacts, gateway_reframe live.gateway (ack.gateway .standby),
    live.history.same ack.receiverSteps, live.senderFlight.bound⟩

theorem deliver_ack_at (live : Live initial current retries true)
    (index : Nat) (served : Served input) (found : current.report.final.services[index]? = some served)
    (emission : WireForwarding.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (actor : served.ticket.value.produced.actor = sender.other)
    (application : CampusTCPDeliveryEnabled.ApplicationSource served.ticket.value.produced)
    (pending : CampusTCPDeliveryEnabled.LinkPending current.report.final index)
    (tuple : emission.asInput.packet.header = (endpoint cut.endpoints sender).core.inbound)
    (controls : EstablishedReceive.control emission.asInput.packet.segment = none)
    (ack : Flags.ack emission.asInput.packet.segment.flags = true)
    (sequence : emission.asInput.packet.segment.sequence = (endpoint cut.endpoints sender).core.receiveNext)
    (acknowledgment : emission.asInput.packet.segment.acknowledgment = (endpoint cut.endpoints sender).core.sendNext)
    (empty : emission.asInput.packet.segment.payload = []) :
    ∃ actual : Step input, Nonempty (AckMove initial current retries index served emission emitted actual) := by
  have other : served.ticket.value.produced.actor.other = sender := by rw [actor]; cases sender <;> rfl
  have ready := live.senderFlight.full_ack_ready emission.asInput tuple controls ack sequence acknowledgment empty
  have selectedReady : CampusTCPDeliveryEnabled.FullAckReady (endpoint current.endpoints served.ticket.value.produced.actor.other)
      emission.asInput live.senderFlight.recovery live.senderFlight.reaction := by simpa only [other] using ready
  obtain ⟨delivery⟩ := CampusTCPRoundDelivery.Report.deliver_full_ack current.report complete current.endpoints
    current.connection index served found emission emitted application pending live.senderFlight.recovery live.senderFlight.reaction selectedReady
  let next : Cut input complete := ⟨_, delivery.toDelivery.append current.supported current.finished,
    delivery.toDelivery.append_supported _ _, rfl, delivery.updated, delivery.connection⟩
  let move : Move current delivery.step := ⟨next, delivery.beforeEq, delivery.supported, delivery.passed, rfl, rfl⟩
  have senderEq : endpoint move.after.endpoints sender = delivery.after := by simpa only [other] using delivery.selected
  have peer : endpoint move.after.endpoints sender.other = endpoint current.endpoints sender.other := by
    simpa only [other] using delivery.peer
  obtain ⟨after, recovery, received, runtime, sent, cursor, valid, prepared, coherent, storage,
      outstanding, deadline, timedOut, count, nextID, frontier, _, karn⟩ :=
    live.senderFlight.receive_full_ack emission.asInput tuple controls ack sequence acknowledgment empty
  have evaluated : delivery.localStep.result =
      ⟨after, .accepted (.receive (lower.length + upper.length) 0), none, [], none⟩ := by
    rw [delivery.localStep.computed, delivery.localBefore, delivery.localEvent]
    simpa only [ApplicationTrace.evaluate, other] using received
  have afterEq : delivery.after = after := delivery.resultState.symm.trans (congrArg Endpoint.Result.state evaluated)
  have retirement : Retirement initial retries (endpoint move.after.endpoints sender) := by
    rw [senderEq, afterEq]
    refine ⟨recovery, runtime, sent, ?_, outstanding, deadline, timedOut, count, nextID, frontier,
      valid, coherent, prepared, storage, karn⟩
    have span := valid.1.2.2.2.2.1
    simpa only [sent, List.length_nil, Seq.add_zero] using span
  have environment : CampusTCPRoundEnvironment.environment current.report.final =
      CampusTCPRoundEnvironment.environment move.after.report.final := delivery.environment
  refine ⟨delivery.step, ⟨⟨move, delivery, rfl, senderEq, peer, ?_, retirement,
    congrArg Endpoint.Result.decision evaluated, ?_, ?_, environment, ?_⟩⟩⟩
  · rw [peer]; exact live.receiverFacts
  · simpa only [other] using delivery.peerSteps
  · intro selected
    rw [move.final, CampusTCPRoundLocal.step_service_nonservice delivery.step (by rw [delivery.event]; trivial), delivery.beforeEq]
  · exact ⟨CampusTCPRoundGuards.AckDelivered.guards delivery live.anchor.guards,
      live.anchor.retained.trans move.retained, live.anchor.environment.trans environment⟩

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

structure ReadMove (initial : GapInitial cut sender lower upper) (current : Cut input complete)
    (retries : Nat) (actual : Step input) where
  move : Move current actual
  event : actual.event = .read sender.other (lower ++ upper).length
  operation : T.Step
  recorded : actual.result.application = some (sender.other, operation)
  localBefore : operation.before = endpoint current.endpoints sender.other
  localEvent : operation.event = .read (lower ++ upper).length
  localStamp : operation.stamp = current.report.final.time
  accepted : operation.result.decision = .accepted (.read (lower ++ upper).length)
  returned : actual.result.read = lower ++ upper
  localRead : operation.result.read = lower ++ upper
  selected : endpoint move.after.endpoints sender.other =
    Endpoint.readState (endpoint current.endpoints sender.other) (lower ++ upper).length
  peer : endpoint move.after.endpoints sender = endpoint current.endpoints sender
  receiver : ReceiverClosed initial (endpoint move.after.endpoints sender.other)
  retirement : Retirement initial retries (endpoint move.after.endpoints sender)
  receiverSteps : applicationSteps move.after.endpoints sender.other =
    applicationSteps current.endpoints sender.other ++ [operation]
  gateway : ∀ selected, beforeService input move.after.report.final selected = beforeService input current.report.final selected
  environment : CampusTCPRoundEnvironment.environment current.report.final =
    CampusTCPRoundEnvironment.environment move.after.report.final
  anchor : Anchor cut move.after

theorem read_at (retired : Retired initial current retries) :
    ∃ actual : Step input, Nonempty (ReadMove initial current retries actual) := by
  have payload : (endpoint current.endpoints sender.other).core.received = lower ++ upper :=
    retired.receiverFacts.received
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
  have guarded := (retired.anchor.guards sender.other).readState (lower ++ upper).length retired.receiverFacts.valid fits
  have guards : CampusTCPRoundGuards.Guards move.after.endpoints :=
    CampusTCPRoundGuards.guards_frame current.endpoints appended.next.endpoints sender.other
      (CampusTCPRoundGuards.read_step_guarded operation (lower ++ upper).length rfl fits (retired.anchor.guards sender.other))
      appended.selected appended.peer retired.anchor.guards
  have receiver : ReceiverClosed initial (endpoint move.after.endpoints sender.other) := by
    rw [selected]
    refine ⟨retired.receiverFacts.recovery, retired.receiverFacts.runtime, ?_,
      Endpoint.readState_valid _ _ retired.receiverFacts.valid, guarded.recoveryCoherent, guarded.prepared,
      ?_, ?_, ?_⟩
    · exact retired.receiverFacts.recoveryState
    · exact read_storage _ _ retired.receiverFacts.storage
    · simp only [Endpoint.readState, payload, List.drop_length]
    · exact retired.receiverFacts.held
  refine ⟨actual, ⟨⟨move, rfl, operation, recorded, rfl, rfl, rfl, congrArg Endpoint.Result.decision evaluated,
    read, congrArg Endpoint.Result.read evaluated, selected, peer, receiver, ?_, ?_, ?_, environment,
    ⟨guards, retired.anchor.retained.trans move.retained, retired.anchor.environment.trans environment⟩⟩⟩⟩
  · rw [peer]; exact retired.retirement
  · simpa only [ite_true] using CampusTCPRoundPhaseHistory.Move.local_history move sender.other
      (.read (lower ++ upper).length) (.read _) operation recorded sender.other
  · intro gateway
    rw [move.final]
    exact CampusTCPRoundLocal.step_service_nonservice actual trivial gateway

def Completed.ofRead (retired : Retired initial current retries) (read : ReadMove initial current retries actual) :
    Completed initial read.move.after retries := by
  refine ⟨read.anchor, actual, read.move.member, read.event, read.returned, read.operation, read.recorded,
    current, read.move.beforeEq, read.localBefore, ?_, ?_, ?_, read.retirement, read.receiver,
    gateway_reframe retired.gateway (read.gateway .standby), retired.bound⟩
  · rw [read.move.beforeEq]
    exact read.localStamp
  · rw [read.localBefore]; exact retired.receiverFacts
  · apply retired.history.read read.operation read.receiverSteps
    · exact List.append_ne_nil_of_left_ne_nil initial.lowerNonempty upper
    · exact read.localEvent
    · rw [ApplicationTrace.Step.readBytes]
      exact read.localRead

theorem Step.deliver_ack (actual : Step input) (live : Live initial current retries true)
    (index : Nat) (served : Served input) (found : current.report.final.services[index]? = some served)
    (emission : WireForwarding.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (actor : served.ticket.value.produced.actor = sender.other)
    (application : CampusTCPDeliveryEnabled.ApplicationSource served.ticket.value.produced)
    (pending : CampusTCPDeliveryEnabled.LinkPending current.report.final index)
    (tuple : emission.asInput.packet.header = (endpoint cut.endpoints sender).core.inbound)
    (controls : EstablishedReceive.control emission.asInput.packet.segment = none)
    (ack : Flags.ack emission.asInput.packet.segment.flags = true)
    (sequence : emission.asInput.packet.segment.sequence = (endpoint cut.endpoints sender).core.receiveNext)
    (acknowledgment : emission.asInput.packet.segment.acknowledgment = (endpoint cut.endpoints sender).core.sendNext)
    (empty : emission.asInput.packet.segment.payload = [])
    (before : actual.before = current.report.final) (event : actual.event = .deliver index emission.bytes true) :
    Nonempty (AckMove initial current retries index served emission emitted actual) := by
  obtain ⟨enabled, ⟨facts⟩⟩ := deliver_ack_at live index served found emission emitted actor application pending
    tuple controls ack sequence acknowledgment empty
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (facts.move.beforeEq.trans before.symm) (facts.actualEq.symm ▸ facts.delivery.event.trans event.symm)
  exact ⟨same ▸ facts⟩

theorem Step.read (actual : Step input) (retired : Retired initial current retries)
    (before : actual.before = current.report.final) (event : actual.event = .read sender.other (lower ++ upper).length) :
    Nonempty (ReadMove initial current retries actual) := by
  obtain ⟨enabled, ⟨facts⟩⟩ := read_at retired
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (facts.move.beforeEq.trans before.symm) (facts.event.trans event.symm)
  exact ⟨same ▸ facts⟩

end Netlib.Check.CampusTCPGapProgressRetire
