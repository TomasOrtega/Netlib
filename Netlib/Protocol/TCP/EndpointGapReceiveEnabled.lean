import Netlib.Protocol.TCP.EndpointReceiveEnabled

namespace Netlib.Protocol.TCP.ReceiveStore

theorem accept_frontier_one (store : State Meta) (upper : Run Meta) (payload : List UInt8) (metadata : Meta)
    (window budget : Nat) (valid : store.Valid (store.frontier + window) budget)
    (held : store.held = [upper]) (adjacent : upper.position = store.frontier + payload.length)
    (nonempty : payload ≠ []) :
    accept store store.frontier payload metadata (store.frontier + window) budget = .ok
      ⟨⟨store.frontier + payload.length + upper.bytes.length, store.nextID + 1, [], store.seenGap⟩,
        store.nextID, payload.length, [current store store.frontier payload metadata, upper], false⟩ := by
  have upperValid := valid.2.2.2.1 upper (by rw [held]; simp)
  have upperBound : store.frontier + payload.length + upper.bytes.length ≤ store.frontier + window := by
    simpa only [Run.limit, adjacent] using upperValid.2.2.1
  let incoming := current store store.frontier payload metadata
  let placed : Placed Meta := ⟨[incoming, upper], false⟩
  have chosen : place incoming store.held = .ok placed := by
    simp only [held, place, incoming, current, Run.limit, adjacent, Nat.le_refl, ite_true, placed]
  have total : store.heldBytes + payload.length ≤ budget := by
    simp only [State.heldBytes, held, size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have room := valid.2.1
    omega
  have drained : drain store.frontier placed.runs =
      ⟨store.frontier + payload.length + upper.bytes.length, [incoming, upper], []⟩ := by
    simp only [placed, drain, incoming, current, ite_true, Run.limit, adjacent]
  have after := after_valid store store.frontier payload metadata (store.frontier + window) budget placed
    valid nonempty (Nat.le_refl _) (by omega) chosen (by simpa only [placed, Bool.false_eq_true, ite_false] using total)
  simp only [drained, Nat.lt_irrefl, decide_false, Bool.or_false, size, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero] at after
  simp only [accept, valid, not_true_eq_false, ite_false, nonempty, Nat.lt_irrefl,
    show ¬store.frontier + window < store.frontier + payload.length by omega]
  rw [chosen]
  simp only [show placed.duplicate = false from rfl, Bool.false_eq_true, ite_false, Nat.not_lt.mpr total]
  rw [drained]
  have afterValid : (⟨store.frontier + payload.length + upper.bytes.length, store.nextID + 1, [], store.seenGap⟩ : State Meta).Valid
      (store.frontier + window) (budget - size [incoming, upper]) := after
  simp only [decide_false, Bool.or_false, afterValid, ite_true]
  rfl

end Netlib.Protocol.TCP.ReceiveStore

namespace Netlib.Protocol.TCP.Recovery

theorem acknowledgeAt_zero_of_past (state : State) (receivedAt : Nat) (past : receivedAt ≤ state.now) :
    acknowledgeAt state 0 receivedAt = .ok state := by
  have untouched : touched 0 state.outstanding = [] := by cases state.outstanding <;> rfl
  simp only [acknowledgeAt, Nat.not_lt.mpr past, ite_false, untouched, List.any_nil,
    Bool.false_eq_true, acknowledge_zero, Except.map, acknowledgeAtState, ite_true]

end Netlib.Protocol.TCP.Recovery

namespace Netlib.Protocol.TCP.Endpoint

structure GapReceiveConditions (state : State) (input : Input) (upper : ReceiveReassembly.Run)
    (recovery : Recovery.State) (reaction : AckReaction.State) : Prop where
  valid : state.Valid
  coherent : RecoveryCoherent state
  prepared : AckPrepared state
  storage : StorageCoherent state
  runtime : state.recovery = some recovery
  ackRuntime : state.ackReaction = some reaction
  idle : recovery.outstanding = []
  held : state.receiveStore.held = [upper]
  adjacent : upper.position = state.receiveStore.frontier + input.packet.segment.payload.length
  lowerNonempty : input.packet.segment.payload ≠ []
  lowerTuple : input.packet.header = state.core.inbound
  lowerControl : EstablishedReceive.control input.packet.segment = none
  lowerAck : Flags.ack input.packet.segment.flags = true
  lowerSequence : input.packet.segment.sequence = state.core.receiveNext
  lowerAckOld : Seq.distance input.packet.segment.acknowledgment state.core.sendUna ≤ EstablishedReceive.maxSendWindow
  upperPayload : upper.metadata.segment.payload = upper.bytes
  upperTuple : upper.metadata.header = state.core.inbound
  upperControl : EstablishedReceive.control upper.metadata.segment = none
  upperAck : Flags.ack upper.metadata.segment.flags = true
  upperSequence : upper.metadata.segment.sequence = state.core.receiveNext.add input.packet.segment.payload.length
  upperAckOld : Seq.distance upper.metadata.segment.acknowledgment state.core.sendUna ≤ EstablishedReceive.maxSendWindow
  upperPast : upper.metadata.receivedAt ≤ state.now

def gapLower (state : State) (input : Input) : ReceiveReassembly.Run := inOrderRun state input

def gapStore (state : State) (input : Input) (upper : ReceiveReassembly.Run) : ReceiveStore.Result ReceiveReassembly.Receipt :=
  ⟨⟨state.receiveStore.frontier + input.packet.segment.payload.length + upper.bytes.length,
    state.receiveStore.nextID + 1, [], state.receiveStore.seenGap⟩,
    state.receiveStore.nextID, input.packet.segment.payload.length, [gapLower state input, upper], false⟩

theorem GapReceiveConditions.store_valid (conditions : GapReceiveConditions state input upper recovery reaction) :
    state.receiveStore.Valid (state.receiveStore.frontier + offeredWindow state) state.core.window := by
  have stored : reaction.advertisement.frontier = state.receiveStore.frontier ∧
      state.receiveStore.Valid (state.receiveStore.frontier + reaction.window) state.core.window := by
    simpa only [conditions.ackRuntime] using conditions.storage.2
  simpa only [conditions.ackRuntime, offeredWindow] using stored.2

theorem GapReceiveConditions.total_fits (conditions : GapReceiveConditions state input upper recovery reaction) :
    input.packet.segment.payload.length + upper.bytes.length ≤ offeredWindow state := by
  have valid := conditions.store_valid
  have upperValid := valid.2.2.2.1 upper (by rw [conditions.held]; simp)
  have bound := upperValid.2.2.1
  simp only [ReceiveStore.Run.limit, conditions.adjacent] at bound
  omega

theorem GapReceiveConditions.sent_empty (conditions : GapReceiveConditions state input upper recovery reaction) :
    state.core.sent = [] := by
  have coherent := conditions.coherent
  simp only [RecoveryCoherent, conditions.runtime] at coherent
  have flight := coherent.2.2.1
  simp only [Recovery.flight, conditions.idle, List.map_nil, List.sum_nil] at flight
  simpa only [List.length_eq_zero_iff] using flight.symm

theorem prepare_frontier_one (conditions : GapReceiveConditions state input upper recovery reaction) :
    ReceiveReassembly.prepare state.core state.receiveStore input (offeredWindow state) state.now =
      .data (gapStore state input upper) := by
  have fits : input.packet.segment.payload.length ≤ offeredWindow state := by
    have bound := conditions.total_fits
    omega
  have accepts : ReceiveWindow.acceptsSegment state.core.receiveNext (offeredWindow state) input.packet.segment = true := by
    simp only [ReceiveWindow.acceptsSegment, conditions.lowerSequence,
      EstablishedReceive.segmentLength_of_control_none _ conditions.lowerControl]
    exact ReceiveWindow.in_order_fits _ _ _ fits
  have gate : ReceiveReassembly.initialGate state.core input (offeredWindow state) = .next 0 := by
    simp only [ReceiveReassembly.initialGate, conditions.valid.1, not_true_eq_false, ite_false,
      conditions.lowerTuple, ne_eq, conditions.lowerControl, accepts, Bool.not_true, Bool.false_eq_true]
  have sameOrder : Seq.before state.core.receiveNext state.core.receiveNext = false := by simp [Seq.before, Seq.Before]
  simp only [ReceiveReassembly.prepare, gate, List.isEmpty_eq_false_iff.mpr conditions.lowerNonempty,
    Bool.false_eq_true, ite_false, ReceiveReassembly.position, conditions.lowerSequence, sameOrder,
    Seq.distance_self, Nat.add_zero]
  rw [ReceiveStore.accept_frontier_one state.receiveStore upper input.packet.segment.payload
    ⟨input.packet.segment, input.packet.header, state.now⟩ (offeredWindow state) state.core.window
    conditions.store_valid conditions.held conditions.adjacent conditions.lowerNonempty]
  rfl

def zeroHeader (state : State) (run : ReceiveReassembly.Run) : ReceiveReassembly.HeaderEffect :=
  ⟨state.core, run, 0, EstablishedReceive.commit state.core run.bytes 0⟩

def zeroRunState (state : State) (recovery : Recovery.State) (run : ReceiveReassembly.Run) : State :=
  { state with
    core := EstablishedReceive.commit state.core run.bytes 0
    recovery := some { recovery with duplicateAcks := 0 }
    lastAckWindow := some run.metadata.segment.window.val
    sendWindow := if windowEligible state run.metadata.segment then run.metadata.segment.window.val else state.sendWindow
    sendWL1 := if windowEligible state run.metadata.segment then run.metadata.segment.sequence else state.sendWL1
    sendWL2 := if windowEligible state run.metadata.segment then run.metadata.segment.acknowledgment else state.sendWL2 }

theorem zeroRunState_eq_windowState (state : State) (recovery : Recovery.State) (run : ReceiveReassembly.Run) :
    zeroRunState state recovery run = windowState state { state with
      core := EstablishedReceive.commit state.core run.bytes 0
      recovery := some { recovery with duplicateAcks := 0 }
      lastAckWindow := some run.metadata.segment.window.val } run.metadata.segment := by
  unfold zeroRunState windowState
  split <;> rfl

theorem applyRun_zero_enabled (state : State) (run : ReceiveReassembly.Run) (valid : state.Valid)
    (payload : run.metadata.segment.payload = run.bytes) (tuple : run.metadata.header = state.core.inbound)
    (controls : EstablishedReceive.control run.metadata.segment = none) (ack : Flags.ack run.metadata.segment.flags = true)
    (sequence : run.metadata.segment.sequence = state.core.receiveNext)
    (fits : run.bytes.length ≤ state.core.window)
    (old : Seq.distance run.metadata.segment.acknowledgment state.core.sendUna ≤ EstablishedReceive.maxSendWindow) :
    ReceiveReassembly.applyRun state.core run = .ok (zeroHeader state run) := by
  have accepts : ReceiveWindow.acceptsSegment state.core.receiveNext state.core.window run.metadata.segment = true := by
    simp only [ReceiveWindow.acceptsSegment, sequence, EstablishedReceive.segmentLength_of_control_none _ controls, payload]
    exact ReceiveWindow.in_order_fits _ _ _ fits
  have evaluated := EstablishedReceive.evaluate_of_ready state.core run.metadata.header run.metadata.segment
    ⟨valid.1, tuple, accepts, controls, ack⟩
  rw [EstablishedReceive.acknowledgedCount_old state.core _ valid.1.2.2.2.2.2 old] at evaluated
  dsimp only at evaluated
  rw [EstablishedReceive.finish_of_fits state.core run.metadata.segment 0 sequence (by simpa only [payload] using fits)] at evaluated
  simp only [ReceiveReassembly.applyRun, payload, ne_eq, not_true_eq_false, ite_false, evaluated]
  rfl

theorem applyHeader_zero_enabled (state : State) (recovery : Recovery.State) (run : ReceiveReassembly.Run)
    (runtime : state.recovery = some recovery) (past : run.metadata.receivedAt ≤ recovery.now) :
    applyHeader state (zeroHeader state run) = .ok (zeroRunState state recovery run) := by
  rw [zeroRunState_eq_windowState]
  simp only [applyHeader, zeroHeader, ne_eq, not_true_eq_false, ite_false, runtime,
    Recovery.acknowledgeAt_zero_of_past recovery _ past, Except.map, Option.isSome_some, ite_true]

@[simp] theorem zeroRunState_core (state : State) (recovery : Recovery.State) (run : ReceiveReassembly.Run) :
    (zeroRunState state recovery run).core = EstablishedReceive.commit state.core run.bytes 0 := rfl

@[simp] theorem zeroRunState_recovery (state : State) (recovery : Recovery.State) (run : ReceiveReassembly.Run) :
    (zeroRunState state recovery run).recovery = some { recovery with duplicateAcks := 0 } := rfl

@[simp] theorem zeroRunState_effectiveMSS (state : State) (recovery : Recovery.State) (run : ReceiveReassembly.Run) :
    (zeroRunState state recovery run).effectiveMSS = state.effectiveMSS := rfl

@[simp] theorem zeroRunState_receiveStore (state : State) (recovery : Recovery.State) (run : ReceiveReassembly.Run) :
    (zeroRunState state recovery run).receiveStore = state.receiveStore := rfl

@[simp] theorem zeroRunState_ackReaction (state : State) (recovery : Recovery.State) (run : ReceiveReassembly.Run) :
    (zeroRunState state recovery run).ackReaction = state.ackReaction := rfl

@[simp] theorem zeroRunState_ownMSS (state : State) (recovery : Recovery.State) (run : ReceiveReassembly.Run) :
    (zeroRunState state recovery run).localReceiveMSS = state.localReceiveMSS := rfl

@[simp] theorem zeroRunState_lastAckWindow (state : State) (recovery : Recovery.State) (run : ReceiveReassembly.Run) :
    (zeroRunState state recovery run).lastAckWindow = some run.metadata.segment.window.val := rfl

theorem zeroRunState_valid (state : State) (recovery : Recovery.State) (run : ReceiveReassembly.Run)
    (valid : state.Valid) (fits : run.bytes.length ≤ state.core.window) : (zeroRunState state recovery run).Valid := by
  rw [zeroRunState_eq_windowState]
  apply windowState_valid
  exact ⟨EstablishedReceive.commit_valid state.core run.bytes 0 valid.1 fits (Nat.zero_le _), valid.2⟩

def gapReceived (state : State) (input : Input) (upper : ReceiveReassembly.Run) (recovery : Recovery.State) : State :=
  zeroRunState (zeroRunState state recovery (gapLower state input)) { recovery with duplicateAcks := 0 } upper

def gapHeaders (state : State) (input : Input) (upper : ReceiveReassembly.Run) (recovery : Recovery.State) :
    List ReceiveReassembly.HeaderEffect :=
  [zeroHeader state (gapLower state input), zeroHeader (zeroRunState state recovery (gapLower state input)) upper]

def gapReaction (state : State) (input : Input) (upper : ReceiveReassembly.Run) (reaction : AckReaction.State) :
    AckReaction.State :=
  AckReaction.receiveRelease reaction state.now
    (state.core.receiveNext.add (input.packet.segment.payload.length + upper.bytes.length))
    input.packet.segment.payload.length (input.packet.segment.payload.length + upper.bytes.length) true

def gapAfter (state : State) (input : Input) (upper : ReceiveReassembly.Run)
    (recovery : Recovery.State) (reaction : AckReaction.State) : State :=
  storedState (gapReceived state input upper recovery) (gapStore state input upper).state
    (some (gapReaction state input upper reaction))

def gapEffect (state : State) (input : Input) (upper : ReceiveReassembly.Run)
    (recovery : Recovery.State) (reaction : AckReaction.State) : ReceiveEffect :=
  ⟨⟨gapAfter state input upper recovery reaction, .accepted (.receive 0 input.packet.segment.payload.length), none, [],
      some (ReceiveReassembly.request (gapAfter state input upper recovery reaction).core
        (offeredWindow (gapAfter state input upper recovery reaction)) .data)⟩,
    [gapLower state input, upper], some (gapStore state input upper), gapHeaders state input upper recovery, none⟩

theorem gapReceived_core (state : State) (input : Input) (upper : ReceiveReassembly.Run) (recovery : Recovery.State) :
    (gapReceived state input upper recovery).core =
      EstablishedReceive.commit state.core (input.packet.segment.payload ++ upper.bytes) 0 := by
  unfold gapReceived
  rw [zeroRunState_core, zeroRunState_core]
  change EstablishedReceive.commit (EstablishedReceive.commit state.core input.packet.segment.payload 0) upper.bytes 0 = _
  simp only [EstablishedReceive.commit, List.length_append, Seq.add_add, List.append_assoc, List.drop_zero, Seq.add_zero]

@[simp] theorem gapAfter_core (state : State) (input : Input) (upper : ReceiveReassembly.Run)
    (recovery : Recovery.State) (reaction : AckReaction.State) :
    (gapAfter state input upper recovery reaction).core =
      EstablishedReceive.commit state.core (input.packet.segment.payload ++ upper.bytes) 0 := by
  rw [gapAfter, storedState_core, gapReceived_core]

private theorem stored_recovery (state : State) (store : ReceiveReassembly.Store) (reaction : Option AckReaction.State) :
    (storedState state store reaction).recovery = state.recovery := rfl

private theorem stored_effectiveMSS (state : State) (store : ReceiveReassembly.Store) (reaction : Option AckReaction.State) :
    (storedState state store reaction).effectiveMSS = state.effectiveMSS := rfl

private theorem stored_ownMSS (state : State) (store : ReceiveReassembly.Store) (reaction : Option AckReaction.State) :
    (storedState state store reaction).localReceiveMSS = state.localReceiveMSS := rfl

private theorem stored_lastAckWindow (state : State) (store : ReceiveReassembly.Store) (reaction : Option AckReaction.State) :
    (storedState state store reaction).lastAckWindow = state.lastAckWindow := rfl

@[simp] theorem gapAfter_recovery (state : State) (input : Input) (upper : ReceiveReassembly.Run)
    (recovery : Recovery.State) (reaction : AckReaction.State) :
    (gapAfter state input upper recovery reaction).recovery = some { recovery with duplicateAcks := 0 } := by
  rw [gapAfter, stored_recovery, gapReceived, zeroRunState_recovery]

@[simp] theorem gapAfter_ackReaction (state : State) (input : Input) (upper : ReceiveReassembly.Run)
    (recovery : Recovery.State) (reaction : AckReaction.State) :
    (gapAfter state input upper recovery reaction).ackReaction = some (gapReaction state input upper reaction) := rfl

@[simp] theorem gapAfter_receiveStore (state : State) (input : Input) (upper : ReceiveReassembly.Run)
    (recovery : Recovery.State) (reaction : AckReaction.State) :
    (gapAfter state input upper recovery reaction).receiveStore = (gapStore state input upper).state := rfl

@[simp] theorem gapAfter_effectiveMSS (state : State) (input : Input) (upper : ReceiveReassembly.Run)
    (recovery : Recovery.State) (reaction : AckReaction.State) :
    (gapAfter state input upper recovery reaction).effectiveMSS = state.effectiveMSS := by
  rw [gapAfter, stored_effectiveMSS, gapReceived, zeroRunState_effectiveMSS, zeroRunState_effectiveMSS]

@[simp] theorem gapAfter_ownMSS (state : State) (input : Input) (upper : ReceiveReassembly.Run)
    (recovery : Recovery.State) (reaction : AckReaction.State) :
    (gapAfter state input upper recovery reaction).localReceiveMSS = state.localReceiveMSS := by
  rw [gapAfter, stored_ownMSS, gapReceived, zeroRunState_ownMSS, zeroRunState_ownMSS]

@[simp] theorem gapAfter_lastAckWindow (state : State) (input : Input) (upper : ReceiveReassembly.Run)
    (recovery : Recovery.State) (reaction : AckReaction.State) :
    (gapAfter state input upper recovery reaction).lastAckWindow = some upper.metadata.segment.window.val := by
  rw [gapAfter, stored_lastAckWindow, gapReceived, zeroRunState_lastAckWindow]

theorem GapReceiveConditions.core_fits (conditions : GapReceiveConditions state input upper recovery reaction) :
    input.packet.segment.payload.length + upper.bytes.length ≤ state.core.window :=
  Nat.le_trans conditions.total_fits (offeredWindow_le state conditions.prepared.1)

theorem GapReceiveConditions.gap_valid (conditions : GapReceiveConditions state input upper recovery reaction) :
    (gapAfter state input upper recovery reaction).Valid := by
  have first : (zeroRunState state recovery (gapLower state input)).Valid :=
    zeroRunState_valid _ _ _ conditions.valid (by
      change input.packet.segment.payload.length ≤ state.core.window
      have total := conditions.core_fits
      omega)
  apply storedState_valid
  apply zeroRunState_valid _ _ _ first
  simp only [zeroRunState_core, EstablishedReceive.commit_window]
  change upper.bytes.length ≤ state.core.window - input.packet.segment.payload.length
  have total := conditions.core_fits
  omega

private theorem processRuns_pair_enabled (state next final : State) (lower upper : ReceiveReassembly.Run)
    (first second : ReceiveReassembly.HeaderEffect)
    (firstCount : first.acknowledged = 0) (secondCount : second.acknowledged = 0)
    (lowerRun : ReceiveReassembly.applyRun state.core lower = .ok first)
    (lowerHeader : applyHeader state first = .ok next)
    (upperRun : ReceiveReassembly.applyRun next.core upper = .ok second)
    (upperHeader : applyHeader next second = .ok final) :
    processRuns state [lower, upper] = .ok ⟨final,
      ⟨second.after, 0, [first, second]⟩⟩ := by
  have core := (applyHeader_fields next second final upperHeader).2.1
  simp only [processRuns.eq_2, lowerRun, lowerHeader, upperRun, upperHeader, processRuns.eq_1, core,
    firstCount, secondCount, Nat.zero_add]

theorem processRuns_gap (conditions : GapReceiveConditions state input upper recovery reaction) :
    processRuns state [gapLower state input, upper] = .ok
      ⟨gapReceived state input upper recovery,
        ⟨(zeroHeader (zeroRunState state recovery (gapLower state input)) upper).after,
          0, gapHeaders state input upper recovery⟩⟩ := by
  have clock : state.now = recovery.now := by simp only [State.now, conditions.runtime, Option.map_some, Option.getD_some]
  have total := conditions.core_fits
  have lowerFits : (gapLower state input).bytes.length ≤ state.core.window := by
    change input.packet.segment.payload.length ≤ state.core.window
    omega
  have lower := applyRun_zero_enabled state (gapLower state input) conditions.valid rfl conditions.lowerTuple
    conditions.lowerControl conditions.lowerAck conditions.lowerSequence lowerFits conditions.lowerAckOld
  have appliedLower := applyHeader_zero_enabled state recovery (gapLower state input) conditions.runtime
    (show state.now ≤ recovery.now from Nat.le_of_eq clock)
  let first := zeroRunState state recovery (gapLower state input)
  have firstValid : first.Valid := zeroRunState_valid _ _ _ conditions.valid lowerFits
  have upperFits : upper.bytes.length ≤ first.core.window := by
    simp only [first, zeroRunState_core, EstablishedReceive.commit_window]
    change upper.bytes.length ≤ state.core.window - input.packet.segment.payload.length
    omega
  have tuple : upper.metadata.header = first.core.inbound := by
    simpa only [first, zeroRunState_core, EstablishedReceive.commit] using conditions.upperTuple
  have sequence : upper.metadata.segment.sequence = first.core.receiveNext := by
    simpa only [first, zeroRunState_core, EstablishedReceive.commit, gapLower, inOrderRun, ReceiveStore.current] using conditions.upperSequence
  have old : Seq.distance upper.metadata.segment.acknowledgment first.core.sendUna ≤ EstablishedReceive.maxSendWindow := by
    simpa only [first, zeroRunState_core, EstablishedReceive.commit, Seq.add_zero] using conditions.upperAckOld
  have appliedUpperRun := applyRun_zero_enabled first upper firstValid conditions.upperPayload tuple conditions.upperControl
    conditions.upperAck sequence upperFits old
  have appliedUpperHeader := applyHeader_zero_enabled first { recovery with duplicateAcks := 0 } upper
    (zeroRunState_recovery _ _ _) (by simpa only [clock] using conditions.upperPast)
  have finalHeader : applyHeader first (zeroHeader first upper) = .ok (gapReceived state input upper recovery) := by
    unfold gapReceived
    exact appliedUpperHeader
  have both := processRuns_pair_enabled state first (gapReceived state input upper recovery) (gapLower state input) upper
    (zeroHeader state (gapLower state input)) (zeroHeader first upper) rfl rfl lower appliedLower appliedUpperRun finalHeader
  have moved := congrArg (fun cursor : State =>
    ((.ok ⟨gapReceived state input upper recovery,
      ⟨(zeroHeader cursor upper).after, 0, [zeroHeader state (gapLower state input), zeroHeader cursor upper]⟩⟩) :
        Except ReceiveFailure ReceiveProcessed))
    (show first = zeroRunState state recovery (gapLower state input) from rfl)
  unfold gapHeaders
  exact both.trans moved

theorem gapAfter_window (state : State) (input : Input) (upper : ReceiveReassembly.Run)
    (recovery : Recovery.State) (reaction : AckReaction.State) :
    (gapAfter state input upper recovery reaction).core.window =
      state.core.window - (input.packet.segment.payload.length + upper.bytes.length) := by
  rw [gapAfter_core, EstablishedReceive.commit_window, List.length_append]

theorem gapAfter_cursor (state : State) (input : Input) (upper : ReceiveReassembly.Run)
    (recovery : Recovery.State) (reaction : AckReaction.State) :
    (gapAfter state input upper recovery reaction).core.receiveNext =
      state.core.receiveNext.add (input.packet.segment.payload.length + upper.bytes.length) := by
  rw [gapAfter_core]
  simp only [EstablishedReceive.commit, List.length_append]

theorem gapAfter_capacity (state : State) (input : Input) (upper : ReceiveReassembly.Run)
    (recovery : Recovery.State) (reaction : AckReaction.State) :
    (gapAfter state input upper recovery reaction).core.capacity = state.core.capacity := by
  rw [gapAfter_core]
  rfl

theorem GapReceiveConditions.gap_now (conditions : GapReceiveConditions state input upper recovery reaction) :
    (gapAfter state input upper recovery reaction).now = state.now := by
  simp only [State.now, gapAfter_recovery, conditions.runtime, Option.map_some, Option.getD_some]

theorem GapReceiveConditions.gap_recovery (conditions : GapReceiveConditions state input upper recovery reaction) :
    RecoveryCoherent (gapAfter state input upper recovery reaction) := by
  have old : recovery.Valid ∧ recovery.smss = state.effectiveMSS ∧
      Recovery.flight recovery = state.core.sent.length ∧ AckWindowKnown state := by
    simpa only [RecoveryCoherent, conditions.runtime] using conditions.coherent
  apply recoveryCoherent_of_runtime _ { recovery with duplicateAcks := 0 } (gapAfter_recovery _ _ _ _ _) old.1
  · simpa only [gapAfter_effectiveMSS] using old.2.1
  · simp only [Recovery.flight, conditions.idle, List.map_nil, List.sum_nil, gapAfter_core,
      EstablishedReceive.commit, List.drop_zero, conditions.sent_empty, List.length_nil]
  · exact ackWindowKnown_of_field _ upper.metadata.segment.window (gapAfter_lastAckWindow _ _ _ _ _)

theorem GapReceiveConditions.gap_ack (conditions : GapReceiveConditions state input upper recovery reaction) :
    AckCoherent (gapAfter state input upper recovery reaction) := by
  have old : state.recovery.isSome = true ∧ reaction.Coherent state.core.receiveNext state.core.window state.localReceiveMSS.limit := by
    simpa only [AckCoherent, conditions.ackRuntime] using conditions.prepared.1
  have fits : input.packet.segment.payload.length + upper.bytes.length ≤ reaction.window := by
    simpa only [offeredWindow, conditions.ackRuntime] using conditions.total_fits
  have changed := AckReaction.receiveRelease_coherent reaction state.now state.core.receiveNext
    input.packet.segment.payload.length (input.packet.segment.payload.length + upper.bytes.length) true
    state.core.window state.localReceiveMSS.limit old.2 fits
  unfold AckCoherent
  rw [gapAfter_ackReaction]
  refine ⟨by simp only [gapAfter_recovery, Option.isSome_some], ?_⟩
  simpa only [gapReaction, gapAfter_cursor, gapAfter_window, gapAfter_ownMSS] using changed

theorem GapReceiveConditions.gap_storage (conditions : GapReceiveConditions state input upper recovery reaction) :
    StorageCoherent (gapAfter state input upper recovery reaction) := by
  have old : reaction.advertisement.frontier = state.receiveStore.frontier ∧
      state.receiveStore.Valid (state.receiveStore.frontier + reaction.window) state.core.window := by
    simpa only [conditions.ackRuntime] using conditions.storage.2
  have next : (gapReaction state input upper reaction).Coherent
      (gapAfter state input upper recovery reaction).core.receiveNext
      (gapAfter state input upper recovery reaction).core.window
      (gapAfter state input upper recovery reaction).localReceiveMSS.limit := by
    have coherent := conditions.gap_ack
    simpa only [AckCoherent, gapAfter_ackReaction, gapAfter_recovery, Option.isSome_some, true_and] using coherent
  constructor
  · exact store_valid_empty _ _ _ rfl (Nat.le_refl _)
  · rw [gapAfter_ackReaction]
    constructor
    · change reaction.advertisement.frontier + (input.packet.segment.payload.length + upper.bytes.length) =
        state.receiveStore.frontier + input.packet.segment.payload.length + upper.bytes.length
      rw [old.1]
      omega
    · exact store_valid_empty _ _ _ rfl next.1.2

theorem GapReceiveConditions.gap_prepared (conditions : GapReceiveConditions state input upper recovery reaction) :
    AckPrepared (gapAfter state input upper recovery reaction) := by
  have oldAck : state.recovery.isSome = true ∧ reaction.Coherent state.core.receiveNext state.core.window state.localReceiveMSS.limit := by
    simpa only [AckCoherent, conditions.ackRuntime] using conditions.prepared.1
  have oldWork : reaction.WithinTime state.now ∧ reaction.Covered state.core.capacity state.core.window state.effectiveMSS := by
    simpa only [conditions.ackRuntime] using conditions.prepared.2
  have fits : input.packet.segment.payload.length + upper.bytes.length ≤ reaction.window := by
    simpa only [offeredWindow, conditions.ackRuntime] using conditions.total_fits
  have timely := AckReaction.receiveRelease_within reaction state.now
    (state.core.receiveNext.add (input.packet.segment.payload.length + upper.bytes.length)) input.packet.segment.payload.length
    (input.packet.segment.payload.length + upper.bytes.length) true oldWork.1
  have covered := AckReaction.receiveRelease_covered reaction state.now
    (state.core.receiveNext.add (input.packet.segment.payload.length + upper.bytes.length)) input.packet.segment.payload.length
    (input.packet.segment.payload.length + upper.bytes.length) true state.core.capacity state.core.window state.effectiveMSS
    oldWork.2 oldAck.2.1 fits
  apply ackPrepared_of_fields _ (gapReaction state input upper reaction) conditions.gap_ack (gapAfter_ackReaction _ _ _ _ _)
  · simpa only [gapReaction, conditions.gap_now] using timely
  · simpa only [gapReaction, gapAfter_capacity, gapAfter_window, gapAfter_effectiveMSS] using covered

theorem gapReaction_due (state : State) (input : Input) (upper : ReceiveReassembly.Run) (reaction : AckReaction.State) :
    ∃ due, (gapReaction state input upper reaction).due = some due ∧ due ≤ state.now := by
  have due := Theory.TimedReaction.issue_due reaction.work state.now
    (AckReaction.demand (gapReaction state input upper reaction) .data
      (state.core.receiveNext.add (input.packet.segment.payload.length + upper.bytes.length)) input.packet.segment.payload.length 0) 0
  change (gapReaction state input upper reaction).due = _ at due
  cases previous : Theory.TimedReaction.pendingDue reaction.work with
  | none => exact ⟨state.now, by simpa only [previous, Nat.add_zero] using due, Nat.le_refl _⟩
  | some deadline => exact ⟨min deadline state.now, by simpa only [previous, Nat.add_zero] using due, Nat.min_le_right _ _⟩

theorem GapReceiveConditions.gap_response (conditions : GapReceiveConditions state input upper recovery reaction) :
    ResponseAvailable (gapAfter state input upper recovery reaction) true := by
  unfold ResponseAvailable
  rw [gapAfter_ackReaction]
  refine ⟨receiveRelease_pending reaction state.now _ _ _ true, fun _ => ?_⟩
  simpa only [conditions.gap_now] using gapReaction_due state input upper reaction

private theorem receiveRaw_from_parts (state : State) (input : Input)
    (stored : ReceiveStore.Result ReceiveReassembly.Receipt) (received : State) (coreResult : ReceiveReassembly.Applied)
    (reaction : Option AckReaction.State) (after : State)
    (valid : state.Valid) (recovery : RecoveryCoherent state) (ack : AckCoherent state) (storage : StorageCoherent state)
    (plan : ReceiveReassembly.prepare state.core state.receiveStore input (offeredWindow state) state.now = .data stored)
    (processed : processRuns state stored.released = .ok ⟨received, coreResult⟩)
    (reacted : state.ackReaction.map (fun before => AckReaction.receiveRelease before state.now received.core.receiveNext
      stored.novel (ReceiveStore.size stored.released) (ReceiveReassembly.immediate state.core state.receiveStore input)) = reaction)
    (changed : storedState received stored.state reaction = after)
    (afterRecovery : RecoveryCoherent after) (afterAck : AckCoherent after) (afterStorage : StorageCoherent after) :
    receiveRaw state input =
      ⟨⟨after, .accepted (.receive coreResult.acknowledged stored.novel), none, [],
          some (ReceiveReassembly.request after.core (offeredWindow after) .data)⟩,
        stored.released, some stored, coreResult.headers, none⟩ := by
  have nextRecovery : RecoveryCoherent (storedState received stored.state reaction) := changed.symm ▸ afterRecovery
  have nextAck : AckCoherent (storedState received stored.state reaction) := changed.symm ▸ afterAck
  have nextStorage : StorageCoherent (storedState received stored.state reaction) := changed.symm ▸ afterStorage
  simp only [receiveRaw, valid, recovery, ack, storage, not_true_eq_false, ite_false, plan, processed, reacted]
  change (if ¬RecoveryCoherent (storedState received stored.state reaction) ∨
      ¬AckCoherent (storedState received stored.state reaction) ∨ ¬StorageCoherent (storedState received stored.state reaction)
    then _ else _) = _
  simp only [nextRecovery, nextAck, nextStorage, not_true_eq_false, or_self, ite_false]
  exact congrArg (fun value : State =>
    (⟨⟨value, .accepted (.receive coreResult.acknowledged stored.novel), none, [],
        some (ReceiveReassembly.request value.core (offeredWindow value) .data)⟩,
      stored.released, some stored, coreResult.headers, none⟩ : ReceiveEffect)) changed

theorem receiveRaw_gap (conditions : GapReceiveConditions state input upper recovery reaction) :
    receiveRaw state input = gapEffect state input upper recovery reaction := by
  have immediate : ReceiveReassembly.immediate state.core state.receiveStore input = true := by
    simp only [ReceiveReassembly.immediate, conditions.held, List.isEmpty_cons, Bool.not_false, Bool.or_true]
  have reacted : state.ackReaction.map (fun before => AckReaction.receiveRelease before state.now
      (gapReceived state input upper recovery).core.receiveNext (gapStore state input upper).novel
      (ReceiveStore.size (gapStore state input upper).released)
      (ReceiveReassembly.immediate state.core state.receiveStore input)) = some (gapReaction state input upper reaction) := by
    simp only [conditions.ackRuntime, Option.map_some, immediate, gapReceived_core, EstablishedReceive.commit,
      List.length_append, gapStore, ReceiveStore.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      gapLower, inOrderRun, ReceiveStore.current, Nat.add_zero]
    rfl
  exact receiveRaw_from_parts state input (gapStore state input upper) (gapReceived state input upper recovery)
    ⟨(zeroHeader (zeroRunState state recovery (gapLower state input)) upper).after, 0, gapHeaders state input upper recovery⟩
    (some (gapReaction state input upper reaction)) (gapAfter state input upper recovery reaction)
    conditions.valid conditions.coherent conditions.prepared.1 conditions.storage (prepare_frontier_one conditions)
    (processRuns_gap conditions) reacted rfl conditions.gap_recovery conditions.gap_ack conditions.gap_storage

structure GapFilled (state : State) (input : Input) (upper : ReceiveReassembly.Run)
    (recovery : Recovery.State) (reaction : AckReaction.State) : Prop where
  actual : receiveEffect state input = gapEffect state input upper recovery reaction
  valid : (gapAfter state input upper recovery reaction).Valid
  coherent : RecoveryCoherent (gapAfter state input upper recovery reaction)
  prepared : AckPrepared (gapAfter state input upper recovery reaction)
  storage : StorageCoherent (gapAfter state input upper recovery reaction)
  response : ResponseAvailable (gapAfter state input upper recovery reaction) true

theorem receive_gap_enabled (conditions : GapReceiveConditions state input upper recovery reaction) :
    GapFilled state input upper recovery reaction := by
  refine ⟨?_, conditions.gap_valid, conditions.gap_recovery, conditions.gap_prepared, conditions.gap_storage, conditions.gap_response⟩
  simp only [receiveEffect, receiveRaw_gap conditions, gapEffect, conditions.gap_valid,
    conditions.gap_storage.1, and_self, ite_true]

theorem GapFilled.receive (filled : GapFilled state input upper recovery reaction) :
    receive state input =
      ⟨gapAfter state input upper recovery reaction, .accepted (.receive 0 input.packet.segment.payload.length), none, [],
        some (ReceiveReassembly.request (gapAfter state input upper recovery reaction).core
          (offeredWindow (gapAfter state input upper recovery reaction)) .data)⟩ :=
  congrArg ReceiveEffect.result filled.actual

theorem GapFilled.runs (filled : GapFilled state input upper recovery reaction) :
    receiveRuns state input = [gapLower state input, upper] := congrArg ReceiveEffect.runs filled.actual

theorem GapFilled.bytes (filled : GapFilled state input upper recovery reaction) :
    receivedBytes state input = input.packet.segment.payload ++ upper.bytes := by
  rw [receivedBytes, filled.runs]
  simp only [ReceiveStore.bytes, List.flatMap_cons, List.flatMap_nil, gapLower, inOrderRun, ReceiveStore.current, List.append_nil]

theorem GapFilled.headers (filled : GapFilled state input upper recovery reaction) :
    (receiveEffect state input).headers = gapHeaders state input upper recovery := congrArg ReceiveEffect.headers filled.actual

theorem GapFilled.header_receipts (filled : GapFilled state input upper recovery reaction) :
    (receiveEffect state input).headers.map (fun header =>
      (header.run.receipt, header.run.metadata.receivedAt, header.acknowledged)) =
      [(state.receiveStore.nextID, state.now, 0), (upper.receipt, upper.metadata.receivedAt, 0)] := by
  rw [filled.headers]
  rfl

theorem GapFilled.response_any (filled : GapFilled state input upper recovery reaction) :
    ResponseAvailable (gapAfter state input upper recovery reaction) false := by
  have available := filled.response
  simp only [ResponseAvailable, gapAfter_ackReaction] at available ⊢
  exact ⟨available.1, fun impossible => by cases impossible⟩

theorem GapFilled.emit_ack (filled : GapFilled state input upper recovery reaction) :
    ∃ output, emitAck (gapAfter state input upper recovery reaction) true =
        ⟨outputState (gapAfter state input upper recovery reaction), .accepted .emitAck, some output, [], none⟩ ∧
      emit (gapAfter state input upper recovery reaction) [] = .ok output ∧
      output.packet.segment.payload = [] ∧
      output.packet.segment.acknowledgment = state.core.receiveNext.add (input.packet.segment.payload.length + upper.bytes.length) ∧
      AckPrepared (outputState (gapAfter state input upper recovery reaction)) := by
  obtain ⟨output, actual, encoded⟩ := emitAck_success_enabled _ filled.valid filled.prepared filled.response_any
  have fields := emit_transport _ [] output encoded
  exact ⟨output, actual, encoded, emit_payload _ [] output encoded,
    fields.2.2.1.trans (gapAfter_cursor _ _ _ _ _), outputState_ackPrepared _ filled.prepared⟩

theorem gapAfter_output_ttl (output : Input)
    (encoded : emit (gapAfter state input upper recovery reaction) [] = .ok output) :
    output.packet.ip.packet.ttl.toNat = 64 := by
  have actual : Output.emitAtWindow (gapAfter state input upper recovery reaction).core
      (gapAfter state input upper recovery reaction).core.sendNext (outputWindow (gapAfter state input upper recovery reaction)) [] = .ok output := by
    simpa only [emit, gapAfter_ackReaction, Output.emitWindow] using encoded
  rw [(Output.emitAtWindow_fields _ _ _ _ _ actual).2.2.2.2]
  rfl

theorem GapFilled.dispatch (filled : GapFilled state input upper recovery reaction) :
    ∃ output, dispatchAck (gapAfter state input upper recovery reaction) true =
        ⟨outputState (gapAfter state input upper recovery reaction), .accepted .dispatchAck, some output, [], none⟩ ∧
      emit (gapAfter state input upper recovery reaction) [] = .ok output ∧
      output.packet.segment.payload = [] ∧
      output.packet.header = Output.reverse state.core.inbound ∧
      output.packet.segment.sequence = state.core.sendNext ∧
      output.packet.segment.acknowledgment = state.core.receiveNext.add (input.packet.segment.payload.length + upper.bytes.length) ∧
      output.packet.segment.window.val = outputWindow (gapAfter state input upper recovery reaction) ∧
      AckPrepared (outputState (gapAfter state input upper recovery reaction)) := by
  obtain ⟨output, actual, encoded⟩ := dispatchAck_success_enabled _ filled.valid filled.prepared filled.response
  have fields := emit_transport _ [] output encoded
  refine ⟨output, actual, encoded, emit_payload _ [] output encoded, ?_, ?_, ?_, fields.2.2.2.1,
    outputState_ackPrepared _ filled.prepared⟩
  · simpa only [gapAfter_core, EstablishedReceive.commit] using fields.1
  · simpa only [gapAfter_core, EstablishedReceive.commit] using fields.2.1
  · exact fields.2.2.1.trans (gapAfter_cursor _ _ _ _ _)

end Netlib.Protocol.TCP.Endpoint
