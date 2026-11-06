import Netlib.Protocol.TCP.Output
import Netlib.Protocol.TCP.Recovery
import Netlib.Protocol.TCP.AckReaction

/-!
# Bounded application operations for a TCP endpoint

The initial state assumes an established connection and peer-window history.
The effective MSS and IP size limit are explicit configuration inputs.
The policy input permits one selected output. It does not prove congestion control.
Serial window comparisons need a separate bound on the age of window history.
The state validity predicate does not supply that bound.
Optional recovery adds bounded established-data timer retries.
Window probing, fast recovery, and connection-control processing remain outside this profile.
-/

namespace Netlib.Protocol.TCP.Endpoint

abbrev ERState := EstablishedReceive.State
abbrev Input := EstablishedReceive.Input

structure State where
  core : ERState
  pending : List UInt8
  pendingLimit : Nat
  sendWindow : Nat
  sendWL1 : Seq
  sendWL2 : Seq
  effectiveMSS : Nat
  ipSendLimit : Nat
  recovery : Option Recovery.State := none
  lastAckWindow : Option Nat := none
  localReceiveMSS : MSS.Offer := .absent
  ackReaction : Option AckReaction.State := none
  deriving Repr, BEq, DecidableEq

def State.Valid (state : State) : Prop :=
  state.core.Valid ∧ state.pending.length ≤ state.pendingLimit ∧ state.pendingLimit ≤ 65535 ∧
    state.sendWindow ≤ 65535 ∧ 0 < state.effectiveMSS ∧
    40 + state.effectiveMSS ≤ state.ipSendLimit ∧ state.ipSendLimit ≤ 65535

instance (state : State) : Decidable state.Valid := by
  unfold State.Valid
  infer_instance

def State.now (state : State) : Nat := (state.recovery.map (·.now)).getD 0

def AckWindowKnown (state : State) : Prop :=
  match state.lastAckWindow with | none => False | some window => window ≤ 65535

instance (state : State) : Decidable (AckWindowKnown state) := by
  unfold AckWindowKnown
  split <;> infer_instance

def RecoveryCoherent (state : State) : Prop :=
  match state.recovery with
  | none => True
  | some recovery => recovery.Valid ∧ recovery.smss = state.effectiveMSS ∧ Recovery.flight recovery = state.core.sent.length ∧ AckWindowKnown state

instance (state : State) : Decidable (RecoveryCoherent state) := by
  unfold RecoveryCoherent
  split <;> infer_instance

def recoveryReady (state : State) (count : Nat) : Prop :=
  match state.recovery with
  | none => True
  | some recovery => RecoveryCoherent state ∧ Recovery.SendReady recovery count

instance (state : State) (count : Nat) : Decidable (recoveryReady state count) := by
  unfold recoveryReady
  split <;> infer_instance

inductive Accepted where
  | write (count : Nat)
  | send (count : Nat)
  | read (count : Nat)
  | emitAck
  | enableRecovery | advanceClock | retry (count : Nat)
  | enableAck | dispatchAck
  | receive (acknowledged received : Nat)
  deriving Repr, BEq, DecidableEq

inductive Reject where
  | invalidSeed | pendingCapacity | readBounds | sendBounds | policy | encoding
  | input (reason : EstablishedReceive.Reject)
  | recovery (reason : Recovery.Stop)
  | ack (reason : AckReaction.Stop)
  deriving Repr, BEq, DecidableEq

inductive Decision where
  | accepted (action : Accepted)
  | reject (reason : Reject)
  | unsupported (reason : EstablishedReceive.Unsupported)
  | recoveryUnsupported (reason : Recovery.Stop)
  | ackUnsupported (reason : AckReaction.Stop)
  deriving Repr, BEq, DecidableEq

structure Result where
  state : State
  decision : Decision
  output : Option Input := none
  read : List UInt8 := []
  ack : Option EstablishedReceive.AckRequest := none

def rejected (state : State) (reason : Reject) : Result := ⟨state, .reject reason, none, [], none⟩

def recoveryBlocked (state : State) (reason : Recovery.Stop) : Result :=
  if reason.unsupported then ⟨state, .recoveryUnsupported reason, none, [], none⟩
  else rejected state (.recovery reason)

def enableRecovery (state : State) : Result :=
  if ¬state.Valid then rejected state .invalidSeed
  else if state.recovery.isSome || !state.core.sent.isEmpty then recoveryBlocked state .ledger
  else ⟨{ state with recovery := some (Recovery.initial state.effectiveMSS), lastAckWindow := some state.sendWindow }, .accepted .enableRecovery, none, [], none⟩

def AckCoherent (state : State) : Prop :=
  match state.ackReaction with
  | none => True
  | some reaction => state.recovery.isSome = true ∧
      reaction.Coherent state.core.receiveNext state.core.window state.localReceiveMSS.limit

instance (state : State) : Decidable (AckCoherent state) := by
  unfold AckCoherent
  split <;> infer_instance

def ackBlocked (state : State) (reason : AckReaction.Stop) : Result :=
  if reason.unsupported then ⟨state, .ackUnsupported reason, none, [], none⟩
  else rejected state (.ack reason)

def outputWindow (state : State) : Nat :=
  match state.ackReaction with
  | none => state.core.window
  | some reaction => AckReaction.candidate reaction state.core.capacity state.core.window state.effectiveMSS

def emit (state : State) (payload : List UInt8) : Except String Input :=
  match state.ackReaction with
  | none => Output.emit state.core payload
  | some _ => Output.emitWindow state.core (outputWindow state) payload

def emitAt (state : State) (sequence : Seq) (payload : List UInt8) : Except String Input :=
  match state.ackReaction with
  | none => Output.emitAt state.core sequence payload
  | some _ => Output.emitAtWindow state.core sequence (outputWindow state) payload

def ackReady (state : State) : Except AckReaction.Stop Unit :=
  if ¬AckCoherent state then .error .ledger
  else match state.ackReaction with
    | none => .ok ()
    | some reaction => AckReaction.outputReady reaction state.now state.core.receiveNext
        state.core.capacity state.core.window state.effectiveMSS

def outputState (state : State) : State :=
  { state with ackReaction := state.ackReaction.map (fun reaction =>
      AckReaction.outputState reaction state.now state.core.receiveNext
        state.core.capacity state.core.window state.effectiveMSS) }

def enableAck (state : State) : Result :=
  if ¬state.Valid then rejected state .invalidSeed
  else if ¬RecoveryCoherent state then recoveryBlocked state .ledger
  else if state.ackReaction.isSome then ackBlocked state .alreadyEnabled
  else if state.recovery.isNone then ackBlocked state .disabled
  else if !state.core.received.isEmpty || !state.core.sent.isEmpty then ackBlocked state .ledger
  else ⟨{ state with ackReaction := some (AckReaction.initial state.core.receiveNext
      state.core.capacity state.localReceiveMSS.limit) }, .accepted .enableAck, none, [], none⟩

def advanceClock (state : State) (millis : Nat) : Result :=
  if ¬state.Valid then rejected state .invalidSeed
  else if ¬RecoveryCoherent state then recoveryBlocked state .ledger
  else match state.recovery with
    | none => recoveryBlocked state .idle
    | some recovery => match Recovery.advance recovery millis with
      | .error reason => recoveryBlocked state reason
      | .ok after =>
        match state.ackReaction with
        | none => ⟨{ state with recovery := some after }, .accepted .advanceClock, none, [], none⟩
        | some reaction => match AckReaction.checkTime reaction millis with
          | .error reason => ackBlocked state reason
          | .ok () => ⟨{ state with recovery := some after }, .accepted .advanceClock, none, [], none⟩

def timeout (state : State) (policy : Bool) : Result :=
  if ¬state.Valid then rejected state .invalidSeed
  else if ¬RecoveryCoherent state then recoveryBlocked state .ledger
  else match state.recovery with
    | none => recoveryBlocked state .idle
    | some recovery => match Recovery.timeout recovery with
      | .error reason => recoveryBlocked state reason
      | .ok (count, after) =>
        if !policy then rejected state .policy
        else if count > state.sendWindow then recoveryBlocked state .persist
        else if count > state.core.sent.length ∨ count > state.effectiveMSS ∨ 40 + count > state.ipSendLimit then
          recoveryBlocked state .ledger
        else match ackReady state with
          | .error reason => ackBlocked state reason
          | .ok () => match emitAt state state.core.sendUna (state.core.sent.take count) with
            | .error _ => rejected state .encoding
            | .ok output => ⟨{ outputState state with recovery := some after },
                .accepted (.retry count), some output, [], none⟩

def writeState (state : State) (bytes : List UInt8) : State :=
  { state with pending := state.pending ++ bytes }

def readState (state : State) (count : Nat) : State :=
  let after := { state.core with received := state.core.received.drop count }
  { state with core := after, ackReaction := state.ackReaction.map (fun reaction =>
      AckReaction.read reaction state.now state.core.receiveNext state.core.capacity
        state.core.window after.window state.effectiveMSS) }

def sendState (state : State) (count : Nat) : State :=
  { outputState state with
    pending := state.pending.drop count
    core := { state.core with
      sent := state.core.sent ++ state.pending.take count
      sendNext := state.core.sendNext.add count }
    recovery := state.recovery.map (fun value => Recovery.sent value count) }

def write (state : State) (bytes : List UInt8) : Result :=
  if ¬state.Valid then rejected state .invalidSeed
  else if state.pending.length + bytes.length > state.pendingLimit then rejected state .pendingCapacity
  else ⟨writeState state bytes, .accepted (.write bytes.length), none, [], none⟩

def read (state : State) (count : Nat) : Result :=
  if ¬state.Valid then rejected state .invalidSeed
  else if count > state.core.received.length then rejected state .readBounds
  else ⟨readState state count, .accepted (.read count), none, state.core.received.take count, none⟩

def SendReady (state : State) (count : Nat) : Prop :=
  0 < count ∧ count ≤ state.pending.length ∧
    state.core.sent.length + count ≤ state.sendWindow ∧
    state.core.sent.length + count ≤ EstablishedReceive.maxSendWindow ∧
    count ≤ state.effectiveMSS ∧ 40 + count ≤ state.ipSendLimit ∧ recoveryReady state count

instance (state : State) (count : Nat) : Decidable (SendReady state count) := by
  unfold SendReady
  infer_instance

def send (state : State) (count : Nat) (policyPermitted : Bool) : Result :=
  if ¬state.Valid then rejected state .invalidSeed
  else if !policyPermitted then rejected state .policy
  else if ¬SendReady state count then
    if state.recovery.isSome && decide (state.sendWindow = 0) then recoveryBlocked state .persist
    else rejected state .sendBounds
  else match ackReady state with
    | .error reason => ackBlocked state reason
    | .ok () => match emit state (state.pending.take count) with
      | .error _ => rejected state .encoding
      | .ok output => ⟨sendState state count, .accepted (.send count), some output, [], none⟩

def responseReady (state : State) (dueOnly : Bool) : Except AckReaction.Stop Unit :=
  match state.ackReaction with
  | none => if dueOnly then .error AckReaction.Stop.disabled else .ok ()
  | some reaction => AckReaction.responseReady reaction state.now dueOnly

def pureAck (state : State) (policyPermitted dueOnly : Bool) : Result :=
  if ¬state.Valid then rejected state .invalidSeed
  else if !policyPermitted then rejected state .policy
  else match responseReady state dueOnly with
    | .error reason => ackBlocked state reason
    | .ok () => match ackReady state with
      | .error reason => ackBlocked state reason
      | .ok () => match emit state [] with
        | .error _ => rejected state .encoding
        | .ok output => ⟨outputState state,
            .accepted (if dueOnly then .dispatchAck else .emitAck), some output, [], none⟩

def emitAck (state : State) (policyPermitted : Bool) : Result := pureAck state policyPermitted false

def dispatchAck (state : State) (policyPermitted : Bool) : Result := pureAck state policyPermitted true

def windowFresh (state : State) (segment : Segment) : Bool :=
  Seq.before state.sendWL1 segment.sequence ||
    (decide (state.sendWL1 = segment.sequence) &&
      (decide (state.sendWL2 = segment.acknowledgment) || Seq.before state.sendWL2 segment.acknowledgment))

def windowEligible (state : State) (segment : Segment) : Bool :=
  decide (Seq.distance state.core.sendUna segment.acknowledgment ≤ state.core.sent.length) &&
    windowFresh state segment

def windowState (before after : State) (segment : Segment) : State :=
  if windowEligible before segment then
    { after with sendWindow := segment.window.val, sendWL1 := segment.sequence, sendWL2 := segment.acknowledgment }
  else after

def receiveState (state : State) (value : Input) (after : ERState) : State :=
  windowState state
    { state with
      core := after
      lastAckWindow := if state.recovery.isSome then some value.packet.segment.window.val else state.lastAckWindow }
    value.packet.segment

def qualifyingDuplicate (state : State) (segment : Segment) (count : Nat) : Bool :=
  decide (count = 0 ∧ state.core.sent ≠ [] ∧ segment.payload = [] ∧
    segment.acknowledgment = state.core.sendUna ∧ segment.window.val = state.lastAckWindow.getD state.sendWindow)

def receiveRecovery (state : State) (segment : Segment) (count : Nat) : Except Recovery.Stop (Option Recovery.State) :=
  match state.recovery with
  | none => .ok none
  | some recovery => do
    let after ← Recovery.acknowledge recovery count
    if qualifyingDuplicate state segment count then some <$> Recovery.duplicate after
    else return some { after with duplicateAcks := 0 }

def receiveModel (state : State) (value : Input) : EstablishedReceive.Result :=
  match state.ackReaction with
  | none => EstablishedReceive.receive state.core value
  | some reaction => EstablishedReceive.receiveWithWindow state.core value reaction.window

def issueRequest (state : State) (after : ERState) (request : Option EstablishedReceive.AckRequest)
    (size : Nat) : Except AckReaction.Stop (Option AckReaction.State) :=
  match state.ackReaction with
  | none => .ok none
  | some reaction =>
    match request with
    | none => .ok (some reaction)
    | some request => match request.kind with
      | .data => .ok (some (AckReaction.receiveData reaction state.now after.receiveNext size))
      | .sequence => .ok (some (AckReaction.receiveSequence reaction state.now after.receiveNext))
      | .challenge => .error .challenge

def receive (state : State) (value : Input) : Result :=
  if ¬state.Valid then rejected state .invalidSeed
  else if ¬RecoveryCoherent state then recoveryBlocked state .ledger
  else if ¬AckCoherent state then ackBlocked state .ledger
  else
    let result := receiveModel state value
    match result.decision with
    | .blocked (.reject reason) =>
      match issueRequest state state.core result.ack 0 with
      | .error reason => ackBlocked state reason
      | .ok ackReaction => ⟨{ state with ackReaction }, .reject (.input reason), none, [], result.ack⟩
    | .blocked (.unsupported reason) => ⟨state, .unsupported reason, none, [], result.ack⟩
    | .accepted count size =>
      match receiveRecovery state value.packet.segment count with
      | .error reason => recoveryBlocked state reason
      | .ok recovery =>
        match issueRequest state result.state result.ack size with
        | .error reason => ackBlocked state reason
        | .ok ackReaction =>
          ⟨{ receiveState state value result.state with recovery, ackReaction },
            .accepted (.receive count size), none, [], result.ack⟩

@[simp] theorem outputState_core (state : State) : (outputState state).core = state.core := rfl
@[simp] theorem outputState_pending (state : State) : (outputState state).pending = state.pending := rfl

theorem ackBlocked_state (state : State) (reason : AckReaction.Stop) : (ackBlocked state reason).state = state := by
  unfold ackBlocked
  split <;> rfl

theorem emit_payload (state : State) (payload : List UInt8) (output : Input)
    (encoded : emit state payload = .ok output) : output.packet.segment.payload = payload := by
  cases selected : state.ackReaction with
  | none => exact Output.emit_payload state.core payload output (by simpa only [emit, selected] using encoded)
  | some reaction => exact Output.emitWindow_payload state.core (outputWindow state) payload output (by simpa only [emit, selected] using encoded)

theorem emit_transport (state : State) (payload : List UInt8) (output : Input)
    (encoded : emit state payload = .ok output) :
    output.packet.header = Output.reverse state.core.inbound ∧
      output.packet.segment.sequence = state.core.sendNext ∧
      output.packet.segment.acknowledgment = state.core.receiveNext ∧
      output.packet.segment.window.val = outputWindow state ∧
      output.packet.segment.flags = 16 ∧ output.packet.segment.reserved = 0 ∧
      output.packet.segment.options = [] ∧ output.packet.segment.urgentPointer = 0 := by
  cases selected : state.ackReaction with
  | none => simpa only [outputWindow, selected] using Output.emit_transport state.core payload output (by simpa only [emit, selected] using encoded)
  | some reaction => exact Output.emitWindow_transport state.core (outputWindow state) payload output (by simpa only [emit, selected] using encoded)

theorem emitAt_payload (state : State) (sequence : Seq) (payload : List UInt8) (output : Input)
    (encoded : emitAt state sequence payload = .ok output) : output.packet.segment.payload = payload := by
  cases selected : state.ackReaction with
  | none => exact Output.emitAt_payload state.core sequence payload output (by simpa only [emitAt, selected] using encoded)
  | some reaction => exact Output.emitAtWindow_payload state.core sequence (outputWindow state) payload output (by simpa only [emitAt, selected] using encoded)

theorem emitAt_transport (state : State) (sequence : Seq) (payload : List UInt8) (output : Input)
    (encoded : emitAt state sequence payload = .ok output) :
    output.packet.header = Output.reverse state.core.inbound ∧
      output.packet.segment.sequence = sequence ∧
      output.packet.segment.acknowledgment = state.core.receiveNext ∧
      output.packet.segment.window.val = outputWindow state ∧
      output.packet.segment.flags = 16 ∧ output.packet.segment.reserved = 0 ∧
      output.packet.segment.options = [] ∧ output.packet.segment.urgentPointer = 0 := by
  cases selected : state.ackReaction with
  | none => simpa only [outputWindow, selected] using Output.emitAt_transport state.core sequence payload output (by simpa only [emitAt, selected] using encoded)
  | some reaction => exact Output.emitAtWindow_transport state.core sequence (outputWindow state) payload output (by simpa only [emitAt, selected] using encoded)

theorem receiveModel_effects (state : State) (value : Input) :
    EstablishedReceive.Effects state.core value.packet.segment (receiveModel state value) := by
  cases selected : state.ackReaction with
  | none => simpa only [receiveModel, selected] using EstablishedReceive.receive_effects state.core value
  | some reaction => simpa only [receiveModel, selected] using EstablishedReceive.receiveWithWindow_effects state.core value reaction.window

theorem receiveModel_valid (state : State) (value : Input) (valid : state.Valid) :
    (receiveModel state value).state.Valid := by
  cases selected : state.ackReaction with
  | none => simpa only [receiveModel, selected] using EstablishedReceive.receive_valid state.core value valid.1
  | some reaction => simpa only [receiveModel, selected] using EstablishedReceive.receiveWithWindow_valid state.core value reaction.window valid.1


theorem receiveState_recovery (state : State) (value : Input) (after : ERState) :
    (receiveState state value after).recovery = state.recovery := by
  unfold receiveState windowState
  split <;> rfl

theorem receive_without_recovery (state : State) (value : Input) (valid : state.Valid)
    (disabled : state.recovery = none) (ackDisabled : state.ackReaction = none) :
    receive state value =
      let result := EstablishedReceive.receive state.core value
      match result.decision with
      | .blocked (.reject reason) => ⟨state, .reject (.input reason), none, [], result.ack⟩
      | .blocked (.unsupported reason) => ⟨state, .unsupported reason, none, [], result.ack⟩
      | .accepted count size =>
        ⟨receiveState state value result.state, .accepted (.receive count size), none, [], result.ack⟩ := by
  have coherent : RecoveryCoherent state := by simp only [RecoveryCoherent, disabled]
  have ackCoherent : AckCoherent state := by simp only [AckCoherent, ackDisabled]
  simp only [receive, valid, coherent, ackCoherent, not_true_eq_false, ite_false, receiveModel, ackDisabled]
  cases selected : (EstablishedReceive.receive state.core value).decision with
  | blocked reason =>
    cases reason
    · simp only [issueRequest, ackDisabled]
      rw [← ackDisabled]
    · rfl
  | accepted count size =>
    simp only [receiveRecovery, disabled, issueRequest, ackDisabled]
    unfold receiveState windowState
    split <;> simp only [disabled, ackDisabled]

theorem writeState_valid (state : State) (bytes : List UInt8) (valid : state.Valid)
    (fits : state.pending.length + bytes.length ≤ state.pendingLimit) :
    (writeState state bytes).Valid := by
  exact ⟨valid.1, by simpa [writeState] using fits, valid.2.2⟩

theorem readState_valid (state : State) (count : Nat) (valid : state.Valid) :
    (readState state count).Valid := by
  refine ⟨?_, valid.2⟩
  obtain ⟨protocol, received, capacity, sent, cursor, short⟩ := valid.1
  refine ⟨protocol, ?_, capacity, sent, cursor, short⟩
  change (state.core.received.drop count).length ≤ state.core.capacity
  rw [List.length_drop]
  omega

theorem sendState_valid (state : State) (count : Nat) (valid : state.Valid) (ready : SendReady state count) :
    (sendState state count).Valid := by
  obtain ⟨positive, pending, _, bounded, _, _⟩ := ready
  obtain ⟨protocol, received, capacity, sent, cursor, short⟩ := valid.1
  have takeLength : (state.pending.take count).length = count := by
    simpa [List.length_take] using Nat.min_eq_left pending
  refine ⟨⟨protocol, received, capacity, ?_, ?_, ?_⟩, ?_, valid.2.2⟩
  · change (state.core.sent ++ state.pending.take count).length ≤ EstablishedReceive.maxSendWindow
    simpa only [List.length_append, takeLength] using bounded
  · change state.core.sendUna.add (state.core.sent ++ state.pending.take count).length = state.core.sendNext.add count
    rw [List.length_append, takeLength, ← Seq.add_add, cursor]
  · change (state.core.sent ++ state.pending.take count).length + EstablishedReceive.maxSendWindow < Seq.halfSpace
    rw [List.length_append, takeLength]
    unfold EstablishedReceive.maxSendWindow Seq.halfSpace at *
    omega
  · change (state.pending.drop count).length ≤ state.pendingLimit
    rw [List.length_drop]
    have pendingBound := valid.2.1
    omega

theorem windowState_valid (before after : State) (segment : Segment) (valid : after.Valid) :
    (windowState before after segment).Valid := by
  unfold windowState
  split
  · refine ⟨valid.1, valid.2.1, valid.2.2.1, ?_, valid.2.2.2.2⟩
    change segment.window.val ≤ 65535
    have bound := segment.window.isLt
    omega
  · exact valid

theorem receiveState_valid (state : State) (value : Input) (after : ERState)
    (valid : state.Valid) (retained : after.Valid) : (receiveState state value after).Valid :=
  windowState_valid _ _ _ ⟨retained, valid.2⟩

theorem write_of_fits (state : State) (bytes : List UInt8) (valid : state.Valid)
    (fits : state.pending.length + bytes.length ≤ state.pendingLimit) :
    write state bytes = ⟨writeState state bytes, .accepted (.write bytes.length), none, [], none⟩ := by
  simp only [write, valid, not_true_eq_false, ite_false, Nat.not_lt.mpr fits]

theorem read_of_fits (state : State) (count : Nat) (valid : state.Valid)
    (fits : count ≤ state.core.received.length) :
    read state count = ⟨readState state count, .accepted (.read count), none, state.core.received.take count, none⟩ := by
  simp only [read, valid, not_true_eq_false, ite_false, Nat.not_lt.mpr fits]

theorem ackReady_coherent (state : State) (ready : ackReady state = .ok ()) : AckCoherent state := by
  unfold ackReady at ready
  split at ready
  · cases ready
  · exact Decidable.not_not.mp ‹¬¬AckCoherent state›

theorem outputWindow_le (state : State) (coherent : AckCoherent state) : outputWindow state ≤ state.core.window := by
  cases selected : state.ackReaction with
  | none => simp only [outputWindow, selected, Nat.le_refl]
  | some reaction =>
    simp only [AckCoherent, selected] at coherent
    have valid : reaction.advertisement.Valid state.core.window := coherent.2.1
    simpa only [outputWindow, selected, AckReaction.candidate] using
      (ReceiveAdvertisement.candidate_bounds reaction.advertisement state.core.capacity state.core.window state.effectiveMSS valid).2

theorem emit_exists (state : State) (payload : List UInt8) (valid : state.Valid)
    (coherent : AckCoherent state) (bounded : 40 + payload.length ≤ 65535) :
    ∃ output, emit state payload = .ok output := by
  cases selected : state.ackReaction with
  | none => simpa only [emit, selected] using Output.emit_exists state.core payload valid.1 bounded
  | some reaction =>
    simpa only [emit, selected] using Output.emitWindow_exists state.core (outputWindow state) payload
      valid.1 (outputWindow_le state coherent) bounded

theorem send_of_ready (state : State) (count : Nat) (valid : state.Valid)
    (ready : SendReady state count) (prepared : ackReady state = .ok ()) (output : Input)
    (encoded : emit state (state.pending.take count) = .ok output) :
    send state count true = ⟨sendState state count, .accepted (.send count), some output, [], none⟩ := by
  simp only [send, valid, not_true_eq_false, ite_false, Bool.not_true, Bool.false_eq_true, ready, prepared, encoded]

theorem send_success (state : State) (count : Nat) (valid : state.Valid)
    (ready : SendReady state count) (prepared : ackReady state = .ok ()) :
    ∃ output, send state count true =
      ⟨sendState state count, .accepted (.send count), some output, [], none⟩ := by
  have length : (state.pending.take count).length = count := by
    simp only [List.length_take, Nat.min_eq_left ready.2.1]
  have bounded : 40 + (state.pending.take count).length ≤ 65535 := by
    rw [length]
    have packetBound := ready.2.2.2.2.2.1
    have ipBound := valid.2.2.2.2.2.2
    omega
  obtain ⟨output, encoded⟩ := emit_exists state (state.pending.take count) valid (ackReady_coherent state prepared) bounded
  exact ⟨output, send_of_ready state count valid ready prepared output encoded⟩

theorem emitAck_success (state : State) (valid : state.Valid) (disabled : state.ackReaction = none) :
    ∃ output, emitAck state true = ⟨state, .accepted .emitAck, some output, [], none⟩ := by
  obtain ⟨output, encoded⟩ := Output.emit_exists state.core [] valid.1 (by decide)
  refine ⟨output, ?_⟩
  simp only [emitAck, pureAck, responseReady, valid, not_true_eq_false, ite_false, Bool.not_true, Bool.false_eq_true,
    disabled, ackReady, AckCoherent, emit, encoded, outputState, Option.map_none]
  rw [← disabled]

theorem readState_window (state : State) (count : Nat) (valid : state.Valid)
    (fits : count ≤ state.core.received.length) :
    (readState state count).core.window = state.core.window + count := by
  have buffered := valid.1.2.1
  simp only [readState, EstablishedReceive.State.window, List.length_drop]
  omega

theorem write_valid (state : State) (bytes : List UInt8) (valid : state.Valid) :
    (write state bytes).state.Valid := by
  unfold write
  split
  · exact valid
  · split
    · exact valid
    · apply writeState_valid state bytes valid
      omega

theorem read_valid (state : State) (count : Nat) (valid : state.Valid) :
    (read state count).state.Valid := by
  unfold read
  split
  · exact valid
  · split
    · exact valid
    · exact readState_valid state count valid

theorem send_valid (state : State) (count : Nat) (policy : Bool) (valid : state.Valid) :
    (send state count policy).state.Valid := by
  unfold send
  repeat' first
    | (solve | exact valid)
    | (solve | rw [ackBlocked_state]; exact valid)
    | (solve | unfold recoveryBlocked; split <;> exact valid)
    | (solve | apply sendState_valid state count valid; exact Decidable.not_not.mp ‹¬¬SendReady state count›)
    | split

theorem pureAck_valid (state : State) (policy dueOnly : Bool) (valid : state.Valid) :
    (pureAck state policy dueOnly).state.Valid := by
  unfold pureAck
  repeat' first
    | (solve | exact valid)
    | (solve | rw [ackBlocked_state]; exact valid)
    | split

theorem emitAck_valid (state : State) (policy : Bool) (valid : state.Valid) :
    (emitAck state policy).state.Valid := pureAck_valid state policy false valid

theorem dispatchAck_valid (state : State) (policy : Bool) (valid : state.Valid) :
    (dispatchAck state policy).state.Valid := pureAck_valid state policy true valid

theorem recoveryBlocked_state (state : State) (reason : Recovery.Stop) : (recoveryBlocked state reason).state = state := by
  unfold recoveryBlocked
  split <;> rfl

theorem enableRecovery_valid (state : State) (valid : state.Valid) : (enableRecovery state).state.Valid := by
  unfold enableRecovery
  repeat' first
    | (solve | exact valid)
    | (solve | rw [recoveryBlocked_state]; exact valid)
    | (solve | rw [ackBlocked_state]; exact valid)
    | (split)
    | (simp only [State.Valid] at *)

theorem advanceClock_valid (state : State) (millis : Nat) (valid : state.Valid) : (advanceClock state millis).state.Valid := by
  unfold advanceClock
  repeat' first
    | (solve | exact valid)
    | (solve | rw [recoveryBlocked_state]; exact valid)
    | (solve | rw [ackBlocked_state]; exact valid)
    | (split)
    | (simp only [State.Valid] at *)

theorem timeout_valid (state : State) (policy : Bool) (valid : state.Valid) : (timeout state policy).state.Valid := by
  unfold timeout
  repeat' first
    | (solve | exact valid)
    | (solve | rw [recoveryBlocked_state]; exact valid)
    | (solve | rw [ackBlocked_state]; exact valid)
    | (split)
    | (simp only [State.Valid] at *)

theorem withRecovery_valid (state : State) (recovery : Option Recovery.State) (valid : state.Valid) :
    ({ state with recovery } : State).Valid := by
  exact valid

theorem enableAck_valid (state : State) (valid : state.Valid) : (enableAck state).state.Valid := by
  unfold enableAck
  repeat' first
    | (solve | exact valid)
    | (solve | rw [recoveryBlocked_state]; exact valid)
    | (solve | rw [ackBlocked_state]; exact valid)
    | split

theorem withRuntime_valid (state : State) (recovery : Option Recovery.State)
    (reaction : Option AckReaction.State) (valid : state.Valid) :
    ({ state with recovery, ackReaction := reaction } : State).Valid := valid

theorem enableAck_state (state : State)
    (selected : (enableAck state).decision = .accepted .enableAck) :
    (enableAck state).state.ackReaction = some (AckReaction.initial state.core.receiveNext
      state.core.capacity state.localReceiveMSS.limit) ∧
    (enableAck state).state.core = state.core ∧
    (enableAck state).state.recovery = state.recovery := by
  unfold enableAck at selected ⊢
  repeat' first
    | (solve | simp_all [rejected, ackBlocked, recoveryBlocked, AckReaction.Stop.unsupported, Recovery.Stop.unsupported])
    | split


theorem receive_valid (state : State) (value : Input) (valid : state.Valid) :
    (receive state value).state.Valid := by
  simp only [receive, valid, not_true_eq_false, ite_false]
  split
  · rw [recoveryBlocked_state]; exact valid
  · split
    · rw [ackBlocked_state]; exact valid
    · cases selected : (receiveModel state value).decision with
      | blocked reason =>
        cases reason with
        | unsupported reason => exact valid
        | reject reason =>
          cases issued : issueRequest state state.core (receiveModel state value).ack 0 with
          | error reason => rw [ackBlocked_state]; exact valid
          | ok reaction => exact valid
      | accepted count size =>
        cases updated : receiveRecovery state value.packet.segment count with
        | error reason => simpa only [updated, recoveryBlocked_state] using valid
        | ok recovery =>
          cases issued : issueRequest state (receiveModel state value).state (receiveModel state value).ack size with
          | error reason => simpa only [updated, issued, ackBlocked_state] using valid
          | ok reaction =>
            simpa only [updated, issued] using withRuntime_valid
              (receiveState state value (receiveModel state value).state) recovery reaction
              (receiveState_valid state value _ valid (receiveModel_valid state value valid))

theorem windowEligible_forward (state : State) (segment : Segment)
    (eligible : windowEligible state segment = true) :
    Seq.distance state.core.sendUna segment.acknowledgment ≤ state.core.sent.length := by
  have pair : (decide (Seq.distance state.core.sendUna segment.acknowledgment ≤ state.core.sent.length) = true) ∧
      windowFresh state segment = true := by
    simpa only [windowEligible, Bool.and_eq_true] using eligible
  exact of_decide_eq_true pair.1

theorem write_accepted (state : State) (bytes : List UInt8)
    (selected : (write state bytes).decision = .accepted (.write bytes.length)) :
    state.Valid ∧ state.pending.length + bytes.length ≤ state.pendingLimit ∧
      write state bytes = ⟨writeState state bytes, .accepted (.write bytes.length), none, [], none⟩ := by
  by_cases valid : state.Valid
  · by_cases fits : state.pending.length + bytes.length ≤ state.pendingLimit
    · exact ⟨valid, fits, write_of_fits state bytes valid fits⟩
    · simp only [write, valid, not_true_eq_false, ite_false, Nat.lt_of_not_ge fits, ite_true,
        rejected] at selected
      cases selected
  · simp only [write, valid, not_false_eq_true, ite_true, rejected] at selected
    cases selected

theorem read_accepted (state : State) (count : Nat)
    (selected : (read state count).decision = .accepted (.read count)) :
    state.Valid ∧ count ≤ state.core.received.length ∧
      read state count = ⟨readState state count, .accepted (.read count), none, state.core.received.take count, none⟩ := by
  by_cases valid : state.Valid
  · by_cases fits : count ≤ state.core.received.length
    · exact ⟨valid, fits, read_of_fits state count valid fits⟩
    · simp only [read, valid, not_true_eq_false, ite_false, Nat.lt_of_not_ge fits, ite_true,
        rejected] at selected
      cases selected
  · simp only [read, valid, not_false_eq_true, ite_true, rejected] at selected
    cases selected

theorem send_accepted (state : State) (count : Nat) (policy : Bool)
    (selected : (send state count policy).decision = .accepted (.send count)) :
    state.Valid ∧ policy = true ∧ SendReady state count ∧
      ∃ output, emit state (state.pending.take count) = .ok output ∧
        send state count policy = ⟨sendState state count, .accepted (.send count), some output, [], none⟩ := by
  by_cases valid : state.Valid
  · cases policy with
    | false => simp [send, valid, rejected] at selected
    | true =>
      by_cases ready : SendReady state count
      · cases prepared : ackReady state with
        | error reason =>
          simp only [send, valid, not_true_eq_false, ite_false, Bool.not_true, Bool.false_eq_true,
            ready, prepared, ackBlocked] at selected
          split at selected <;> cases selected
        | ok answer =>
          cases answer
          cases encoded : emit state (state.pending.take count) with
          | error reason =>
            simp [send, valid, ready, prepared, encoded, rejected] at selected
          | ok output => exact ⟨valid, rfl, ready, output, rfl, send_of_ready state count valid ready prepared output encoded⟩
      · simp only [send, valid, not_true_eq_false, ite_false, Bool.not_true, Bool.false_eq_true,
          ready, not_false_eq_true, ite_true] at selected
        split at selected
        · simp [recoveryBlocked, Recovery.Stop.unsupported] at selected
        · cases selected
  · simp only [send, valid, not_false_eq_true, ite_true, rejected] at selected
    cases selected

theorem receive_accepted (state : State) (value : Input) (count size : Nat)
    (selected : (receive state value).decision = .accepted (.receive count size)) :
    state.Valid ∧ (receiveModel state value).decision = .accepted count size ∧
      ∃ recovery ackReaction,
        receiveRecovery state value.packet.segment count = .ok recovery ∧
        issueRequest state (receiveModel state value).state (receiveModel state value).ack size = .ok ackReaction ∧
        receive state value =
          ⟨{ receiveState state value (receiveModel state value).state with recovery, ackReaction },
            .accepted (.receive count size), none, [], (receiveModel state value).ack⟩ := by
  unfold receive at selected
  dsimp only at selected
  split at selected
  · cases selected
  · rename_i valid
    split at selected
    · simp [recoveryBlocked, rejected, Recovery.Stop.unsupported] at selected
    · rename_i coherent
      split at selected
      · simp [ackBlocked, rejected, AckReaction.Stop.unsupported] at selected
      · rename_i ackCoherent
        cases chosen : (receiveModel state value).decision with
        | blocked reason =>
          cases reason
          · simp only [chosen] at selected
            split at selected
            · unfold ackBlocked at selected
              split at selected <;> cases selected
            · cases selected
          · simp only [chosen] at selected
            cases selected
        | accepted amount length =>
          simp only [chosen] at selected
          cases updated : receiveRecovery state value.packet.segment amount with
          | error reason =>
            simp only [updated, recoveryBlocked] at selected
            split at selected <;> cases selected
          | ok recovery =>
            simp only [updated] at selected
            cases issued : issueRequest state (receiveModel state value).state (receiveModel state value).ack length with
            | error reason =>
              simp only [issued, ackBlocked] at selected
              split at selected <;> cases selected
            | ok ackReaction =>
              simp only [issued, Decision.accepted.injEq, Accepted.receive.injEq] at selected
              obtain ⟨rfl, rfl⟩ := selected
              exact ⟨Decidable.not_not.mp valid, rfl, recovery, ackReaction, updated, issued,
                by simp only [receive, valid, coherent, ackCoherent, ite_false, chosen, updated, issued]⟩

theorem receive_in_order (state : State) (value : Input) (count size : Nat)
    (selected : (receive state value).decision = .accepted (.receive count size))
    (nonempty : value.packet.segment.payload ≠ []) :
    value.packet.segment.sequence = state.core.receiveNext := by
  have coreSelected := (receive_accepted state value count size selected).2.1
  cases chosen : state.ackReaction with
  | none =>
    simp only [receiveModel, chosen] at coreSelected
    by_cases order : value.packet.segment.sequence = state.core.receiveNext
    · exact order
    · unfold EstablishedReceive.receive EstablishedReceive.evaluate at coreSelected
      cases gate : EstablishedReceive.gate state.core value.packet.header value.packet.segment with
      | blocked reason kind => simp only [gate, EstablishedReceive.blocked] at coreSelected; cases coreSelected
      | next amount =>
        simp only [gate, EstablishedReceive.finish, nonempty, order, ne_eq, not_false_eq_true,
          and_self, ite_true, EstablishedReceive.blocked] at coreSelected
        cases coreSelected
  | some reaction =>
    exact EstablishedReceive.receiveWithWindow_in_order state.core value reaction.window count size
      (by simpa only [receiveModel, chosen] using coreSelected) nonempty

theorem send_output (state : State) (count : Nat) (policy : Bool)
    (selected : (send state count policy).decision = .accepted (.send count)) :
    ∃ output, (send state count policy).output = some output ∧
      emit state (state.pending.take count) = .ok output ∧
      output.packet.segment.payload = state.pending.take count ∧
      output.packet.segment.sequence = state.core.sendNext ∧
      output.packet.segment.acknowledgment = state.core.receiveNext := by
  obtain ⟨_, _, _, output, encoded, result⟩ := send_accepted state count policy selected
  refine ⟨output, ?_, encoded, emit_payload _ _ _ encoded, ?_, ?_⟩
  · rw [result]
  · exact (emit_transport _ _ _ encoded).2.1
  · exact (emit_transport _ _ _ encoded).2.2.1

theorem pureAck_output (state : State) (policy dueOnly : Bool) (action : Accepted)
    (selected : (pureAck state policy dueOnly).decision = .accepted action) :
    ∃ output, (pureAck state policy dueOnly).output = some output ∧ emit state [] = .ok output := by
  by_cases valid : state.Valid
  · cases policy with
    | false => simp [pureAck, valid, rejected] at selected
    | true =>
      cases response : responseReady state dueOnly with
      | error reason =>
        simp only [pureAck, valid, not_true_eq_false, ite_false, Bool.not_true, Bool.false_eq_true, response,
          ackBlocked] at selected
        split at selected <;> cases selected
      | ok answer =>
        cases answer
        cases prepared : ackReady state with
        | error reason =>
          simp only [pureAck, valid, not_true_eq_false, ite_false, Bool.not_true, Bool.false_eq_true, response,
            prepared, ackBlocked] at selected
          split at selected <;> cases selected
        | ok answer =>
          cases answer
          cases encoded : emit state [] with
          | error reason => simp [pureAck, valid, response, prepared, encoded, rejected] at selected
          | ok output =>
            exact ⟨output, by simp only [pureAck, valid, not_true_eq_false, ite_false, Bool.not_true,
              Bool.false_eq_true, response, prepared, encoded], rfl⟩
  · simp [pureAck, valid, rejected] at selected

theorem send_ackReady (state : State) (count : Nat) (policy : Bool)
    (selected : (send state count policy).decision = .accepted (.send count)) : ackReady state = .ok () := by
  unfold send at selected
  repeat' first
    | (solve | assumption)
    | (solve | cases selected)
    | (solve | unfold ackBlocked at selected; split at selected <;> cases selected)
    | (solve | unfold recoveryBlocked at selected; split at selected <;> cases selected)
    | split at selected

theorem timeout_ackReady (state : State) (policy : Bool) (count : Nat)
    (selected : (timeout state policy).decision = .accepted (.retry count)) : ackReady state = .ok () := by
  unfold timeout at selected
  repeat' first
    | (solve | assumption)
    | (solve | cases selected)
    | (solve | unfold ackBlocked at selected; split at selected <;> cases selected)
    | (solve | unfold recoveryBlocked at selected; split at selected <;> cases selected)
    | split at selected

theorem pureAck_ackReady (state : State) (policy dueOnly : Bool) (action : Accepted)
    (selected : (pureAck state policy dueOnly).decision = .accepted action) : ackReady state = .ok () := by
  unfold pureAck at selected
  repeat' first
    | (solve | assumption)
    | (solve | cases selected)
    | (solve | unfold ackBlocked at selected; split at selected <;> cases selected)
    | (solve | unfold recoveryBlocked at selected; split at selected <;> cases selected)
    | split at selected

theorem pureAck_state (state : State) (policy dueOnly : Bool) (action : Accepted)
    (selected : (pureAck state policy dueOnly).decision = .accepted action) :
    (pureAck state policy dueOnly).state = outputState state := by
  by_cases valid : state.Valid
  · cases policy with
    | false => simp [pureAck, valid, rejected] at selected
    | true =>
      cases response : responseReady state dueOnly with
      | error reason =>
        simp only [pureAck, valid, not_true_eq_false, ite_false, Bool.not_true, Bool.false_eq_true, response,
          ackBlocked] at selected
        split at selected <;> cases selected
      | ok answer =>
        cases answer
        cases prepared : ackReady state with
        | error reason =>
          simp only [pureAck, valid, not_true_eq_false, ite_false, Bool.not_true, Bool.false_eq_true, response,
            prepared, ackBlocked] at selected
          split at selected <;> cases selected
        | ok answer =>
          cases answer
          cases encoded : emit state [] with
          | error reason => simp [pureAck, valid, response, prepared, encoded, rejected] at selected
          | ok output =>
            simp only [pureAck, valid, not_true_eq_false, ite_false, Bool.not_true,
              Bool.false_eq_true, response, prepared, encoded]
  · simp [pureAck, valid, rejected] at selected


theorem emitAck_output (state : State) (policy : Bool)
    (selected : (emitAck state policy).decision = .accepted .emitAck) :
    ∃ output, (emitAck state policy).output = some output ∧ emit state [] = .ok output :=
  pureAck_output state policy false .emitAck selected

theorem dispatchAck_output (state : State) (policy : Bool)
    (selected : (dispatchAck state policy).decision = .accepted .dispatchAck) :
    ∃ output, (dispatchAck state policy).output = some output ∧ emit state [] = .ok output :=
  pureAck_output state policy true .dispatchAck selected



theorem windowEligible_old_ack (state : State) (segment : Segment)
    (short : state.core.ShortArc)
    (different : segment.acknowledgment ≠ state.core.sendUna)
    (old : Seq.distance segment.acknowledgment state.core.sendUna ≤ EstablishedReceive.maxSendWindow) :
    windowEligible state segment = false := by
  have total := Seq.distance_reverse state.core.sendUna segment.acknowledgment (Ne.symm different)
  have outside : ¬Seq.distance state.core.sendUna segment.acknowledgment ≤ state.core.sent.length := by
    unfold EstablishedReceive.State.ShortArc EstablishedReceive.maxSendWindow Seq.halfSpace at short
    unfold EstablishedReceive.maxSendWindow at old
    unfold Seq.modulus at total
    omega
  simp only [windowEligible, outside, decide_false, Bool.false_and]

theorem windowEligible_duplicate (state : State) (segment : Segment)
    (same : segment.acknowledgment = state.core.sendUna) :
    windowEligible state segment = windowFresh state segment := by
  simp only [windowEligible, same, Seq.distance_self, Nat.zero_le, decide_true, Bool.true_and]

theorem windowState_unchanged (before after : State) (segment : Segment)
    (stale : windowEligible before segment = false) : windowState before after segment = after := by
  simp only [windowState, stale, Bool.false_eq_true, ite_false]

theorem windowState_updated (before after : State) (segment : Segment)
    (fresh : windowEligible before segment = true) :
    windowState before after segment =
      { after with sendWindow := segment.window.val, sendWL1 := segment.sequence, sendWL2 := segment.acknowledgment } := by
  simp only [windowState, fresh, ite_true]

theorem windowFresh_older_sequence (state : State) (segment : Segment)
    (older : Seq.Before segment.sequence state.sendWL1) : windowFresh state segment = false := by
  have notForward := Seq.before_asymm segment.sequence state.sendWL1 older
  have unequal : state.sendWL1 ≠ segment.sequence := by
    intro same
    rw [same] at older
    exact Seq.before_irrefl _ older
  have forward : Seq.before state.sendWL1 segment.sequence = false := by
    simp only [Seq.before, notForward, decide_false]
  simp only [windowFresh, forward, unequal, decide_false, Bool.false_and, Bool.false_or]

theorem windowFresh_older_ack (state : State) (segment : Segment)
    (same : segment.sequence = state.sendWL1)
    (older : Seq.Before segment.acknowledgment state.sendWL2) : windowFresh state segment = false := by
  have notForward := Seq.before_asymm segment.acknowledgment state.sendWL2 older
  have unequal : state.sendWL2 ≠ segment.acknowledgment := by
    intro same
    rw [same] at older
    exact Seq.before_irrefl _ older
  have forward : Seq.before state.sendWL2 segment.acknowledgment = false := by
    simp only [Seq.before, notForward, decide_false]
  have reflexive : Seq.before state.sendWL1 state.sendWL1 = false := by
    simp only [Seq.before, Seq.before_irrefl, decide_false]
  simp only [windowFresh, same, reflexive, decide_true, Bool.true_and, forward,
    unequal, decide_false, Bool.false_or]

theorem windowFresh_coordinates (state : State) (segment : Segment)
    (sequenceOrigin ackOrigin : Seq) (sequenceLength ackLength : Nat)
    (sequenceShort : sequenceLength < Seq.halfSpace) (ackShort : ackLength < Seq.halfSpace)
    (oldSequence : Seq.InInterval sequenceOrigin sequenceLength state.sendWL1)
    (newSequence : Seq.InInterval sequenceOrigin sequenceLength segment.sequence)
    (oldAck : Seq.InInterval ackOrigin ackLength state.sendWL2)
    (newAck : Seq.InInterval ackOrigin ackLength segment.acknowledgment) :
    windowFresh state segment = true ↔
      Seq.distance sequenceOrigin state.sendWL1 < Seq.distance sequenceOrigin segment.sequence ∨
        (state.sendWL1 = segment.sequence ∧
          Seq.distance ackOrigin state.sendWL2 ≤ Seq.distance ackOrigin segment.acknowledgment) := by
  have sequenceOrder := Seq.common_arc_before sequenceOrigin state.sendWL1 segment.sequence sequenceLength
    sequenceShort oldSequence newSequence
  have ackOrder := Seq.common_arc_before ackOrigin state.sendWL2 segment.acknowledgment ackLength
    ackShort oldAck newAck
  have ackEqual : state.sendWL2 = segment.acknowledgment ↔
      Seq.distance ackOrigin state.sendWL2 = Seq.distance ackOrigin segment.acknowledgment := by
    constructor
    · intro same
      rw [same]
    · intro same
      calc
        state.sendWL2 = ackOrigin.add (Seq.distance ackOrigin state.sendWL2) := (Seq.add_distance _ _).symm
        _ = ackOrigin.add (Seq.distance ackOrigin segment.acknowledgment) := congrArg (Seq.add ackOrigin) same
        _ = segment.acknowledgment := Seq.add_distance _ _
  simp only [windowFresh, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Seq.before_correct]
  rw [sequenceOrder, ackOrder, ackEqual]
  have arithmetic (a b : Nat) : a = b ∨ a < b ↔ a ≤ b := by omega
  rw [arithmetic]

def State.rebind (state : State) (header : Packet.Header) : State :=
  { state with core := state.core.rebind header }

def Result.rebind (result : Result) (header : Packet.Header) : Result :=
  { result with state := result.state.rebind header }

theorem State.rebind_valid (state : State) (header : Packet.Header) (valid : state.Valid)
    (transport : header.protocol = Packet.Protocol.tcp) : (state.rebind header).Valid :=
  ⟨state.core.rebind_valid header valid.1 transport, valid.2⟩

theorem windowEligible_rewrite (state : State) (header : Packet.Header) (value : DecodedIPv4)
    (target : Packet.Header) :
    windowEligible (state.rebind header) (TCPRewrite.segment value target) = windowEligible state value.segment := rfl

theorem receiveState_rewrite (state : State) (value : Input) (after : ERState)
    (target : Packet.Header) (ttl : UInt8) (transport : target.protocol = Packet.Protocol.tcp) :
    receiveState (state.rebind target) (value.rewrite target ttl transport) (after.rebind target) =
      (receiveState state value after).rebind target := by
  have eligible : windowEligible (state.rebind target)
      (value.rewrite target ttl transport).packet.segment = windowEligible state value.packet.segment := rfl
  simp only [receiveState, windowState, eligible]
  split <;> rfl

theorem recoveryCoherent_rebind (state : State) (header : Packet.Header) :
    RecoveryCoherent (state.rebind header) = RecoveryCoherent state := rfl

theorem receiveRecovery_rewrite (state : State) (header : Packet.Header) (value : DecodedIPv4)
    (target : Packet.Header) (count : Nat) :
    receiveRecovery (state.rebind header) (TCPRewrite.segment value target) count = receiveRecovery state value.segment count := rfl

theorem receiveRecovery_input_rewrite (state : State) (value : Input) (target : Packet.Header) (ttl : UInt8)
    (transport : target.protocol = Packet.Protocol.tcp) (count : Nat) :
    receiveRecovery (state.rebind target) (value.rewrite target ttl transport).packet.segment count =
      receiveRecovery state value.packet.segment count := rfl


theorem timeout_accepted (state : State) (policy : Bool) (count : Nat)
    (selected : (timeout state policy).decision = .accepted (.retry count)) :
    state.Valid ∧ policy = true ∧
      ∃ recovery after output, state.recovery = some recovery ∧ Recovery.timeout recovery = .ok (count, after) ∧
        0 < count ∧ count ≤ state.core.sent.length ∧ count ≤ state.effectiveMSS ∧
        40 + count ≤ state.ipSendLimit ∧ count ≤ state.sendWindow ∧
        emitAt state state.core.sendUna (state.core.sent.take count) = .ok output ∧
        timeout state policy = ⟨{ outputState state with recovery := some after }, .accepted (.retry count), some output, [], none⟩ := by
  by_cases valid : state.Valid
  · by_cases coherent : RecoveryCoherent state
    · cases stored : state.recovery with
      | none => simp [timeout, valid, coherent, stored, recoveryBlocked, Recovery.Stop.unsupported, rejected] at selected
      | some recovery =>
        cases timed : Recovery.timeout recovery with
        | error reason =>
          simp only [timeout, valid, not_true_eq_false, ite_false, coherent, stored, timed, recoveryBlocked] at selected
          split at selected <;> cases selected
        | ok pair =>
          obtain ⟨amount, after⟩ := pair
          cases policy with
          | false => simp [timeout, valid, coherent, stored, timed, rejected] at selected
          | true =>
            by_cases window : amount ≤ state.sendWindow
            · by_cases bounded : amount ≤ state.core.sent.length ∧ amount ≤ state.effectiveMSS ∧ 40 + amount ≤ state.ipSendLimit
              · have noBounds : ¬(amount > state.core.sent.length ∨ amount > state.effectiveMSS ∨ 40 + amount > state.ipSendLimit) := by omega
                cases prepared : ackReady state with
                | error reason =>
                  simp only [timeout, valid, not_true_eq_false, ite_false, coherent, stored, timed,
                    Bool.not_true, Bool.false_eq_true, Nat.not_lt.mpr window, noBounds, prepared, ackBlocked] at selected
                  split at selected <;> cases selected
                | ok answer =>
                  cases answer
                  cases encoded : emitAt state state.core.sendUna (state.core.sent.take amount) with
                  | error reason =>
                    simp [timeout, valid, coherent, stored, timed, Nat.not_lt.mpr window, noBounds, prepared, encoded, rejected] at selected
                  | ok output =>
                    simp only [timeout, valid, not_true_eq_false, ite_false, coherent, stored, timed,
                      Bool.not_true, Bool.false_eq_true, Nat.not_lt.mpr window, noBounds, prepared, encoded,
                      Decision.accepted.injEq, Accepted.retry.injEq] at selected
                    subst amount
                    exact ⟨valid, rfl, recovery, after, output, rfl, timed,
                      (Recovery.timeout_bounds recovery count after timed).1, bounded.1, bounded.2.1, bounded.2.2, window,
                      encoded, by simp only [timeout, valid, not_true_eq_false, ite_false, coherent, stored, timed,
                        Bool.not_true, Bool.false_eq_true, Nat.not_lt.mpr window, noBounds, prepared, encoded]⟩
              · have outside : amount > state.core.sent.length ∨ amount > state.effectiveMSS ∨ 40 + amount > state.ipSendLimit := by omega
                simp [timeout, valid, coherent, stored, timed, Nat.not_lt.mpr window, outside, recoveryBlocked, Recovery.Stop.unsupported, rejected] at selected
            · have outside : amount > state.sendWindow := by omega
              simp [timeout, valid, coherent, stored, timed, outside, recoveryBlocked, Recovery.Stop.unsupported] at selected
    · simp [timeout, valid, coherent, recoveryBlocked, Recovery.Stop.unsupported, rejected] at selected
  · simp [timeout, valid, rejected] at selected

theorem timeout_output (state : State) (policy : Bool) (count : Nat)
    (selected : (timeout state policy).decision = .accepted (.retry count)) :
    ∃ recovery after output, state.recovery = some recovery ∧ Recovery.timeout recovery = .ok (count, after) ∧
      (timeout state policy).state = { outputState state with recovery := some after } ∧
      (timeout state policy).output = some output ∧
      emitAt state state.core.sendUna (state.core.sent.take count) = .ok output ∧
      output.packet.segment.payload = state.core.sent.take count ∧
      output.packet.segment.sequence = state.core.sendUna ∧ count ≤ state.core.sent.length := by
  obtain ⟨_, _, recovery, after, output, stored, timed, _, bound, _, _, _, encoded, actual⟩ :=
    timeout_accepted state policy count selected
  exact ⟨recovery, after, output, stored, timed, by rw [actual], by rw [actual], encoded,
    emitAt_payload _ _ _ _ encoded, (emitAt_transport _ _ _ _ encoded).2.1, bound⟩

theorem ackCoherent_rebind (state : State) (header : Packet.Header) :
    AckCoherent (state.rebind header) = AckCoherent state := rfl

theorem issueRequest_rebind (state : State) (after : ERState) (request : Option EstablishedReceive.AckRequest)
    (size : Nat) (header : Packet.Header) :
    issueRequest (state.rebind header) (after.rebind header) request size = issueRequest state after request size := rfl

theorem issueRequest_rebind_self (state : State) (request : Option EstablishedReceive.AckRequest)
    (size : Nat) (header : Packet.Header) :
    issueRequest (state.rebind header) (state.rebind header).core request size =
      issueRequest state state.core request size := rfl

theorem ackBlocked_rebind (state : State) (reason : AckReaction.Stop) (header : Packet.Header) :
    ackBlocked (state.rebind header) reason = (ackBlocked state reason).rebind header := by
  unfold ackBlocked
  split <;> rfl

theorem recoveryBlocked_rebind (state : State) (reason : Recovery.Stop) (header : Packet.Header) :
    recoveryBlocked (state.rebind header) reason = (recoveryBlocked state reason).rebind header := by
  unfold recoveryBlocked
  split <;> rfl

theorem receiveModel_rewrite (state : State) (value : Input) (target : Packet.Header) (ttl : UInt8)
    (valid : state.Valid) (tuple : value.packet.header = state.core.inbound)
    (transport : target.protocol = Packet.Protocol.tcp) :
    receiveModel (state.rebind target) (value.rewrite target ttl transport) =
      (receiveModel state value).rebind target := by
  cases selected : state.ackReaction with
  | none =>
    simpa only [receiveModel, State.rebind, selected] using
      EstablishedReceive.receive_rewrite state.core value target ttl valid.1 tuple transport
  | some reaction =>
    simpa only [receiveModel, State.rebind, selected] using
      EstablishedReceive.receiveWithWindow_rewrite state.core value reaction.window target ttl valid.1 tuple transport

theorem receive_rewrite (state : State) (value : Input) (target : Packet.Header) (ttl : UInt8)
    (valid : state.Valid) (tuple : value.packet.header = state.core.inbound)
    (transport : target.protocol = Packet.Protocol.tcp) :
    receive (state.rebind target) (value.rewrite target ttl transport) = (receive state value).rebind target := by
  have rebound := state.rebind_valid target valid transport
  have core := receiveModel_rewrite state value target ttl valid tuple transport
  by_cases coherent : RecoveryCoherent state
  · have reboundCoherent : RecoveryCoherent (state.rebind target) := coherent
    by_cases ackCoherent : AckCoherent state
    · have reboundAck : AckCoherent (state.rebind target) := ackCoherent
      cases original : receiveModel state value with
      | mk after decision ack =>
        have reboundCore : receiveModel (state.rebind target) (value.rewrite target ttl transport) =
            (⟨after, decision, ack⟩ : EstablishedReceive.Result).rebind target := by rw [core, original]
        cases decision with
        | blocked reason =>
          cases reason with
          | unsupported reason =>
            simp only [receive, rebound, valid, not_true_eq_false, ite_false, reboundCoherent, coherent,
              reboundAck, ackCoherent, reboundCore, original, EstablishedReceive.Result.rebind]
            rfl
          | reject reason =>
            simp only [receive, rebound, valid, not_true_eq_false, ite_false, reboundCoherent, coherent,
              reboundAck, ackCoherent, reboundCore, original, EstablishedReceive.Result.rebind]
            rw [issueRequest_rebind_self]
            cases issued : issueRequest state state.core ack 0 with
            | error reason => simpa only using ackBlocked_rebind state reason target
            | ok reaction => rfl
        | accepted count size =>
          simp only [receive, rebound, valid, not_true_eq_false, ite_false, reboundCoherent, coherent,
            reboundAck, ackCoherent, reboundCore, original, EstablishedReceive.Result.rebind]
          rw [receiveRecovery_input_rewrite]
          cases updated : receiveRecovery state value.packet.segment count with
          | error reason => simpa only using recoveryBlocked_rebind state reason target
          | ok recovery =>
            simp only []
            rw [issueRequest_rebind]
            cases issued : issueRequest state after ack size with
            | error reason => simpa only using ackBlocked_rebind state reason target
            | ok reaction =>
              have eligible : windowEligible (state.rebind target)
                  (value.rewrite target ttl transport).packet.segment = windowEligible state value.packet.segment := rfl
              simp only [receiveState, windowState, eligible]
              split <;> rfl
    · have reboundAck : ¬AckCoherent (state.rebind target) := ackCoherent
      simp only [receive, rebound, valid, not_true_eq_false, ite_false, reboundCoherent, coherent,
        reboundAck, ackCoherent, not_false_eq_true, ite_true]
      rfl
  · have reboundCoherent : ¬RecoveryCoherent (state.rebind target) := coherent
    simp only [receive, rebound, valid, not_true_eq_false, ite_false, reboundCoherent, coherent,
      not_false_eq_true, ite_true]
    rfl

end Netlib.Protocol.TCP.Endpoint
