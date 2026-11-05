import Netlib.Protocol.TCP.Output

/-!
# Bounded application operations for a TCP endpoint

The initial state assumes an established connection and peer-window history.
The effective MSS and IP size limit are explicit configuration inputs.
The policy input permits one selected output. It does not prove congestion control.
Serial window comparisons need a separate bound on the age of window history.
The state validity predicate does not supply that bound.
This profile has no retransmission, window probe, timer, or connection-control operation.
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
  deriving Repr, BEq, DecidableEq

def State.Valid (state : State) : Prop :=
  state.core.Valid ∧ state.pending.length ≤ state.pendingLimit ∧ state.pendingLimit ≤ 65535 ∧
    state.sendWindow ≤ 65535 ∧ 0 < state.effectiveMSS ∧
    40 + state.effectiveMSS ≤ state.ipSendLimit ∧ state.ipSendLimit ≤ 65535

instance (state : State) : Decidable state.Valid := by
  unfold State.Valid
  infer_instance

inductive Accepted where
  | write (count : Nat)
  | send (count : Nat)
  | read (count : Nat)
  | emitAck
  | receive (acknowledged received : Nat)
  deriving Repr, BEq, DecidableEq

inductive Reject where
  | invalidSeed | pendingCapacity | readBounds | sendBounds | policy | encoding
  | input (reason : EstablishedReceive.Reject)
  deriving Repr, BEq, DecidableEq

inductive Decision where
  | accepted (action : Accepted)
  | reject (reason : Reject)
  | unsupported (reason : EstablishedReceive.Unsupported)
  deriving Repr, BEq, DecidableEq

structure Result where
  state : State
  decision : Decision
  output : Option Input := none
  read : List UInt8 := []
  ack : Option EstablishedReceive.AckRequest := none

def rejected (state : State) (reason : Reject) : Result := ⟨state, .reject reason, none, [], none⟩

def writeState (state : State) (bytes : List UInt8) : State :=
  { state with pending := state.pending ++ bytes }

def readState (state : State) (count : Nat) : State :=
  { state with core := { state.core with received := state.core.received.drop count } }

def sendState (state : State) (count : Nat) : State :=
  { state with
    pending := state.pending.drop count
    core := { state.core with
      sent := state.core.sent ++ state.pending.take count
      sendNext := state.core.sendNext.add count } }

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
    count ≤ state.effectiveMSS ∧ 40 + count ≤ state.ipSendLimit

instance (state : State) (count : Nat) : Decidable (SendReady state count) := by
  unfold SendReady
  infer_instance

def send (state : State) (count : Nat) (policyPermitted : Bool) : Result :=
  if ¬state.Valid then rejected state .invalidSeed
  else if !policyPermitted then rejected state .policy
  else if ¬SendReady state count then rejected state .sendBounds
  else match Output.emit state.core (state.pending.take count) with
    | .error _ => rejected state .encoding
    | .ok output => ⟨sendState state count, .accepted (.send count), some output, [], none⟩

def emitAck (state : State) (policyPermitted : Bool) : Result :=
  if ¬state.Valid then rejected state .invalidSeed
  else if !policyPermitted then rejected state .policy
  else match Output.emit state.core [] with
    | .error _ => rejected state .encoding
    | .ok output => ⟨state, .accepted .emitAck, some output, [], none⟩

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
  windowState state { state with core := after } value.packet.segment

def receive (state : State) (value : Input) : Result :=
  if ¬state.Valid then rejected state .invalidSeed
  else
    let result := EstablishedReceive.receive state.core value
    match result.decision with
    | .blocked (.reject reason) => ⟨state, .reject (.input reason), none, [], result.ack⟩
    | .blocked (.unsupported reason) => ⟨state, .unsupported reason, none, [], result.ack⟩
    | .accepted count size =>
      ⟨receiveState state value result.state, .accepted (.receive count size), none, [], result.ack⟩

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

theorem send_of_ready (state : State) (count : Nat) (valid : state.Valid)
    (ready : SendReady state count) (output : Input)
    (encoded : Output.emit state.core (state.pending.take count) = .ok output) :
    send state count true = ⟨sendState state count, .accepted (.send count), some output, [], none⟩ := by
  simp only [send, valid, not_true_eq_false, ite_false, Bool.not_true, Bool.false_eq_true, ready, encoded]

theorem send_success (state : State) (count : Nat) (valid : state.Valid)
    (ready : SendReady state count) :
    ∃ output, send state count true =
      ⟨sendState state count, .accepted (.send count), some output, [], none⟩ := by
  have length : (state.pending.take count).length = count := by
    simp only [List.length_take, Nat.min_eq_left ready.2.1]
  have bounded : 40 + (state.pending.take count).length ≤ 65535 := by
    rw [length]
    have packetBound := ready.2.2.2.2.2
    have ipBound := valid.2.2.2.2.2.2
    omega
  obtain ⟨output, encoded⟩ := Output.emit_exists state.core (state.pending.take count) valid.1 bounded
  exact ⟨output, send_of_ready state count valid ready output encoded⟩

theorem emitAck_success (state : State) (valid : state.Valid) :
    ∃ output, emitAck state true = ⟨state, .accepted .emitAck, some output, [], none⟩ := by
  obtain ⟨output, encoded⟩ := Output.emit_exists state.core [] valid.1 (by decide)
  refine ⟨output, ?_⟩
  simp only [emitAck, valid, not_true_eq_false, ite_false, Bool.not_true, Bool.false_eq_true, encoded]

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
  split
  · exact valid
  · split
    · exact valid
    · split
      · exact valid
      · rename_i ready
        cases Output.emit state.core (state.pending.take count) with
        | error reason => exact valid
        | ok output => exact sendState_valid state count valid (Decidable.of_not_not ready)

theorem emitAck_valid (state : State) (policy : Bool) (valid : state.Valid) :
    (emitAck state policy).state.Valid := by
  unfold emitAck
  split
  · exact valid
  · split
    · exact valid
    · cases Output.emit state.core [] <;> exact valid

theorem receive_valid (state : State) (value : Input) (valid : state.Valid) :
    (receive state value).state.Valid := by
  simp only [receive, valid, not_true_eq_false, ite_false]
  cases selected : (EstablishedReceive.receive state.core value).decision with
  | blocked reason => cases reason <;> exact valid
  | accepted count size =>
    exact receiveState_valid state value _ valid (EstablishedReceive.receive_valid state.core value valid.1)

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
      ∃ output, Output.emit state.core (state.pending.take count) = .ok output ∧
        send state count policy = ⟨sendState state count, .accepted (.send count), some output, [], none⟩ := by
  by_cases valid : state.Valid
  · cases policy with
    | false =>
      simp only [send, valid, not_true_eq_false, ite_false, Bool.not_false, ite_true, rejected] at selected
      cases selected
    | true =>
      by_cases ready : SendReady state count
      · cases encoded : Output.emit state.core (state.pending.take count) with
        | error reason =>
          simp only [send, valid, not_true_eq_false, ite_false, Bool.not_true, Bool.false_eq_true,
            ready, encoded, rejected] at selected
          cases selected
        | ok output => exact ⟨valid, rfl, ready, output, rfl, send_of_ready state count valid ready output encoded⟩
      · simp only [send, valid, not_true_eq_false, ite_false, Bool.not_true, Bool.false_eq_true,
          ready, not_false_eq_true, ite_true, rejected] at selected
        cases selected
  · simp only [send, valid, not_false_eq_true, ite_true, rejected] at selected
    cases selected

theorem receive_accepted (state : State) (value : Input) (count size : Nat)
    (selected : (receive state value).decision = .accepted (.receive count size)) :
    state.Valid ∧ (EstablishedReceive.receive state.core value).decision = .accepted count size ∧
      receive state value =
        ⟨receiveState state value (EstablishedReceive.receive state.core value).state,
          .accepted (.receive count size), none, [], (EstablishedReceive.receive state.core value).ack⟩ := by
  by_cases valid : state.Valid
  · simp only [receive, valid, not_true_eq_false, ite_false] at selected
    cases chosen : (EstablishedReceive.receive state.core value).decision with
    | blocked reason =>
      cases reason <;> simp only [chosen] at selected <;> cases selected
    | accepted amount length =>
      simp only [chosen, Decision.accepted.injEq, Accepted.receive.injEq] at selected
      obtain ⟨rfl, rfl⟩ := selected
      exact ⟨valid, rfl, by simp only [receive, valid, not_true_eq_false, ite_false, chosen]⟩
  · simp only [receive, valid, not_false_eq_true, ite_true, rejected] at selected
    cases selected

theorem receive_in_order (state : State) (value : Input) (count size : Nat)
    (selected : (receive state value).decision = .accepted (.receive count size))
    (nonempty : value.packet.segment.payload ≠ []) :
    value.packet.segment.sequence = state.core.receiveNext := by
  have coreSelected := (receive_accepted state value count size selected).2.1
  by_cases order : value.packet.segment.sequence = state.core.receiveNext
  · exact order
  · unfold EstablishedReceive.receive EstablishedReceive.evaluate at coreSelected
    cases gate : EstablishedReceive.gate state.core value.packet.header value.packet.segment with
    | blocked reason kind => simp only [gate, EstablishedReceive.blocked] at coreSelected; cases coreSelected
    | next amount =>
      simp only [gate, EstablishedReceive.finish, nonempty, order, ne_eq, not_false_eq_true,
        and_self, ite_true, EstablishedReceive.blocked] at coreSelected
      cases coreSelected

theorem send_output (state : State) (count : Nat) (policy : Bool)
    (selected : (send state count policy).decision = .accepted (.send count)) :
    ∃ output, (send state count policy).output = some output ∧
      Output.emit state.core (state.pending.take count) = .ok output ∧
      output.packet.segment.payload = state.pending.take count ∧
      output.packet.segment.sequence = state.core.sendNext ∧
      output.packet.segment.acknowledgment = state.core.receiveNext := by
  obtain ⟨_, _, _, output, encoded, result⟩ := send_accepted state count policy selected
  refine ⟨output, ?_, encoded, Output.emit_payload _ _ _ encoded, ?_, ?_⟩
  · rw [result]
  · exact (Output.emit_transport _ _ _ encoded).2.1
  · exact (Output.emit_transport _ _ _ encoded).2.2.1

theorem emitAck_output (state : State) (policy : Bool)
    (selected : (emitAck state policy).decision = .accepted .emitAck) :
    ∃ output, (emitAck state policy).output = some output ∧ Output.emit state.core [] = .ok output := by
  by_cases valid : state.Valid
  · cases policy with
    | false =>
      simp only [emitAck, valid, not_true_eq_false, ite_false, Bool.not_false, ite_true, rejected] at selected
      cases selected
    | true =>
      cases encoded : Output.emit state.core [] with
      | error reason =>
        simp only [emitAck, valid, not_true_eq_false, ite_false, Bool.not_true, Bool.false_eq_true,
          encoded, rejected] at selected
        cases selected
      | ok output =>
        refine ⟨output, ?_, rfl⟩
        simp only [emitAck, valid, not_true_eq_false, ite_false, Bool.not_true, Bool.false_eq_true, encoded]
  · simp only [emitAck, valid, not_false_eq_true, ite_true, rejected] at selected
    cases selected

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
  change windowState (state.rebind target) { state.rebind target with core := after.rebind target }
      (TCPRewrite.segment value.packet target) = _
  unfold receiveState windowState
  rw [windowEligible_rewrite]
  split <;> rfl

theorem receive_rewrite (state : State) (value : Input) (target : Packet.Header) (ttl : UInt8)
    (valid : state.Valid) (tuple : value.packet.header = state.core.inbound)
    (transport : target.protocol = Packet.Protocol.tcp) :
    receive (state.rebind target) (value.rewrite target ttl transport) = (receive state value).rebind target := by
  have rebound := state.rebind_valid target valid transport
  have core : EstablishedReceive.receive (state.rebind target).core (value.rewrite target ttl transport) =
      (EstablishedReceive.receive state.core value).rebind target :=
    EstablishedReceive.receive_rewrite state.core value target ttl valid.1 tuple transport
  unfold receive
  rw [ite_eq_right (not_not_intro rebound), ite_eq_right (not_not_intro valid)]
  dsimp only
  rw [core]
  dsimp only [EstablishedReceive.Result.rebind]
  cases selected : (EstablishedReceive.receive state.core value).decision with
  | blocked reason => cases reason <;> rfl
  | accepted count size =>
    change (⟨receiveState (state.rebind target) (value.rewrite target ttl transport)
      ((EstablishedReceive.receive state.core value).state.rebind target),
      .accepted (.receive count size), none, [], (EstablishedReceive.receive state.core value).ack⟩ : Result) = _
    rw [receiveState_rewrite]
    rfl

end Netlib.Protocol.TCP.Endpoint
