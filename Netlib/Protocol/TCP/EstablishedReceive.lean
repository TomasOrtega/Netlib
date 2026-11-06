import Netlib.Protocol.TCP.ReceiveWindow
import Netlib.Protocol.TCP.Rewrite

/-!
# A receive projection for a pre-established TCP endpoint

The caller supplies the initial tuple, cursors, and sent-byte buffer.
The caller assumes that the endpoint transmitted these buffer bytes.
This module does not prove a handshake or a transmission history.
Local capacity limits the receive buffer. The peer window does not set this capacity.
The profile selects the DATA check in [RFC 5961, section 5.2](https://www.rfc-editor.org/rfc/rfc5961.html#section-5.2).
It uses the permitted fixed MAX.SND.WND value 65535, without scaling.
It processes ACKs and in-order data within the available receive capacity.
The profile does not process controls, options, overlap trimming, or out-of-order storage.
The control and option scope gate precedes the sequence test.
This gate limits the profile. It does not specify the RFC action order.
For supported input, the exact sequence test precedes ACK processing.
An ACK request is not a transmitted packet.
This module has no send events, timer updates, or packet emission.
It does not update SND.WND, SND.WL1, or SND.WL2.
ACK rate limits remain outside this projection.
PSH has no effect in this projection.
Endpoint progress does not prove conntrack acceptance or state transfer.
-/

namespace Netlib.Protocol.TCP.EstablishedReceive

def maxSendWindow : Nat := 65535

structure State where
  inbound : Packet.Header
  receiveNext : Seq
  capacity : Nat
  received : List UInt8
  sendUna : Seq
  sendNext : Seq
  sent : List UInt8
  deriving Repr, BEq, DecidableEq

def State.window (state : State) : Nat := state.capacity - state.received.length

def State.ShortArc (state : State) : Prop := state.sent.length + maxSendWindow < Seq.halfSpace

def State.Valid (state : State) : Prop :=
  state.inbound.protocol = Packet.Protocol.tcp ∧
    state.received.length ≤ state.capacity ∧ state.capacity ≤ 65535 ∧
    state.sent.length ≤ maxSendWindow ∧ state.sendUna.add state.sent.length = state.sendNext ∧ state.ShortArc

instance (state : State) : Decidable state.Valid := by
  unfold State.Valid State.ShortArc
  infer_instance

structure Input where
  bytes : List UInt8
  packet : DecodedIPv4
  checked : decodeIPv4 bytes = .ok packet

def input (bytes : List UInt8) : Except String Input :=
  match checked : decodeIPv4 bytes with
  | .error reason => .error reason
  | .ok packet => .ok ⟨bytes, packet, checked⟩

theorem Input.valid (value : Input) : TCPRewrite.SourceValid value.packet :=
  TCPRewrite.sourceValid_of_decoded value.bytes value.packet value.checked

inductive Reject where
  | invalidSeed | tuple | sequence | missingAck | acknowledgment
  deriving Repr, BEq, DecidableEq

inductive Unsupported where
  | reset | synchronize | finish | urgent | congestion | options | trimming | outOfOrder
  deriving Repr, BEq, DecidableEq

inductive Block where
  | reject (reason : Reject)
  | unsupported (reason : Unsupported)
  deriving Repr, BEq, DecidableEq

inductive Decision where
  | blocked (reason : Block)
  | accepted (acknowledged received : Nat)
  deriving Repr, BEq, DecidableEq

inductive AckKind where
  | sequence | challenge | data
  deriving Repr, BEq, DecidableEq

structure AckRequest where
  kind : AckKind
  sequence : Seq
  acknowledgment : Seq
  window : Nat
  deriving Repr, BEq, DecidableEq

structure Result where
  state : State
  decision : Decision
  ack : Option AckRequest
  deriving Repr, BEq, DecidableEq

def request (state : State) (kind : AckKind) : AckRequest :=
  ⟨kind, state.sendNext, state.receiveNext, state.window⟩

def blocked (state : State) (reason : Block) (kind : Option AckKind := none) : Result :=
  ⟨state, .blocked reason, kind.map (request state)⟩

def control (segment : Segment) : Option Unsupported :=
  if Flags.rst segment.flags then some .reset
  else if Flags.syn segment.flags then some .synchronize
  else if Flags.fin segment.flags then some .finish
  else if Flags.urg segment.flags then some .urgent
  else if Flags.ece segment.flags || Flags.cwr segment.flags then some .congestion
  else if !segment.options.isEmpty then some .options
  else none

-- The two ACK coordinates use the same short arc through SND.UNA.
def acknowledgedCountAt (sendUna : Seq) (sentLength : Nat) (ack : Seq) : Option Nat :=
  if Seq.distance sendUna ack ≤ sentLength then some (Seq.distance sendUna ack)
  else if Seq.distance ack sendUna ≤ maxSendWindow then some 0
  else none

attribute [irreducible] acknowledgedCountAt

def acknowledgedCount (state : State) (ack : Seq) : Option Nat :=
  acknowledgedCountAt state.sendUna state.sent.length ack

def AckInRange (state : State) (ack : Seq) : Prop :=
  Seq.distance (state.sendUna.add (Seq.modulus - maxSendWindow)) ack ≤ maxSendWindow + state.sent.length

def commit (state : State) (payload : List UInt8) (count : Nat) : State :=
  { state with
    receiveNext := state.receiveNext.add payload.length
    received := state.received ++ payload
    sendUna := state.sendUna.add count
    sent := state.sent.drop count }

def finish (state : State) (segment : Segment) (count : Nat) : Result :=
  if segment.payload ≠ [] ∧ segment.sequence ≠ state.receiveNext then
    blocked state (.unsupported (if Seq.before segment.sequence state.receiveNext then .trimming else .outOfOrder))
  else if segment.payload.length > state.window then blocked state (.unsupported .trimming)
  else
    let after := commit state segment.payload count
    ⟨after, .accepted count segment.payload.length,
      if segment.payload.isEmpty then none else some (request after .data)⟩

inductive Gate where
  | blocked (reason : Block) (kind : Option AckKind)
  | next (count : Nat)
  deriving Repr, BEq, DecidableEq

def gateTailAt (receiveNext : Seq) (window : Nat) (sendUna : Seq) (sentLength : Nat) (segment : Segment) : Gate :=
  if !ReceiveWindow.acceptsSegment receiveNext window segment then
    .blocked (.reject .sequence) (if Flags.rst segment.flags then none else some .sequence)
  else if !Flags.ack segment.flags then .blocked (.reject .missingAck) none
  else match acknowledgedCountAt sendUna sentLength segment.acknowledgment with
    | none => .blocked (.reject .acknowledgment) (some .challenge)
    | some count => .next count

def gateTail (state : State) (segment : Segment) : Gate :=
  gateTailAt state.receiveNext state.window state.sendUna state.sent.length segment

def gate (state : State) (header : Packet.Header) (segment : Segment) : Gate :=
  if ¬state.Valid then .blocked (.reject .invalidSeed) none
  else if header ≠ state.inbound then .blocked (.reject .tuple) none
  else if let some reason := control segment then .blocked (.unsupported reason) none
  else gateTail state segment

def evaluate (state : State) (header : Packet.Header) (segment : Segment) : Result :=
  match gate state header segment with
  | .blocked reason kind => blocked state reason kind
  | .next count => finish state segment count

def receive (state : State) (value : Input) : Result := evaluate state value.packet.header value.packet.segment

theorem State.window_bound (state : State) (valid : state.Valid) : state.window ≤ 65535 := by
  have capacity := valid.2.2.1
  unfold State.window
  omega

theorem State.sent_short (state : State) (valid : state.Valid) : state.sent.length < Seq.halfSpace := by
  have selected := valid.2.2.2.2.2
  unfold State.ShortArc at selected
  omega

theorem Input.segment_encodable (value : Input) : value.packet.segment.Encodable :=
  (decode_fields _ _ _ _ value.valid.1.2).1

theorem Input.segmentLength_short (value : Input) : ReceiveWindow.segmentLength value.packet.segment < Seq.halfSpace :=
  ReceiveWindow.segmentLength_short value.packet.segment value.segment_encodable

theorem acknowledgedCount_bounded (state : State) (ack : Seq) (count : Nat)
    (selected : acknowledgedCount state ack = some count) : count ≤ state.sent.length := by
  unfold acknowledgedCount acknowledgedCountAt at selected
  split at selected
  · cases selected
    assumption
  · split at selected
    · cases selected
      omega
    · cases selected

theorem acknowledgedCount_forward (state : State) (ack : Seq)
    (inside : Seq.distance state.sendUna ack ≤ state.sent.length) :
    acknowledgedCount state ack = some (Seq.distance state.sendUna ack) := by
  simp only [acknowledgedCount, acknowledgedCountAt, inside, ite_true]

theorem acknowledgedCount_old (state : State) (ack : Seq) (short : state.ShortArc)
    (old : Seq.distance ack state.sendUna ≤ maxSendWindow) : acknowledgedCount state ack = some 0 := by
  by_cases same : state.sendUna = ack
  · simp [acknowledgedCount, acknowledgedCountAt, same]
  · have total := Seq.distance_reverse state.sendUna ack same
    have outside : ¬Seq.distance state.sendUna ack ≤ state.sent.length := by
      unfold State.ShortArc Seq.halfSpace maxSendWindow at short
      simp only [Seq.modulus, maxSendWindow] at total old
      omega
    simp only [acknowledgedCount, acknowledgedCountAt, outside, ite_false, old, ite_true]

theorem ack_range_coordinates (state : State) (ack : Seq) (short : state.ShortArc) :
    AckInRange state ack ↔
      Seq.distance state.sendUna ack ≤ state.sent.length ∨ Seq.distance ack state.sendUna ≤ maxSendWindow := by
  let base := state.sendUna.add (Seq.modulus - maxSendWindow)
  have closes : base.add maxSendWindow = state.sendUna := by
    dsimp only [base]
    rw [Seq.add_add]
    have sum : Seq.modulus - maxSendWindow + maxSendWindow = Seq.modulus := by decide
    rw [sum, Seq.add_modulus]
  have offset : Seq.distance base state.sendUna = maxSendWindow := by
    have selected := Seq.distance_add base maxSendWindow
    rw [closes, Nat.mod_eq_of_lt (by decide)] at selected
    exact selected
  have route := Seq.distance_triangle_mod base state.sendUna ack
  rw [offset] at route
  have forwardBound := Seq.distance_lt state.sendUna ack
  by_cases same : state.sendUna = ack
  · subst ack
    simp only [AckInRange, ← show base = state.sendUna.add (Seq.modulus - maxSendWindow) from rfl,
      offset, Seq.distance_self]
    omega
  · have total := Seq.distance_reverse state.sendUna ack same
    change Seq.distance base ack ≤ maxSendWindow + state.sent.length ↔ _
    rw [route]
    unfold State.ShortArc Seq.halfSpace maxSendWindow at short
    simp only [Seq.modulus, maxSendWindow] at total forwardBound ⊢
    omega

theorem acknowledgedCount_range (state : State) (ack : Seq) (short : state.ShortArc) :
    (acknowledgedCount state ack).isSome = true ↔ AckInRange state ack := by
  rw [ack_range_coordinates state ack short]
  by_cases forward : Seq.distance state.sendUna ack ≤ state.sent.length <;>
    by_cases old : Seq.distance ack state.sendUna ≤ maxSendWindow <;>
    simp [acknowledgedCount, acknowledgedCountAt, forward, old]

theorem acknowledgedCount_outside (state : State) (ack : Seq) (short : state.ShortArc)
    (outside : ¬AckInRange state ack) : acknowledgedCount state ack = none := by
  have notSome : (acknowledgedCount state ack).isSome ≠ true := by
    intro selected
    exact outside ((acknowledgedCount_range state ack short).mp selected)
  cases selected : acknowledgedCount state ack with
  | none => rfl
  | some count => simp [selected] at notSome

@[simp] theorem commit_sendNext (state : State) (payload : List UInt8) (count : Nat) :
    (commit state payload count).sendNext = state.sendNext := rfl

@[simp] theorem commit_received (state : State) (payload : List UInt8) (count : Nat) :
    (commit state payload count).received = state.received ++ payload := rfl

@[simp] theorem commit_receiveNext (state : State) (payload : List UInt8) (count : Nat) :
    (commit state payload count).receiveNext = state.receiveNext.add payload.length := rfl

@[simp] theorem commit_sent (state : State) (payload : List UInt8) (count : Nat) :
    (commit state payload count).sent = state.sent.drop count := rfl

@[simp] theorem commit_sendUna (state : State) (payload : List UInt8) (count : Nat) :
    (commit state payload count).sendUna = state.sendUna.add count := rfl

theorem commit_valid (state : State) (payload : List UInt8) (count : Nat) (valid : state.Valid)
    (fits : payload.length ≤ state.window) (acknowledged : count ≤ state.sent.length) :
    (commit state payload count).Valid := by
  obtain ⟨protocol, received, capacity, sent, cursors, short⟩ := valid
  refine ⟨protocol, ?_, capacity, ?_, ?_, ?_⟩
  · change (state.received ++ payload).length ≤ state.capacity
    rw [List.length_append]
    unfold State.window at fits
    omega
  · change (state.sent.drop count).length ≤ maxSendWindow
    rw [List.length_drop]
    omega
  · change (state.sendUna.add count).add (state.sent.drop count).length = state.sendNext
    rw [List.length_drop, Seq.add_add, Nat.add_sub_of_le acknowledged]
    exact cursors
  · change (state.sent.drop count).length + maxSendWindow < Seq.halfSpace
    rw [List.length_drop]
    unfold State.ShortArc at short
    omega


def Effects (before : State) (segment : Segment) (result : Result) : Prop :=
  match result.decision with
  | .blocked _ => result.state = before
  | .accepted count size =>
    acknowledgedCount before segment.acknowledgment = some count ∧
      count ≤ before.sent.length ∧ size = segment.payload.length ∧
      segment.payload.length ≤ before.window ∧ result.state = commit before segment.payload count

theorem finish_effects (state : State) (segment : Segment) (count : Nat)
    (selected : acknowledgedCount state segment.acknowledgment = some count) :
    Effects state segment (finish state segment count) := by
  unfold finish
  split
  · rfl
  · split
    · rfl
    · exact ⟨selected, acknowledgedCount_bounded state segment.acknowledgment count selected,
        rfl, by omega, rfl⟩

theorem gate_count (state : State) (header : Packet.Header) (segment : Segment) (count : Nat)
    (selected : gate state header segment = .next count) :
    acknowledgedCount state segment.acknowledgment = some count := by
  unfold gate at selected
  split at selected
  · cases selected
  · split at selected
    · cases selected
    · cases controls : control segment with
      | some reason => simp [controls] at selected
      | none =>
        simp only [controls] at selected
        unfold gateTail gateTailAt at selected
        split at selected
        · cases selected
        · split at selected
          · cases selected
          · cases acknowledgment : acknowledgedCountAt state.sendUna state.sent.length segment.acknowledgment with
            | none => simp [acknowledgment] at selected
            | some amount =>
              simp only [acknowledgment, Gate.next.injEq] at selected
              cases selected
              simpa only [acknowledgedCount] using acknowledgment

theorem evaluate_effects (state : State) (header : Packet.Header) (segment : Segment) :
    Effects state segment (evaluate state header segment) := by
  unfold evaluate
  cases selected : gate state header segment with
  | blocked reason kind => rfl
  | next count => exact finish_effects state segment count (gate_count state header segment count selected)

theorem receive_effects (state : State) (value : Input) : Effects state value.packet.segment (receive state value) :=
  evaluate_effects state value.packet.header value.packet.segment

theorem receive_blocked_preserves (state : State) (value : Input) (reason : Block)
    (selected : (receive state value).decision = .blocked reason) : (receive state value).state = state := by
  have effects := receive_effects state value
  simpa only [Effects, selected] using effects

theorem receive_accepted (state : State) (value : Input) (count size : Nat)
    (selected : (receive state value).decision = .accepted count size) :
    acknowledgedCount state value.packet.segment.acknowledgment = some count ∧
      count ≤ state.sent.length ∧ size = value.packet.segment.payload.length ∧
      value.packet.segment.payload.length ≤ state.window ∧
      (receive state value).state = commit state value.packet.segment.payload count := by
  have effects := receive_effects state value
  simpa only [Effects, selected] using effects

theorem receive_valid (state : State) (value : Input) (valid : state.Valid) : (receive state value).state.Valid := by
  cases selected : (receive state value).decision with
  | blocked reason => rw [receive_blocked_preserves state value reason selected]; exact valid
  | accepted count size =>
    obtain ⟨_, bounded, _, fits, after⟩ := receive_accepted state value count size selected
    rw [after]
    exact commit_valid state value.packet.segment.payload count valid fits bounded

theorem receive_buffer_bounds (state : State) (value : Input) (valid : state.Valid) :
    (receive state value).state.received.length ≤ state.capacity ∧
      (receive state value).state.sent.length ≤ maxSendWindow := by
  cases selected : (receive state value).decision with
  | blocked reason =>
    rw [receive_blocked_preserves state value reason selected]
    exact ⟨valid.2.1, valid.2.2.2.1⟩
  | accepted count size =>
    obtain ⟨_, bounded, _, fits, after⟩ := receive_accepted state value count size selected
    rw [after]
    have retained := commit_valid state value.packet.segment.payload count valid fits bounded
    exact ⟨retained.2.1, retained.2.2.2.1⟩

theorem receive_sendNext (state : State) (value : Input) : (receive state value).state.sendNext = state.sendNext := by
  cases selected : (receive state value).decision with
  | blocked reason => rw [receive_blocked_preserves state value reason selected]
  | accepted count size =>
    rw [(receive_accepted state value count size selected).2.2.2.2]
    rfl

theorem receive_payload (state : State) (value : Input) (count size : Nat)
    (selected : (receive state value).decision = .accepted count size) :
    (receive state value).state.received = state.received ++ value.packet.segment.payload ∧
      (receive state value).state.receiveNext = state.receiveNext.add value.packet.segment.payload.length := by
  rw [(receive_accepted state value count size selected).2.2.2.2]
  exact ⟨rfl, rfl⟩

theorem receive_ack_prefix (state : State) (value : Input) (count size : Nat)
    (selected : (receive state value).decision = .accepted count size) :
    (receive state value).state.sent = state.sent.drop count ∧
      (receive state value).state.sendUna = state.sendUna.add count ∧
      (receive state value).state.sendNext = state.sendNext := by
  rw [(receive_accepted state value count size selected).2.2.2.2]
  exact ⟨rfl, rfl, rfl⟩

theorem receive_wire_ack (state : State) (value : Input) (count size : Nat)
    (selected : (receive state value).decision = .accepted count size)
    (forward : Seq.distance state.sendUna value.packet.segment.acknowledgment ≤ state.sent.length) :
    (receive state value).state.sendUna = value.packet.segment.acknowledgment := by
  have computed := (receive_accepted state value count size selected).1
  rw [acknowledgedCount_forward state value.packet.segment.acknowledgment forward] at computed
  cases Option.some.inj computed
  rw [(receive_ack_prefix state value _ size selected).2.1]
  exact Seq.add_distance state.sendUna value.packet.segment.acknowledgment


def Ready (state : State) (header : Packet.Header) (segment : Segment) : Prop :=
  state.Valid ∧ header = state.inbound ∧
    ReceiveWindow.acceptsSegment state.receiveNext state.window segment = true ∧
    control segment = none ∧ Flags.ack segment.flags = true

theorem gate_of_ready (state : State) (header : Packet.Header) (segment : Segment)
    (ready : Ready state header segment) : gate state header segment =
    match acknowledgedCount state segment.acknowledgment with
    | none => .blocked (.reject .acknowledgment) (some .challenge)
    | some count => .next count := by
  obtain ⟨valid, tuple, sequence, controls, ack⟩ := ready
  cases selected : acknowledgedCount state segment.acknowledgment <;>
    change acknowledgedCountAt state.sendUna state.sent.length segment.acknowledgment = _ at selected <;>
    unfold gate <;>
    rw [ite_eq_right (not_not_intro valid)] <;>
    rw [ite_eq_right (show ¬header ≠ state.inbound from not_not_intro tuple)] <;>
    rw [controls] <;>
    dsimp only <;>
    unfold gateTail gateTailAt <;>
    rw [ite_eq_right (show ¬(!ReceiveWindow.acceptsSegment state.receiveNext state.window segment) = true by
      simp only [sequence, Bool.not_true, Bool.false_eq_true, not_false_eq_true])] <;>
    rw [ite_eq_right (show ¬(!Flags.ack segment.flags) = true by
      simp only [ack, Bool.not_true, Bool.false_eq_true, not_false_eq_true])] <;>
    rw [selected]

theorem evaluate_of_ready (state : State) (header : Packet.Header) (segment : Segment)
    (ready : Ready state header segment) : evaluate state header segment =
    match acknowledgedCount state segment.acknowledgment with
    | none => blocked state (.reject .acknowledgment) (some .challenge)
    | some count => finish state segment count := by
  rw [evaluate, gate_of_ready state header segment ready]
  cases selected : acknowledgedCount state segment.acknowledgment <;> rfl

theorem gate_next_ready (state : State) (header : Packet.Header) (segment : Segment) (count : Nat)
    (selected : gate state header segment = .next count) : Ready state header segment := by
  by_cases valid : state.Valid
  · by_cases tuple : header = state.inbound
    · cases controls : control segment with
      | some reason => simp [gate, valid, tuple, controls] at selected
      | none =>
        by_cases sequence : ReceiveWindow.acceptsSegment state.receiveNext state.window segment = true
        · by_cases ack : Flags.ack segment.flags = true
          · exact ⟨valid, tuple, sequence, controls, ack⟩
          · simp [gate, gateTail, gateTailAt, valid, tuple, sequence, controls, ack] at selected
        · simp [gate, gateTail, gateTailAt, valid, tuple, sequence, controls] at selected
    · simp [gate, valid, tuple] at selected
  · simp [gate, valid] at selected

theorem evaluate_accepted_ready (state : State) (header : Packet.Header) (segment : Segment) (count size : Nat)
    (selected : (evaluate state header segment).decision = .accepted count size) : Ready state header segment := by
  unfold evaluate at selected
  cases chosen : gate state header segment with
  | blocked reason kind => simp [chosen, blocked] at selected
  | next amount => exact gate_next_ready state header segment amount chosen

theorem receive_accepted_ready (state : State) (value : Input) (count size : Nat)
    (selected : (receive state value).decision = .accepted count size) :
    Ready state value.packet.header value.packet.segment := evaluate_accepted_ready state _ _ count size selected

theorem receive_sequence_first (state : State) (value : Input) (valid : state.Valid)
    (tuple : value.packet.header = state.inbound)
    (controls : control value.packet.segment = none)
    (sequence : ReceiveWindow.acceptsSegment state.receiveNext state.window value.packet.segment = false) :
    receive state value = blocked state (.reject .sequence)
      (if Flags.rst value.packet.segment.flags then none else some .sequence) := by
  simp only [receive, evaluate, gate, gateTail, gateTailAt, valid, not_true_eq_false, ite_false, tuple, ne_eq,
    controls, sequence, Bool.not_false, ite_true]

theorem receive_control (state : State) (value : Input) (valid : state.Valid)
    (tuple : value.packet.header = state.inbound)
    (reason : Unsupported) (controls : control value.packet.segment = some reason) :
    receive state value = blocked state (.unsupported reason) := by
  simp only [receive, evaluate, gate, valid, not_true_eq_false, ite_false, tuple, ne_eq,
    controls]

theorem receive_ack_outside (state : State) (value : Input)
    (ready : Ready state value.packet.header value.packet.segment)
    (outside : ¬AckInRange state value.packet.segment.acknowledgment) :
    receive state value = blocked state (.reject .acknowledgment) (some .challenge) := by
  rw [receive, evaluate_of_ready state _ _ ready,
    acknowledgedCount_outside state _ ready.1.2.2.2.2.2 outside]

theorem finish_of_fits (state : State) (segment : Segment) (count : Nat)
    (inOrder : segment.sequence = state.receiveNext) (fits : segment.payload.length ≤ state.window) :
    finish state segment count =
      ⟨commit state segment.payload count, .accepted count segment.payload.length,
        if segment.payload.isEmpty then none else some (request (commit state segment.payload count) .data)⟩ := by
  simp [finish, inOrder, Nat.not_lt.mpr fits]

theorem receive_old_ack_data (state : State) (value : Input)
    (ready : Ready state value.packet.header value.packet.segment)
    (old : Seq.distance value.packet.segment.acknowledgment state.sendUna ≤ maxSendWindow)
    (inOrder : value.packet.segment.sequence = state.receiveNext)
    (fits : value.packet.segment.payload.length ≤ state.window) :
    receive state value =
      ⟨commit state value.packet.segment.payload 0, .accepted 0 value.packet.segment.payload.length,
        if value.packet.segment.payload.isEmpty then none
        else some (request (commit state value.packet.segment.payload 0) .data)⟩ := by
  rw [receive, evaluate_of_ready state _ _ ready,
    acknowledgedCount_old state _ ready.1.2.2.2.2.2 old]
  exact finish_of_fits state value.packet.segment 0 inOrder fits

theorem receive_old_ack_preserves_send (state : State) (value : Input)
    (ready : Ready state value.packet.header value.packet.segment)
    (old : Seq.distance value.packet.segment.acknowledgment state.sendUna ≤ maxSendWindow)
    (inOrder : value.packet.segment.sequence = state.receiveNext)
    (fits : value.packet.segment.payload.length ≤ state.window) :
    (receive state value).state.sent = state.sent ∧ (receive state value).state.sendUna = state.sendUna ∧
      (receive state value).state.receiveNext = state.receiveNext.add value.packet.segment.payload.length := by
  rw [receive_old_ack_data state value ready old inOrder fits]
  simp only [commit, Seq.add_zero, List.drop_zero, and_self]



theorem acknowledgedCount_beyond_next (state : State) (extra : Nat) (valid : state.Valid)
    (positive : 0 < extra) (short : state.sent.length + extra < Seq.halfSpace) :
    acknowledgedCount state (state.sendNext.add extra) = none := by
  have bounded : state.sent.length + extra < Seq.modulus := by
    unfold Seq.modulus Seq.halfSpace at *
    omega
  have forward : Seq.distance state.sendUna (state.sendNext.add extra) = state.sent.length + extra := by
    rw [← valid.2.2.2.2.1, Seq.add_add, Seq.distance_add, Nat.mod_eq_of_lt bounded]
  have different : state.sendUna ≠ state.sendNext.add extra := by
    intro same
    rw [same, Seq.distance_self] at forward
    omega
  have total := Seq.distance_reverse state.sendUna (state.sendNext.add extra) different
  have notOld : ¬Seq.distance (state.sendNext.add extra) state.sendUna ≤ maxSendWindow := by
    rw [forward] at total
    unfold Seq.modulus at total
    unfold Seq.halfSpace at short
    unfold maxSendWindow
    omega
  have beyond : ¬state.sent.length + extra ≤ state.sent.length := by omega
  simp only [acknowledgedCount, acknowledgedCountAt, forward, beyond, ite_false, notOld]

theorem receive_beyond_next (state : State) (value : Input) (extra : Nat)
    (ready : Ready state value.packet.header value.packet.segment)
    (ack : value.packet.segment.acknowledgment = state.sendNext.add extra)
    (positive : 0 < extra) (short : state.sent.length + extra < Seq.halfSpace) :
    receive state value = blocked state (.reject .acknowledgment) (some .challenge) := by
  rw [receive, evaluate_of_ready state _ _ ready, ack, acknowledgedCount_beyond_next state extra ready.1 positive short]

def State.rebind (state : State) (header : Packet.Header) : State := { state with inbound := header }

def Result.rebind (result : Result) (header : Packet.Header) : Result :=
  { result with state := result.state.rebind header }

theorem State.rebind_valid (state : State) (header : Packet.Header) (valid : state.Valid)
    (transport : header.protocol = Packet.Protocol.tcp) : (state.rebind header).Valid :=
  ⟨transport, valid.2⟩

theorem gateTail_rebind (state : State) (header : Packet.Header) (segment : Segment) :
    gateTail (state.rebind header) segment = gateTail state segment := rfl


theorem finish_rebind (state : State) (header : Packet.Header) (segment : Segment) (count : Nat) :
    finish (state.rebind header) segment count = (finish state segment count).rebind header := by
  by_cases empty : segment.payload = [] <;>
    by_cases order : segment.sequence = state.receiveNext <;>
    by_cases fits : segment.payload.length > state.capacity - state.received.length <;>
    simp [finish, State.rebind, Result.rebind, blocked, commit, request, State.window, empty, order, fits]

theorem gate_rebind (state : State) (header : Packet.Header) (segment : Segment) (valid : state.Valid)
    (transport : header.protocol = Packet.Protocol.tcp) :
    gate (state.rebind header) header segment = gate state state.inbound segment := by
  have rebound := state.rebind_valid header valid transport
  unfold gate
  rw [ite_eq_right (not_not_intro rebound), ite_eq_right (not_not_intro valid)]
  rw [ite_eq_right (show ¬header ≠ (state.rebind header).inbound from not_not_intro rfl)]
  rw [ite_eq_right (show ¬state.inbound ≠ state.inbound from not_not_intro rfl)]
  cases controls : control segment with
  | some reason => rfl
  | none => exact gateTail_rebind state header segment

theorem evaluate_rebind (state : State) (header : Packet.Header) (segment : Segment) (valid : state.Valid)
    (transport : header.protocol = Packet.Protocol.tcp) :
    evaluate (state.rebind header) header segment = (evaluate state state.inbound segment).rebind header := by
  unfold evaluate
  rw [gate_rebind state header segment valid transport]
  cases selected : gate state state.inbound segment with
  | blocked reason kind => rfl
  | next count => exact finish_rebind state header segment count

theorem evaluate_rewrite_segment (state : State) (header : Packet.Header) (value : DecodedIPv4)
    (target : Packet.Header) :
    evaluate state header (TCPRewrite.segment value target) = evaluate state header value.segment := by
  have fields := TCPRewrite.segment_transport value target
  have sequence := fields.1
  have acknowledgment := fields.2.1
  have flags := fields.2.2.2.1
  have options := fields.2.2.2.2.2.2
  have payload := TCPRewrite.segment_payload value target
  have sequenceTest : ReceiveWindow.acceptsSegment state.receiveNext state.window (TCPRewrite.segment value target) =
      ReceiveWindow.acceptsSegment state.receiveNext state.window value.segment := by
    simp only [ReceiveWindow.acceptsSegment, ReceiveWindow.segmentLength, sequence, flags, payload]
  have controls : control (TCPRewrite.segment value target) = control value.segment := by
    simp only [control, flags, options]
  have gates : gate state header (TCPRewrite.segment value target) = gate state header value.segment := by
    simp only [gate, gateTail, gateTailAt, sequenceTest, controls, flags, acknowledgment]
  have finishTest (count : Nat) : finish state (TCPRewrite.segment value target) count = finish state value.segment count := by
    simp only [finish, sequence, payload]
  unfold evaluate
  rw [gates]
  cases selected : gate state header value.segment with
  | blocked reason kind => rfl
  | next count => exact finishTest count

def Input.rewrite (value : Input) (target : Packet.Header) (ttl : UInt8)
    (transport : target.protocol = Packet.Protocol.tcp) : Input :=
  let result := TCPRewrite.rewrite value.packet target ttl value.valid transport
  ⟨result.bytes, result.packet, result.decoded⟩

theorem receive_rewrite (state : State) (value : Input) (target : Packet.Header) (ttl : UInt8)
    (valid : state.Valid) (tuple : value.packet.header = state.inbound)
    (transport : target.protocol = Packet.Protocol.tcp) :
    receive (state.rebind target) (value.rewrite target ttl transport) = (receive state value).rebind target := by
  let result := TCPRewrite.rewrite value.packet target ttl value.valid transport
  change evaluate (state.rebind target) result.packet.header result.packet.segment =
    (evaluate state value.packet.header value.packet.segment).rebind target
  rw [result.header transport]
  change evaluate (state.rebind target) target (TCPRewrite.segment value.packet target) = _
  rw [evaluate_rewrite_segment, evaluate_rebind state target value.packet.segment valid transport, tuple]

theorem receive_rewrite_decision (state : State) (value : Input) (target : Packet.Header) (ttl : UInt8)
    (valid : state.Valid) (tuple : value.packet.header = state.inbound)
    (transport : target.protocol = Packet.Protocol.tcp) :
    (receive (state.rebind target) (value.rewrite target ttl transport)).decision = (receive state value).decision ∧
      (receive (state.rebind target) (value.rewrite target ttl transport)).ack = (receive state value).ack := by
  rw [receive_rewrite state value target ttl valid tuple transport]
  exact ⟨rfl, rfl⟩


def gateWithWindow (state : State) (header : Packet.Header) (segment : Segment) (window : Nat) : Gate :=
  if ¬state.Valid then .blocked (.reject .invalidSeed) none
  else if header ≠ state.inbound then .blocked (.reject .tuple) none
  else if let some reason := control segment then .blocked (.unsupported reason) none
  else gateTailAt state.receiveNext window state.sendUna state.sent.length segment

def withAckWindow (result : Result) (window : Nat) : Result :=
  { result with ack := result.ack.map (fun request => { request with window }) }

def evaluateWithWindow (state : State) (header : Packet.Header) (segment : Segment) (window : Nat) : Result :=
  match gateWithWindow state header segment window with
  | .blocked reason kind => withAckWindow (blocked state reason kind) window
  | .next count =>
    if segment.payload.length > window then blocked state (.unsupported .trimming)
    else
      let result := finish state segment count
      withAckWindow result (window - match result.decision with | .accepted _ size => size | _ => 0)

def receiveWithWindow (state : State) (value : Input) (window : Nat) : Result :=
  evaluateWithWindow state value.packet.header value.packet.segment window

theorem gateWithWindow_count (state : State) (header : Packet.Header) (segment : Segment) (window count : Nat)
    (selected : gateWithWindow state header segment window = .next count) :
    acknowledgedCount state segment.acknowledgment = some count := by
  unfold gateWithWindow at selected
  split at selected
  · cases selected
  · split at selected
    · cases selected
    · cases controls : control segment with
      | some reason => simp [controls] at selected
      | none =>
        simp only [controls] at selected
        unfold gateTailAt at selected
        split at selected
        · cases selected
        · split at selected
          · cases selected
          · cases acknowledgment : acknowledgedCountAt state.sendUna state.sent.length segment.acknowledgment with
            | none => simp [acknowledgment] at selected
            | some amount =>
              simp only [acknowledgment, Gate.next.injEq] at selected
              cases selected
              simpa only [acknowledgedCount] using acknowledgment

theorem receiveWithWindow_effects (state : State) (value : Input) (window : Nat) :
    Effects state value.packet.segment (receiveWithWindow state value window) := by
  unfold receiveWithWindow evaluateWithWindow
  cases selected : gateWithWindow state value.packet.header value.packet.segment window with
  | blocked reason kind => rfl
  | next count =>
    by_cases outside : value.packet.segment.payload.length > window
    · simp only [outside, ite_true]
      rfl
    · simpa only [outside, ite_false, Effects, withAckWindow] using
        finish_effects state value.packet.segment count (gateWithWindow_count state _ _ window count selected)

theorem receiveWithWindow_blocked_preserves (state : State) (value : Input) (window : Nat) (reason : Block)
    (selected : (receiveWithWindow state value window).decision = .blocked reason) :
    (receiveWithWindow state value window).state = state := by
  simpa only [Effects, selected] using receiveWithWindow_effects state value window

theorem receiveWithWindow_accepted (state : State) (value : Input) (window count size : Nat)
    (selected : (receiveWithWindow state value window).decision = .accepted count size) :
    acknowledgedCount state value.packet.segment.acknowledgment = some count ∧
      count ≤ state.sent.length ∧ size = value.packet.segment.payload.length ∧
      value.packet.segment.payload.length ≤ state.window ∧
      (receiveWithWindow state value window).state = commit state value.packet.segment.payload count := by
  simpa only [Effects, selected] using receiveWithWindow_effects state value window

theorem receiveWithWindow_payload_bound (state : State) (value : Input) (window count size : Nat)
    (selected : (receiveWithWindow state value window).decision = .accepted count size) :
    value.packet.segment.payload.length ≤ window := by
  unfold receiveWithWindow evaluateWithWindow at selected
  simp only [withAckWindow] at selected
  cases chosen : gateWithWindow state value.packet.header value.packet.segment window with
  | blocked reason kind => simp [chosen, blocked] at selected
  | next amount =>
    simp only [chosen] at selected
    split at selected
    · simp [blocked] at selected
    · omega

theorem receiveWithWindow_in_order (state : State) (value : Input) (window count size : Nat)
    (selected : (receiveWithWindow state value window).decision = .accepted count size)
    (nonempty : value.packet.segment.payload ≠ []) : value.packet.segment.sequence = state.receiveNext := by
  unfold receiveWithWindow evaluateWithWindow at selected
  simp only [withAckWindow] at selected
  cases chosen : gateWithWindow state value.packet.header value.packet.segment window with
  | blocked reason kind => simp [chosen, blocked] at selected
  | next amount =>
    simp only [chosen] at selected
    split at selected
    · simp [blocked] at selected
    · unfold finish at selected
      split at selected
      · simp [blocked] at selected
      · rename_i ordered
        by_cases same : value.packet.segment.sequence = state.receiveNext
        · exact same
        · exact False.elim (ordered ⟨nonempty, same⟩)

theorem receiveWithWindow_valid (state : State) (value : Input) (window : Nat) (valid : state.Valid) :
    (receiveWithWindow state value window).state.Valid := by
  cases selected : (receiveWithWindow state value window).decision with
  | blocked reason => rw [receiveWithWindow_blocked_preserves state value window reason selected]; exact valid
  | accepted count size =>
    obtain ⟨_, bounded, _, fits, after⟩ := receiveWithWindow_accepted state value window count size selected
    rw [after]
    exact commit_valid state value.packet.segment.payload count valid fits bounded

theorem gateWithWindow_rebind (state : State) (header : Packet.Header) (segment : Segment) (window : Nat)
    (valid : state.Valid) (transport : header.protocol = Packet.Protocol.tcp) :
    gateWithWindow (state.rebind header) header segment window = gateWithWindow state state.inbound segment window := by
  have rebound := state.rebind_valid header valid transport
  unfold gateWithWindow
  rw [ite_eq_right (not_not_intro rebound), ite_eq_right (not_not_intro valid)]
  rw [ite_eq_right (show ¬header ≠ (state.rebind header).inbound from not_not_intro rfl)]
  rw [ite_eq_right (show ¬state.inbound ≠ state.inbound from not_not_intro rfl)]
  cases controls : control segment <;> rfl

theorem evaluateWithWindow_rebind (state : State) (header : Packet.Header) (segment : Segment) (window : Nat)
    (valid : state.Valid) (transport : header.protocol = Packet.Protocol.tcp) :
    evaluateWithWindow (state.rebind header) header segment window =
      (evaluateWithWindow state state.inbound segment window).rebind header := by
  unfold evaluateWithWindow
  rw [gateWithWindow_rebind state header segment window valid transport]
  cases selected : gateWithWindow state state.inbound segment window with
  | blocked reason kind => rfl
  | next count =>
    by_cases outside : segment.payload.length > window
    · simp only [outside, ite_true]
      rfl
    · simp only [outside, ite_false]
      rw [finish_rebind state header segment count]
      rfl

theorem evaluateWithWindow_rewrite_segment (state : State) (header : Packet.Header) (value : DecodedIPv4)
    (target : Packet.Header) (window : Nat) :
    evaluateWithWindow state header (TCPRewrite.segment value target) window =
      evaluateWithWindow state header value.segment window := by
  have fields := TCPRewrite.segment_transport value target
  have sequence := fields.1
  have acknowledgment := fields.2.1
  have flags := fields.2.2.2.1
  have options := fields.2.2.2.2.2.2
  have payload := TCPRewrite.segment_payload value target
  have sequenceTest : ReceiveWindow.acceptsSegment state.receiveNext window (TCPRewrite.segment value target) =
      ReceiveWindow.acceptsSegment state.receiveNext window value.segment := by
    simp only [ReceiveWindow.acceptsSegment, ReceiveWindow.segmentLength, sequence, flags, payload]
  have controls : control (TCPRewrite.segment value target) = control value.segment := by
    simp only [control, flags, options]
  have gates : gateWithWindow state header (TCPRewrite.segment value target) window =
      gateWithWindow state header value.segment window := by
    simp only [gateWithWindow, gateTailAt, sequenceTest, controls, flags, acknowledgment]
  have finishTest (count : Nat) : finish state (TCPRewrite.segment value target) count = finish state value.segment count := by
    simp only [finish, sequence, payload]
  unfold evaluateWithWindow
  rw [gates]
  cases selected : gateWithWindow state header value.segment window with
  | blocked reason kind => rfl
  | next count =>
    simp only [payload]
    split
    · rfl
    · simp only [finishTest count]

theorem receiveWithWindow_rewrite (state : State) (value : Input) (window : Nat) (target : Packet.Header) (ttl : UInt8)
    (valid : state.Valid) (tuple : value.packet.header = state.inbound)
    (transport : target.protocol = Packet.Protocol.tcp) :
    receiveWithWindow (state.rebind target) (value.rewrite target ttl transport) window =
      (receiveWithWindow state value window).rebind target := by
  let result := TCPRewrite.rewrite value.packet target ttl value.valid transport
  change evaluateWithWindow (state.rebind target) result.packet.header result.packet.segment window =
    (evaluateWithWindow state value.packet.header value.packet.segment window).rebind target
  rw [result.header transport]
  change evaluateWithWindow (state.rebind target) target (TCPRewrite.segment value.packet target) window = _
  rw [evaluateWithWindow_rewrite_segment, evaluateWithWindow_rebind state target value.packet.segment window valid transport, tuple]

end Netlib.Protocol.TCP.EstablishedReceive
