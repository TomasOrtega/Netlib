import Netlib.Protocol.TCP.Handshake
import Netlib.Protocol.TCP.ReceiveWindowEnabled

/-!
# ACK responses to consumed startup controls

An original SYN position lies before the receive cursor after consumption.
The sequence test rejects it for every unscaled window, including zero and wrap.
The response uses the current cursors and has no SYN or application payload.
This module constructs outputs without changing endpoint or timer state.
-/

namespace Netlib.Protocol.TCP.HandshakeDuplicate

open Handshake

theorem original_position_rejected (start : Seq) (window : Nat) (bounded : window ≤ 65535) :
    ReceiveWindow.accepts (start.add 1) window start 1 = false := by
  apply ReceiveWindow.whole_old_range_rejected start window 1 (by decide)
  unfold Seq.modulus
  omega

theorem syn_span (input : Input) (profile : Handshake.Profile input 2) :
    ReceiveWindow.segmentLength input.packet.segment = 1 := by
  change occupiedLength input.packet.segment.payload.length input.packet.segment.flags = 1
  rw [profile.1, profile.2.2]
  rfl

theorem synAck_span (input : Input) (profile : Handshake.Profile input 18) :
    ReceiveWindow.segmentLength input.packet.segment = 1 := by
  change occupiedLength input.packet.segment.payload.length input.packet.segment.flags = 1
  rw [profile.1, profile.2.2]
  rfl

theorem syn_rejected (input : Input) (profile : Handshake.Profile input 2)
    (window : Nat) (bounded : window ≤ 65535) :
    ReceiveWindow.acceptsSegment (input.packet.segment.sequence.add 1) window input.packet.segment = false := by
  rw [ReceiveWindow.acceptsSegment, syn_span input profile]
  exact original_position_rejected _ _ bounded

theorem synAck_rejected (input : Input) (profile : Handshake.Profile input 18)
    (window : Nat) (bounded : window ≤ 65535) :
    ReceiveWindow.acceptsSegment (input.packet.segment.sequence.add 1) window input.packet.segment = false := by
  rw [ReceiveWindow.acceptsSegment, synAck_span input profile]
  exact original_position_rejected _ _ bounded

theorem received_syn_rejected (pending : SynReceived) :
    ReceiveWindow.acceptsSegment (pending.input.packet.segment.sequence.add 1)
      pending.config.capacity pending.input.packet.segment = false :=
  syn_rejected pending.input pending.profile _ pending.localValid.1

theorem established_synAck_rejected (pending : SynSent) (input : Input)
    (ready : ActiveEstablished pending input) :
    ReceiveWindow.acceptsSegment ready.seed.core.receiveNext ready.seed.core.window input.packet.segment = false := by
  rw [ready.derived]
  simpa only [activeSeed, EstablishedReceive.State.window, List.length_nil, Nat.sub_zero] using
    synAck_rejected input ready.accepted.2.1 pending.config.capacity pending.localValid.1

theorem established_syn_rejected (pending : SynReceived) (input : Input)
    (ready : PassiveEstablished pending input) :
    ReceiveWindow.acceptsSegment ready.seed.core.receiveNext ready.seed.core.window pending.input.packet.segment = false := by
  rw [ready.derived]
  simpa only [passiveSeed, EstablishedReceive.State.window, List.length_nil, Nat.sub_zero] using
    received_syn_rejected pending

structure BareAck (header : Packet.Header) (sendNext receiveNext : Seq) (window ipLimit : Nat) where
  output : Input
  generated : ControlOutput.emit header sendNext receiveNext 16 window = .ok output
  fits : output.bytes.length ≤ ipLimit

def BareAck.make (header : Packet.Header) (sendNext receiveNext : Seq) (window ipLimit : Nat)
    (transport : header.protocol = Packet.Protocol.tcp) (bounded : window ≤ 65535)
    (room : 40 ≤ ipLimit) : BareAck header sendNext receiveNext window ipLimit := by
  let output : Input := ⟨ControlOutput.bytes header sendNext receiveNext 16 window,
    ControlOutput.packet header sendNext receiveNext 16 window,
    decodeIPv4_encodeIPv4 _ _ (ControlOutput.encoded _ _ _ _ _)⟩
  have generated : ControlOutput.emit header sendNext receiveNext 16 window = .ok output := by
    simp only [ControlOutput.emit, transport, ne_eq, not_true_eq_false, ite_false,
      show ControlOutput.Allowed 16 from Or.inr (Or.inr rfl), Nat.not_lt.mpr bounded]
    rfl
  refine ⟨output, generated, ?_⟩
  rw [ControlOutput.emit_length _ _ _ _ _ _ generated]
  exact room

variable {header : Packet.Header} {sendNext receiveNext : Seq} {window ipLimit : Nat}

theorem BareAck.transport (value : BareAck header sendNext receiveNext window ipLimit) :
    value.output.packet.header = header ∧ value.output.packet.segment.sequence = sendNext ∧
      value.output.packet.segment.acknowledgment = receiveNext ∧ value.output.packet.segment.window.val = window ∧
      value.output.packet.segment.flags = 16 ∧ value.output.packet.segment.options = [] ∧
      value.output.packet.segment.payload = [] ∧ value.output.packet.segment.reserved = 0 ∧
      value.output.packet.segment.urgentPointer = 0 :=
  ControlOutput.emit_transport _ _ _ _ _ _ value.generated

theorem BareAck.profile (value : BareAck header sendNext receiveNext window ipLimit) :
    Handshake.Profile value.output 16 := by
  have fields := value.transport
  exact ⟨fields.2.2.2.2.1, by simpa only [Handshake.optionProfile, ite_true] using fields.2.2.2.2.2.1,
    fields.2.2.2.2.2.2.1⟩

theorem BareAck.span (value : BareAck header sendNext receiveNext window ipLimit) :
    ReceiveWindow.segmentLength value.output.packet.segment = 0 := by
  change occupiedLength value.output.packet.segment.payload.length value.output.packet.segment.flags = 0
  rw [value.profile.1, value.profile.2.2]
  rfl

theorem BareAck.checksums (value : BareAck header sendNext receiveNext window ipLimit) :
    checksumAccepts value.output.packet.ip.packet.source value.output.packet.ip.packet.destination
        value.output.packet.segment = true ∧
      InternetChecksum.valid (IPv4.headerBytes value.output.packet.ip.packet value.output.packet.ip.checksum) = true :=
  ControlOutput.emit_checksums _ _ _ _ _ _ value.generated

theorem BareAck.ttl (value : BareAck header sendNext receiveNext window ipLimit) :
    value.output.packet.ip.packet.ttl.toNat = 64 := by
  rw [(ControlOutput.emit_fields _ _ _ _ _ _ value.generated).2.2.2.2]
  rfl

theorem BareAck.length (value : BareAck header sendNext receiveNext window ipLimit) :
    value.output.bytes.length = 40 :=
  ControlOutput.emit_length _ _ _ _ _ _ value.generated

theorem BareAck.ip_length (value : BareAck header sendNext receiveNext window ipLimit) :
    value.output.packet.ip.packet.wireLength = 40 := by
  rw [(ControlOutput.emit_fields _ _ _ _ _ _ value.generated).2.2.2.2]
  simp only [ControlOutput.packet, IPv4.Packet.wireLength, ControlOutput.ipPacket, Segment.encodeBytes_length,
    ControlOutput.segment, computed, rechecksum, Segment.wireLength, Segment.headerLength, List.length_nil]

theorem BareAck.ip_fits (value : BareAck header sendNext receiveNext window ipLimit) :
    value.output.packet.ip.packet.wireLength ≤ ipLimit := by
  rw [value.ip_length]
  simpa only [value.length] using value.fits

def syn_received_ack (pending : SynReceived) :
    BareAck (Output.reverse pending.input.packet.header) (pending.config.iss.add 1)
      (pending.input.packet.segment.sequence.add 1) pending.config.capacity pending.config.ipSendLimit :=
  BareAck.make _ _ _ _ _ (by rfl) pending.localValid.1 (Nat.le_of_lt pending.localValid.2.2.1)

def active_established_ack (pending : SynSent) (input : Input) (ready : ActiveEstablished pending input) :
    BareAck (Output.reverse ready.seed.core.inbound) ready.seed.core.sendNext ready.seed.core.receiveNext
      ready.seed.core.window ready.seed.ipSendLimit :=
  BareAck.make _ _ _ _ _ ready.valid.1.1
    (EstablishedReceive.State.window_bound _ ready.valid.1) (by
      rw [ready.derived]
      exact Nat.le_of_lt pending.localValid.2.2.1)

def passive_established_ack (pending : SynReceived) (input : Input) (ready : PassiveEstablished pending input) :
    BareAck (Output.reverse ready.seed.core.inbound) ready.seed.core.sendNext ready.seed.core.receiveNext
      ready.seed.core.window ready.seed.ipSendLimit :=
  BareAck.make _ _ _ _ _ ready.valid.1.1
    (EstablishedReceive.State.window_bound _ ready.valid.1) (by
      rw [ready.derived]
      exact Nat.le_of_lt pending.localValid.2.2.1)

end Netlib.Protocol.TCP.HandshakeDuplicate
