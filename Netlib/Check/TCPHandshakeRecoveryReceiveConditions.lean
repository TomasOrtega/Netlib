import Netlib.Check.TCPHandshakeRecoveryInvariantCore
import Netlib.Check.TCPHandshakeRecoveryOutputShape
import Netlib.Check.TCPHandshakeWireDelivery
import Netlib.Protocol.TCP.HandshakeEnabled

/-!
# Current fields for a startup receive

The input retains its actual source and checked byte path.
The conditions compare received fields with the current phase and past receipts.
-/

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

structure ReceiveInput (state : State active passive) (index : Nat) (path : O.Path) where
  source : Emission
  selected : state.source source.index = some source
  earlier : source.index < index
  packet : H.Input
  delivery : X.Delivery source.packet (TCPHandshake.spec packet path)
  same : delivery.input = packet

def ReceiveInput.receipt (input : ReceiveInput state index path) : Receipt :=
  ⟨index, input.source, TCPHandshake.spec input.packet path, input.delivery, input.earlier⟩

def ReceiveInput.event (input : ReceiveInput state index path) : Event :=
  .receive input.source.index input.packet.bytes path true

def ReceiveIndex (state : State active passive) (index : Nat) : Prop :=
  state.last.isNone || decide (state.last.getD 0 < index) = true

def SameDecoded (packet original : H.Input) : Prop :=
  packet.packet.header = original.packet.header ∧ packet.packet.segment = original.packet.segment

def EmptyAckFields (before : PreData seed) (packet : H.Input) (index : Nat) : Prop :=
  Handshake.Profile packet 16 ∧ packet.packet.header = before.current.core.inbound ∧
    packet.packet.segment.sequence = before.current.core.receiveNext ∧
    packet.packet.segment.acknowledgment = before.current.core.sendUna ∧
    ∀ old ∈ before.steps, old.stamp < index

def DiscardAckFields (active : H.Local) (opened : O.Opened active) (packet : H.Input) : Prop :=
  Handshake.Profile packet 16 ∧ packet.packet.header = Handshake.inbound active opened.remote ∧
    packet.packet.segment.acknowledgment = active.iss.add 1

def ReceiveFields (state : State active passive) (receipt : Receipt) : Prop :=
  receipt.source.actor = receipt.source.kind.actor ∧
    match receipt.source.kind, state.phase with
    | .syn, .opened opened =>
      receipt.source.packet = opened.pending.output ∧ passive.Valid ∧
        Handshake.destination passive receipt.delivery.input ∧ Handshake.Profile receipt.delivery.input 2
    | .syn, .answered answered =>
      receipt.source.packet = answered.opened.pending.output ∧ SameDecoded receipt.delivery.input answered.delivery.input
    | .syn, .acknowledged acknowledged _ =>
      receipt.source.packet = acknowledged.answered.opened.pending.output ∧
        SameDecoded receipt.delivery.input acknowledged.answered.delivery.input
    | .syn, .complete complete _ _ =>
      receipt.source.packet = complete.certificate.activePending.output ∧
        SameDecoded receipt.delivery.input complete.certificate.syn.input
    | .synAck, .answered answered =>
      receipt.source.packet = answered.pending.output ∧ Handshake.ActiveAccepted answered.opened.pending receipt.delivery.input
    | .synAck, .acknowledged acknowledged _ =>
      receipt.source.packet = acknowledged.answered.pending.output ∧
        SameDecoded receipt.delivery.input acknowledged.delivery.input
    | .synAck, .complete complete _ _ =>
      receipt.source.packet = complete.certificate.passivePending.output ∧
        SameDecoded receipt.delivery.input complete.certificate.synAck.input
    | .finalAck, .acknowledged acknowledged _ =>
      receipt.source.packet = acknowledged.ready.output ∧
        Handshake.PassiveAccepted acknowledged.answered.pending receipt.delivery.input ∧
        acknowledged.answered.opened.index < acknowledged.answered.index ∧
        acknowledged.answered.index < acknowledged.index ∧ acknowledged.index < receipt.index
    | .finalAck, .complete _ _ server => EmptyAckFields server receipt.delivery.input receipt.index
    | .synReplyAck, .opened opened => DiscardAckFields active opened receipt.delivery.input
    | .synReplyAck, .answered answered => DiscardAckFields active answered.opened receipt.delivery.input
    | .synReplyAck, .acknowledged _ client => EmptyAckFields client receipt.delivery.input receipt.index
    | .synReplyAck, .complete _ client _ => EmptyAckFields client receipt.delivery.input receipt.index
    | _, _ => False

def receiveLevel (before : Nat) : Kind → Nat
  | .syn => max before 2
  | .synAck => max before 3
  | .finalAck => 4
  | .synReplyAck => before

def receiveResponse (phase : Phase active passive) : Kind → Option Kind
  | .syn => match phase with | .opened _ => some .synAck | _ => some .synReplyAck
  | .synAck => some .finalAck
  | .finalAck | .synReplyAck => none

def ResponseKind (expected : Option Kind) (actual : Option Emission) : Prop :=
  match expected with
  | none => actual = none
  | some kind => ∃ output, actual = some output ∧ output.actor = kind.actor ∧ output.kind = kind

end Netlib.Check.TCPHandshakeRecovery
