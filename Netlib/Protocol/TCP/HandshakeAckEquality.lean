import Netlib.Protocol.TCP.HandshakeDuplicate

/-!
# Exact equality of empty startup ACK outputs

The control and endpoint constructors use the same bytes for equal cursors.
The receive-window markers do not enter either packet constructor.
-/

namespace Netlib.Protocol.TCP.HandshakeDuplicate

private theorem input_eq (first second : Handshake.Input) (same : first.bytes = second.bytes) : first = second := by
  cases first with
  | mk bytes packet checked =>
    cases second with
    | mk other decoded verified =>
      dsimp only at same
      subst other
      have equal := Except.ok.inj (checked.symm.trans verified)
      subst decoded
      rfl

theorem BareAck.empty_output (state : EstablishedReceive.State)
    (ack : BareAck (Output.reverse state.inbound) state.sendNext state.receiveNext state.window ipLimit)
    (output : Handshake.Input) (generated : Output.emit state [] = .ok output) : ack.output = output := by
  apply input_eq
  rw [(ControlOutput.emit_fields _ _ _ _ _ _ ack.generated).2.2.2.1,
    (Output.emit_fields _ _ _ generated).2.2.1]
  rfl

theorem BareAck.same_output
    (first : BareAck header sendNext receiveNext window firstLimit)
    (second : BareAck header sendNext receiveNext window secondLimit) : first.output = second.output := by
  have generated := first.generated.symm.trans second.generated
  exact Except.ok.inj generated

end Netlib.Protocol.TCP.HandshakeDuplicate
