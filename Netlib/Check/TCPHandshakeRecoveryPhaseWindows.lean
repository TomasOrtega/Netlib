import Netlib.Check.TCPHandshakeRecoveryOutputShape
import Netlib.Protocol.TCP.EndpointEmptyAckFrame

/-!
# Peer windows before application data

Every generated control advertises its actor's fixed receive capacity.
Accepted empty ACKs can update window markers while retaining that capacity.
-/

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

def PhaseWindows (state : State active passive) : Prop :=
  match state.phase with
  | .idle | .opened _ | .answered _ => True
  | .acknowledged _ client => client.current.sendWindow = passive.capacity
  | .complete _ client server =>
    client.current.sendWindow = passive.capacity ∧ server.current.sendWindow = active.capacity

variable {active passive : H.Local}
variable {before after : State active passive} {output : Emission}

theorem PhaseWindows.initial : PhaseWindows (State.initial : State active passive) := trivial

theorem PhaseWindows.frame (prior : PhaseWindows before) (phase : after.phase = before.phase) : PhaseWindows after := by
  unfold PhaseWindows
  rw [phase]
  exact prior

theorem PhaseWindows.withTimer (prior : PhaseWindows before) (actor : Side)
    (timer : HandshakeTimer.State) (valid : timer.Valid) : PhaseWindows (before.withTimer actor timer valid) := by
  cases actor <;> exact prior

theorem PhaseWindows.publish (prior : PhaseWindows before) (output : Emission) :
    PhaseWindows (publish before output).state := prior

theorem PhaseWindows.retainReceipt (prior : PhaseWindows effect.state) (receipt : Receipt) :
    PhaseWindows (retainReceipt effect receipt).state := prior

theorem Receipt.input_window (receipt : Receipt) (shape : OutputShape active passive receipt.source) :
    receipt.delivery.input.packet.segment.window.val = receipt.source.kind.capacity active passive := by
  have window := congrArg (fun value : Protocol.InternetChecksum.Word => value.val) receipt.delivery.path.control_fields.2.2.1
  exact window.trans shape.capacity

theorem Acknowledged.peer_window (acknowledged : O.Acknowledged active passive) :
    acknowledged.ready.seed.sendWindow = passive.capacity := by
  have window := congrArg (fun value : Protocol.InternetChecksum.Word => value.val) acknowledged.delivery.path.control_fields.2.2.1
  exact acknowledged.ready.peer_fields.1.trans (window.trans (Answered.output_shape acknowledged.answered).capacity)

theorem Completed.peer_windows (complete : O.Completed active passive) :
    complete.certificate.activeSeed.sendWindow = passive.capacity ∧ complete.certificate.passiveSeed.sendWindow = active.capacity := by
  have windows := complete.certificate.peer_capacities
  rw [complete.activeConfig, complete.passiveConfig] at windows
  exact windows

theorem ReceivedAck.send_window {seed : Endpoint.State} {current : PreData seed}
    (applied : ReceivedAck current packet index) (clean : PreDataClean seed current)
    (old : current.current.sendWindow = window) (incoming : packet.packet.segment.window.val = window) :
    applied.after.current.sendWindow = window := by
  have fields := clean.fields
  have received := Endpoint.receive_empty_ack_initial current.current packet current.valid
    fields.1 fields.2.1 fields.2.2.1 applied.tuple applied.profile.1
    (by simpa only [Handshake.optionProfile, ite_true] using applied.profile.2.1)
    applied.profile.2.2 applied.coordinates.1 applied.coordinates.2
  have result := applied.operation.computed
  rw [applied.event, ApplicationTrace.evaluate, applied.beforeEq, received] at result
  rw [applied.state, result]
  change (Endpoint.windowState current.current current.current packet.packet.segment).sendWindow = window
  unfold Endpoint.windowState
  split
  · exact incoming
  · exact old

end Netlib.Check.TCPHandshakeRecovery
