import Netlib.Check.TCPHandshakeRecoveryInvariantCore
import Netlib.Protocol.TCP.EndpointEmptyAckFrame

/-!
# Empty ACK receives from current pre-data fields

The actual local operation retains any window-marker changes.
-/

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

variable {seed : Endpoint.State}

theorem PreData.receiveAck_enabled (before : PreData seed) (clean : PreDataClean seed before)
    (packet : H.Input) (index : Nat) (profile : Handshake.Profile packet 16)
    (tuple : packet.packet.header = before.current.core.inbound)
    (coordinates : packet.packet.segment.sequence = before.current.core.receiveNext ∧
      packet.packet.segment.acknowledgment = before.current.core.sendUna)
    (earlier : ∀ old ∈ before.steps, old.stamp < index) :
    ∃ received : ReceivedAck before packet index,
      before.receiveAck packet index = .ok received ∧
      received.operation.result =
        ⟨Endpoint.windowState before.current before.current packet.packet.segment,
          .accepted (.receive 0 0), none, [], none⟩ ∧
      received.after.current = Endpoint.windowState before.current before.current packet.packet.segment ∧
      received.after.steps = before.steps ++ [received.operation] ∧
      PreDataClean seed received.after := by
  have fields := clean.fields
  have options : packet.packet.segment.options = [] := by
    simpa only [Handshake.optionProfile, ↓reduceIte] using profile.2.1
  have endpoint := Endpoint.receive_empty_ack_initial before.current packet before.valid
    fields.1 fields.2.1 fields.2.2.1 tuple profile.1 options profile.2.2 coordinates.1 coordinates.2
  let operation := ApplicationTrace.Step.make before.current before.valid (.receive packet) index
  have result : operation.result =
      ⟨Endpoint.windowState before.current before.current packet.packet.segment,
        .accepted (.receive 0 0), none, [], none⟩ := endpoint
  have accepted : operation.result.decision = .accepted (.receive 0 0) := by rw [result]
  have quiet : operation.result.output = none := by rw [result]
  have read : operation.result.read = [] := by rw [result]
  dsimp only [operation] at accepted quiet read
  have enabled : ∃ received : ReceivedAck before packet index, before.receiveAck packet index = .ok received := by
    unfold PreData.receiveAck
    rw [dite_eq_left profile, dite_eq_left tuple, dite_eq_left coordinates, dite_eq_left earlier]
    rw [dite_eq_left accepted, dite_eq_left quiet, dite_eq_left read]
    exact ⟨_, rfl⟩
  obtain ⟨received, computed⟩ := enabled
  have actualResult : received.operation.result =
      ⟨Endpoint.windowState before.current before.current packet.packet.segment,
        .accepted (.receive 0 0), none, [], none⟩ := by
    rw [received.operation.computed, received.beforeEq, received.event]
    exact endpoint
  have state : received.after.current = Endpoint.windowState before.current before.current packet.packet.segment := by
    rw [received.state, actualResult]
  have frame : WindowFrame before.current received.after.current := by
    rw [state]
    exact WindowFrame.windowState before.current packet.packet.segment
  exact ⟨received, computed, actualResult, state, received.history, clean.1.trans frame, clean.2⟩

end Netlib.Check.TCPHandshakeRecovery
