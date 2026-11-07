import Netlib.Protocol.TCP.ApplicationPayloadHistory
import Netlib.Protocol.TCP.ApplicationTraceFacts

/-!
# Payload byte origins through actual attempts

The byte joins include retries and the actual ordered release and read.
-/

namespace Netlib.Protocol.TCP.ApplicationTrace

theorem received_payload_byte_origin (sourceChain : Chain sourceInitial sourceSteps sourceFinal)
    (history : PayloadDeliveryHistory sourceSteps targetSteps) (emptySent : sourceInitial.core.sent = [])
    (emptyPending : sourceInitial.pending = []) (step : Step) (member : step ∈ targetSteps)
    (index : Nat) (byte : UInt8) (selected : step.acceptedPayload[index]? = some byte) :
    ∃ input count size, step.event = .receive input ∧
      step.result.decision = .accepted (.receive count size) ∧
      ∃ attempt : OutputAt sourceSteps, BytePath attempt.output input ∧ attempt.step.stamp < step.stamp ∧
        Nonempty (AttemptByteOrigin sourceInitial sourceSteps attempt index byte) := by
  have nonempty : step.acceptedPayload ≠ [] := by intro empty; simp [empty] at selected
  obtain ⟨input, count, size, event, accepted, payload⟩ := step.data nonempty
  obtain ⟨attempt, earlier, path⟩ := history.delivered step member nonempty input event
  have sourceByte : attempt.output.packet.segment.payload[index]? = some byte := by
    rw [payload, path.fields.1] at selected
    exact selected
  exact ⟨input, count, size, event, accepted, attempt, path, earlier,
    attempt.byte_origin sourceChain emptySent emptyPending history.senderOrder index byte sourceByte⟩

theorem RunReceiptOrigin.payload_attempt_origin (value : RunReceiptOrigin targetSteps run)
    (sourceChain : Chain sourceInitial sourceSteps sourceFinal) (history : PayloadDeliveryHistory sourceSteps targetSteps)
    (emptySent : sourceInitial.core.sent = []) (emptyPending : sourceInitial.pending = [])
    (index : Nat) (byte : UInt8) (selected : run.bytes[index]? = some byte) :
    ∃ attempt : OutputAt sourceSteps,
      BytePath attempt.output value.allocation.input ∧ attempt.step.stamp < value.issuer.stamp ∧
      Nonempty (AttemptByteOrigin sourceInitial sourceSteps attempt index byte) := by
  obtain ⟨attempt, earlier, path⟩ := history.delivered value.issuer value.member value.allocation.accepted_payload_nonempty
    value.allocation.input value.allocation.event
  have sourceByte : attempt.output.packet.segment.payload[index]? = some byte := by
    rw [value.fields.1, path.fields.1] at selected
    exact selected
  exact ⟨attempt, path, earlier,
    attempt.byte_origin sourceChain emptySent emptyPending history.senderOrder index byte sourceByte⟩

theorem ActualReleasedByteOrigin.payload_attempt_origin (value : ActualReleasedByteOrigin targetSteps release index byte)
    (sourceChain : Chain sourceInitial sourceSteps sourceFinal) (history : PayloadDeliveryHistory sourceSteps targetSteps)
    (emptySent : sourceInitial.core.sent = []) (emptyPending : sourceInitial.pending = []) :
    ∃ attempt : OutputAt sourceSteps,
      BytePath attempt.output value.origin.allocation.input ∧ attempt.step.stamp < value.origin.issuer.stamp ∧
      Nonempty (AttemptByteOrigin sourceInitial sourceSteps attempt value.localIndex byte) := by
  obtain ⟨attempt, earlier, path⟩ := history.delivered value.origin.issuer value.origin.issuer_member value.origin.allocation.accepted_payload_nonempty
    value.origin.allocation.input value.origin.allocation.event
  have sourceByte : attempt.output.packet.segment.payload[value.localIndex]? = some byte := by
    rw [← path.fields.1]
    exact value.input_byte
  exact ⟨attempt, path, earlier,
    attempt.byte_origin sourceChain emptySent emptyPending history.senderOrder value.localIndex byte sourceByte⟩

theorem ReadReleasedByteOrigin.payload_attempt_origin (value : ReadReleasedByteOrigin targetSteps reader index byte)
    (sourceChain : Chain sourceInitial sourceSteps sourceFinal) (history : PayloadDeliveryHistory sourceSteps targetSteps)
    (emptySent : sourceInitial.core.sent = []) (emptyPending : sourceInitial.pending = []) :
    ∃ attempt : OutputAt sourceSteps,
      BytePath attempt.output value.origin.origin.allocation.input ∧
      attempt.step.stamp < value.origin.origin.issuer.stamp ∧
      value.origin.origin.issuer.stamp ≤ value.release.stamp ∧ value.release.stamp < reader.stamp ∧
      Nonempty (AttemptByteOrigin sourceInitial sourceSteps attempt value.origin.localIndex byte) := by
  obtain ⟨attempt, path, earlier, provenance⟩ := value.origin.payload_attempt_origin sourceChain history emptySent emptyPending
  exact ⟨attempt, path, earlier, value.origin.origin.no_later history.receiverOrder, value.earlier, provenance⟩

end Netlib.Protocol.TCP.ApplicationTrace
