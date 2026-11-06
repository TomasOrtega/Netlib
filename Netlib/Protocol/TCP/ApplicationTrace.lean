import Netlib.Protocol.TCP.ApplicationTraceCore
import Netlib.Protocol.TCP.ApplicationReceiveHistory

namespace Netlib.Protocol.TCP.ApplicationTrace

theorem application_prefix (sourceChain : Chain sourceInitial sourceSteps sourceFinal)
    (targetChain : Chain targetInitial targetSteps targetFinal)
    (history : DeliveryHistory sourceSteps targetSteps)
    (emptyPending : sourceInitial.pending = [])
    (emptySent : sourceInitial.core.sent = [])
    (emptyReceived : targetInitial.core.received = [])
    (emptyHeld : targetInitial.receiveStore.held = [])
    (cursors : targetInitial.core.receiveNext = sourceInitial.core.sendNext)
    (epoch : (sourceSteps.flatMap Step.emitted).length < Seq.halfSpace) :
    targetSteps.flatMap Step.readBytes <+: sourceSteps.flatMap Step.written := by
  exact (targetChain.read_prefix_received emptyReceived).trans
    ((released_prefix_emitted sourceChain emptySent targetChain history emptyHeld cursors epoch).trans
      (sourceChain.emitted_prefix_written emptyPending))


theorem OutputOrigin.pending_prefix (origin : OutputOrigin step output) (original : NoRetry step) :
    output.packet.segment.payload <+: step.before.pending := by
  rw [(origin.fields original).1]
  cases origin with
  | send count policy event accepted actual =>
    simpa only [Step.emitted, event, accepted, emitted] using List.take_prefix count step.before.pending
  | ack policy event accepted actual =>
    simp only [Step.emitted, event, emitted, List.nil_prefix]
  | dispatchAck policy event accepted actual =>
    simp only [Step.emitted, event, emitted, List.nil_prefix]
  | retry count policy event accepted actual => exact False.elim (original policy event)

theorem OutputOrigin.nonempty_send (origin : OutputOrigin step output) (original : NoRetry step)
    (nonempty : output.packet.segment.payload ≠ []) :
    ∃ count policy, step.event = .send count policy ∧ step.result.decision = .accepted (.send count) := by
  cases origin with
  | send count policy event accepted actual => exact ⟨count, policy, event, accepted⟩
  | ack policy event accepted actual =>
    have payload := ((OutputOrigin.ack policy event accepted actual).fields original).1
    simp only [Step.emitted, event, emitted] at payload
    exact False.elim (nonempty payload)
  | dispatchAck policy event accepted actual =>
    have payload := ((OutputOrigin.dispatchAck policy event accepted actual).fields original).1
    simp only [Step.emitted, event, emitted] at payload
    exact False.elim (nonempty payload)
  | retry count policy event accepted actual => exact False.elim (original policy event)

theorem OutputAt.written_prefix (value : OutputAt steps) (chain : Chain initial steps final)
    (empty : initial.pending = []) (original : NoRetry value.step) :
    value.prior.flatMap Step.emitted ++ value.output.packet.segment.payload <+: value.prior.flatMap Step.written := by
  have split := chain
  rw [value.same] at split
  have balance := split.cut.1.pending
  simp only [empty, List.nil_append] at balance
  obtain ⟨remaining, same⟩ := value.origin.pending_prefix original
  exact ⟨remaining, by rw [List.append_assoc, same, ← balance]⟩

theorem OutputAt.prior_before (value : OutputAt steps) (order : Chronological steps)
    (writer : Step) (member : writer ∈ value.prior) : writer.stamp < value.step.stamp := by
  have ordered := order
  unfold Chronological at ordered
  rw [value.same] at ordered
  exact (List.pairwise_append.mp ordered).2.2 writer member value.step (by simp)

theorem OutputAt.byte_write (value : OutputAt steps) (chain : Chain initial steps final)
    (empty : initial.pending = []) (order : Chronological steps) (original : NoRetry value.step)
    (byte : UInt8) (member : byte ∈ value.output.packet.segment.payload) :
    ∃ writer ∈ value.prior, writer.stamp < value.step.stamp ∧ byte ∈ writer.written := by
  have priorMember : byte ∈ value.prior.flatMap Step.written :=
    (value.written_prefix chain empty original).subset (List.mem_append_right _ member)
  obtain ⟨writer, before, present⟩ := List.mem_flatMap.mp priorMember
  exact ⟨writer, before, value.prior_before order writer before, present⟩

theorem Step.written_event (step : Step) (byte : UInt8) (member : byte ∈ step.written) :
    ∃ bytes count, step.event = .write bytes ∧
      step.result.decision = .accepted (.write count) ∧ byte ∈ bytes := by
  cases event : step.event with
  | send count policy => simp [Step.written, ApplicationTrace.written, event] at member
  | read count => simp [Step.written, ApplicationTrace.written, event] at member
  | emitAck policy => simp [Step.written, ApplicationTrace.written, event] at member
  | receive input => simp [Step.written, ApplicationTrace.written, event] at member
  | enableRecovery | advanceClock _ | timeout _ | enableAck | dispatchAck _ => simp [Step.written, ApplicationTrace.written, event] at member
  | write bytes =>
    cases selected : step.result.decision with
    | reject reason => simp [Step.written, ApplicationTrace.written, event, selected] at member
    | unsupported reason | recoveryUnsupported reason | ackUnsupported reason => simp [Step.written, ApplicationTrace.written, event, selected] at member
    | accepted action =>
      cases action with
      | write count =>
        exact ⟨bytes, count, rfl, rfl, by
          simpa only [Step.written, ApplicationTrace.written, event, selected] using member⟩
      | send count => simp [Step.written, ApplicationTrace.written, event, selected] at member
      | read count => simp [Step.written, ApplicationTrace.written, event, selected] at member
      | emitAck | enableRecovery | advanceClock | retry _ | enableAck | dispatchAck => simp [Step.written, ApplicationTrace.written, event, selected] at member
      | receive count size => simp [Step.written, ApplicationTrace.written, event, selected] at member

theorem received_original_byte_origin (sourceChain : Chain sourceInitial sourceSteps sourceFinal)
    (history : DeliveryHistory sourceSteps targetSteps) (empty : sourceInitial.pending = [])
    (originals : ∀ source : OutputAt sourceSteps, NoRetry source.step)
    (step : Step) (member : step ∈ targetSteps)
    (byte : UInt8) (present : byte ∈ step.acceptedPayload) :
    ∃ input count size, step.event = .receive input ∧
      step.result.decision = .accepted (.receive count size) ∧
      ∃ source : OutputAt sourceSteps,
        BytePath source.output input ∧ source.step.stamp < step.stamp ∧
        (∃ sent policy, source.step.event = .send sent policy ∧
          source.step.result.decision = .accepted (.send sent)) ∧
        ∃ writer ∈ source.prior,
          writer.stamp < source.step.stamp ∧
          ∃ bytes writtenCount, writer.event = .write bytes ∧
            writer.result.decision = .accepted (.write writtenCount) ∧ byte ∈ bytes := by
  have nonempty : step.acceptedPayload ≠ [] := by intro empty; simp [empty] at present
  obtain ⟨input, count, size, event, accepted, payload⟩ := step.data nonempty
  obtain ⟨source, earlier, path⟩ := history.delivered step member input event
  have sourceMember : byte ∈ source.output.packet.segment.payload := by
    rw [payload, path.fields.1] at present
    exact present
  have sourceNonempty : source.output.packet.segment.payload ≠ [] := by
    intro empty
    simp [empty] at sourceMember
  obtain ⟨writer, prior, before, writtenMember⟩ :=
    source.byte_write sourceChain empty history.senderOrder (originals source) byte sourceMember
  exact ⟨input, count, size, event, accepted, source, path, earlier,
    source.origin.nonempty_send (originals source) sourceNonempty, writer, prior, before,
    writer.written_event byte writtenMember⟩

theorem paired_application_prefix
    (leftChain : Chain leftInitial leftSteps leftFinal)
    (rightChain : Chain rightInitial rightSteps rightFinal)
    (leftToRight : DeliveryHistory leftSteps rightSteps)
    (rightToLeft : DeliveryHistory rightSteps leftSteps)
    (leftPending : leftInitial.pending = []) (rightPending : rightInitial.pending = [])
    (leftSent : leftInitial.core.sent = []) (rightSent : rightInitial.core.sent = [])
    (leftReceived : leftInitial.core.received = []) (rightReceived : rightInitial.core.received = [])
    (leftHeld : leftInitial.receiveStore.held = []) (rightHeld : rightInitial.receiveStore.held = [])
    (leftCursor : leftInitial.core.receiveNext = rightInitial.core.sendNext)
    (rightCursor : rightInitial.core.receiveNext = leftInitial.core.sendNext)
    (leftEpoch : (leftSteps.flatMap Step.emitted).length < Seq.halfSpace)
    (rightEpoch : (rightSteps.flatMap Step.emitted).length < Seq.halfSpace) :
    rightSteps.flatMap Step.readBytes <+: leftSteps.flatMap Step.written ∧
      leftSteps.flatMap Step.readBytes <+: rightSteps.flatMap Step.written := by
  exact ⟨application_prefix leftChain rightChain leftToRight leftPending leftSent rightReceived rightHeld rightCursor leftEpoch,
    application_prefix rightChain leftChain rightToLeft rightPending rightSent leftReceived leftHeld leftCursor rightEpoch⟩

end Netlib.Protocol.TCP.ApplicationTrace
