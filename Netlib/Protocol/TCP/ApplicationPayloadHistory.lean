import Netlib.Protocol.TCP.ApplicationTrace

/-!
# Byte histories with empty control receives

Only accepted nonempty payload needs a peer application output.
Empty startup ACKs retain their separate actual control provenance.
-/

namespace Netlib.Protocol.TCP.ApplicationTrace

def PayloadDelivered (sender : List Step) (step : Step) : Prop :=
  step.acceptedPayload ≠ [] → Delivered sender step

structure PayloadDeliveryHistory (sender receiver : List Step) : Prop where
  senderOrder : Chronological sender
  receiverOrder : Chronological receiver
  delivered : ∀ step ∈ receiver, PayloadDelivered sender step

theorem DeliveryHistory.toPayload (history : DeliveryHistory sender receiver) : PayloadDeliveryHistory sender receiver :=
  ⟨history.senderOrder, history.receiverOrder, fun step member _ => history.delivered step member⟩

theorem ActualAllocation.accepted_payload_nonempty (actual : ActualAllocation operation) :
    operation.acceptedPayload ≠ [] := by
  have commit := Endpoint.receiveEffect_stored operation.before actual.input actual.store.result actual.committed
  obtain ⟨_, _, nonempty, _⟩ := ReceiveReassembly.prepare_data _ _ _ _ _ _ commit.prepared
  obtain ⟨count, accepted⟩ := actual.accepted
  have payload : operation.acceptedPayload = actual.input.packet.segment.payload := by
    simp only [Step.acceptedPayload, ApplicationTrace.acceptedPayload, actual.event, accepted]
  intro empty
  rw [← payload, empty] at nonempty
  cases nonempty

private theorem payload_released_prefix_aux (sourceChain : Chain sourceInitial sourceSteps sourceFinal)
    (emptySent : sourceInitial.core.sent = [])
    (epoch : (sourceSteps.flatMap Step.emitted).length < Seq.halfSpace)
    (base : Nat) (targetChain : Chain targetInitial targetSteps targetFinal) :
    ∀ accumulated : List UInt8,
      accumulated <+: sourceSteps.flatMap Step.emitted →
      targetInitial.core.receiveNext = sourceInitial.core.sendNext.add accumulated.length →
      targetInitial.receiveStore.frontier = base + accumulated.length →
      (∀ run ∈ targetInitial.receiveStore.held, H.StreamRange base (sourceSteps.flatMap Step.emitted) run) →
      (∀ operation ∈ targetSteps, PayloadDelivered sourceSteps operation) →
      accumulated ++ targetSteps.flatMap Step.releasedPayload <+: sourceSteps.flatMap Step.emitted := by
  induction targetChain with
  | nil state => intro accumulated prior _ _ _ _; simpa using prior
  | cons head tail ih =>
    intro accumulated prior cursor frontier held delivered
    cases transition : head.storeTransition with
    | stutter same empty =>
      have nextCursor : head.result.state.core.receiveNext = sourceInitial.core.sendNext.add accumulated.length := by
        rw [head.receiveNext_balance, empty, List.length_nil, Seq.add_zero]
        exact cursor
      have nextFrontier : head.result.state.receiveStore.frontier = base + accumulated.length := by
        rw [same]
        exact frontier
      have nextHeld : ∀ run ∈ head.result.state.receiveStore.held, H.StreamRange base (sourceSteps.flatMap Step.emitted) run := by
        rw [same]
        exact held
      have rest := ih accumulated prior nextCursor nextFrontier nextHeld
        (fun operation member => delivered operation (by simp [member]))
      simpa only [List.flatMap_cons, empty, List.nil_append] using rest
    | accepted allocation =>
      have incoming := allocation.streamRange sourceChain emptySent epoch base accumulated prior cursor frontier
        (delivered head (by simp) allocation.accepted_payload_nonempty)
      have added := allocation.store.prefix_step base (sourceSteps.flatMap Step.emitted) accumulated
        (by rw [allocation.before]; exact frontier) prior
        (by rw [allocation.before]; exact held) incoming
      have nextPrefix : accumulated ++ head.releasedPayload <+: sourceSteps.flatMap Step.emitted := by
        simpa only [allocation.released] using added.1
      have nextCursor : head.result.state.core.receiveNext =
          sourceInitial.core.sendNext.add (accumulated ++ head.releasedPayload).length := by
        rw [head.receiveNext_balance, cursor, Seq.add_add, List.length_append]
      have nextFrontier : head.result.state.receiveStore.frontier = base + (accumulated ++ head.releasedPayload).length := by
        rw [← allocation.after, allocation.store.frontier, allocation.before, allocation.released, frontier, List.length_append]
        omega
      have nextHeld : ∀ run ∈ head.result.state.receiveStore.held, H.StreamRange base (sourceSteps.flatMap Step.emitted) run := by
        rw [← allocation.after]
        exact added.2
      have rest := ih (accumulated ++ head.releasedPayload) nextPrefix nextCursor nextFrontier nextHeld
        (fun operation member => delivered operation (by simp [member]))
      simpa only [List.flatMap_cons, List.append_assoc] using rest

theorem payload_released_prefix_emitted (sourceChain : Chain sourceInitial sourceSteps sourceFinal)
    (emptySent : sourceInitial.core.sent = [])
    (targetChain : Chain targetInitial targetSteps targetFinal)
    (history : PayloadDeliveryHistory sourceSteps targetSteps)
    (emptyHeld : targetInitial.receiveStore.held = [])
    (cursors : targetInitial.core.receiveNext = sourceInitial.core.sendNext)
    (epoch : (sourceSteps.flatMap Step.emitted).length < Seq.halfSpace) :
    targetSteps.flatMap Step.releasedPayload <+: sourceSteps.flatMap Step.emitted := by
  have result := payload_released_prefix_aux sourceChain emptySent epoch targetInitial.receiveStore.frontier targetChain []
    (by simp) (by simpa only [List.length_nil, Seq.add_zero] using cursors) (by simp)
    (by intro run member; simp only [emptyHeld, List.not_mem_nil] at member) history.delivered
  simpa only [List.nil_append] using result

theorem payload_application_prefix (sourceChain : Chain sourceInitial sourceSteps sourceFinal)
    (targetChain : Chain targetInitial targetSteps targetFinal)
    (history : PayloadDeliveryHistory sourceSteps targetSteps)
    (emptyPending : sourceInitial.pending = [])
    (emptySent : sourceInitial.core.sent = [])
    (emptyReceived : targetInitial.core.received = [])
    (emptyHeld : targetInitial.receiveStore.held = [])
    (cursors : targetInitial.core.receiveNext = sourceInitial.core.sendNext)
    (epoch : (sourceSteps.flatMap Step.emitted).length < Seq.halfSpace) :
    targetSteps.flatMap Step.readBytes <+: sourceSteps.flatMap Step.written := by
  exact (targetChain.read_prefix_received emptyReceived).trans
    ((payload_released_prefix_emitted sourceChain emptySent targetChain history emptyHeld cursors epoch).trans
      (sourceChain.emitted_prefix_written emptyPending))


theorem received_original_payload_byte_origin (sourceChain : Chain sourceInitial sourceSteps sourceFinal)
    (history : PayloadDeliveryHistory sourceSteps targetSteps) (empty : sourceInitial.pending = [])
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
  obtain ⟨source, earlier, path⟩ := history.delivered step member nonempty input event
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

theorem payload_paired_application_prefix
    (leftChain : Chain leftInitial leftSteps leftFinal)
    (rightChain : Chain rightInitial rightSteps rightFinal)
    (leftToRight : PayloadDeliveryHistory leftSteps rightSteps)
    (rightToLeft : PayloadDeliveryHistory rightSteps leftSteps)
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
  exact ⟨payload_application_prefix leftChain rightChain leftToRight leftPending leftSent rightReceived rightHeld rightCursor leftEpoch,
    payload_application_prefix rightChain leftChain rightToLeft rightPending rightSent leftReceived leftHeld leftCursor rightEpoch⟩

end Netlib.Protocol.TCP.ApplicationTrace
