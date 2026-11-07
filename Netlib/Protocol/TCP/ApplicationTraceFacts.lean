import Netlib.Protocol.TCP.ApplicationTrace

namespace Netlib.Protocol.TCP.ApplicationTrace

theorem Chain.append (first : Chain initial prior middle) (second : Chain middle later final) :
    Chain initial (prior ++ later) final := by
  induction first with
  | nil state => exact second
  | cons head tail ih => exact .cons head (ih second)

theorem Chain.snoc (prior : Chain initial steps head.before) :
    Chain initial (steps ++ [head]) head.result.state :=
  prior.append (.cons head (.nil head.result.state))

theorem chronological_snoc (ordered : Chronological steps)
    (earlier : ∀ step ∈ steps, step.stamp < head.stamp) : Chronological (steps ++ [head]) := by
  apply List.pairwise_append.mpr
  refine ⟨ordered, .cons (by intro item member; cases member) .nil, ?_⟩
  intro item member last present
  simp only [List.mem_singleton] at present
  subst last
  exact earlier item member


def stepOutput (step : Step) : Except String { output : Input // OutputOrigin step output } :=
  match event : step.event with
  | .send count policy =>
    match selected : step.result.decision with
    | .accepted (.send amount) =>
      if same : amount = count then
        match actual : step.result.output with
        | some output => .ok ⟨output, .send count policy event (by simpa only [same] using selected) actual⟩
        | none => .error "The selected send has no checked output."
      else .error "The selected send count differs from its event."
    | _ => .error "The selected send did not succeed."
  | .timeout policy =>
    match selected : step.result.decision with
    | .accepted (.retry count) =>
      match actual : step.result.output with
      | some output => .ok ⟨output, .retry count policy event selected actual⟩
      | none => .error "The selected retry has no checked output."
    | _ => .error "The selected timeout did not emit a retry."
  | .emitAck policy =>
    match selected : step.result.decision with
    | .accepted .emitAck =>
      match actual : step.result.output with
      | some output => .ok ⟨output, .ack policy event selected actual⟩
      | none => .error "The selected ACK event has no checked output."
    | _ => .error "The selected ACK event did not succeed."
  | .dispatchAck policy =>
    match selected : step.result.decision with
    | .accepted .dispatchAck =>
      match actual : step.result.output with
      | some output => .ok ⟨output, .dispatchAck policy event selected actual⟩
      | none => .error "The selected ACK dispatch has no checked output."
    | _ => .error "The selected ACK dispatch did not succeed."
  | _ => .error "The selected event cannot produce application-profile output."

def findOutput : (steps : List Step) → (stamp : Nat) →
    Except String { value : OutputAt steps // value.step.stamp = stamp }
  | [], _ => .error "The selected output event is absent from this application trace."
  | head :: tail, stamp => do
    if same : head.stamp = stamp then
      let output ← stepOutput head
      return ⟨⟨[], head, tail, rfl, output.val, output.property⟩, same⟩
    else
      let found ← findOutput tail stamp
      let value : OutputAt (head :: tail) :=
        ⟨head :: found.val.prior, found.val.step, found.val.later,
          congrArg (head :: ·) found.val.same, found.val.output, found.val.origin⟩
      return ⟨value, found.property⟩

theorem flatMap_location {α β : Type} (bytes : α → List β) (steps : List α) (index : Nat) (byte : β)
    (selected : (steps.flatMap bytes)[index]? = some byte) :
    ∃ prior step later localIndex, steps = prior ++ step :: later ∧
      index = (prior.flatMap bytes).length + localIndex ∧
      (bytes step)[localIndex]? = some byte := by
  induction steps generalizing index with
  | nil => simp at selected
  | cons head tail ih =>
    have found : (bytes head ++ tail.flatMap bytes)[index]? = some byte := selected
    by_cases inside : index < (bytes head).length
    · rw [List.getElem?_append_left inside] at found
      exact ⟨[], head, tail, index, rfl, by simp, found⟩
    · have outside : (bytes head).length ≤ index := by omega
      rw [List.getElem?_append_right outside] at found
      obtain ⟨prior, step, later, localIndex, same, position, present⟩ := ih _ found
      refine ⟨head :: prior, step, later, localIndex, by simp [same], ?_, present⟩
      simp only [List.flatMap_cons, List.length_append]
      omega

theorem Step.emitted_index (step : Step) (index : Nat) (byte : UInt8)
    (selected : step.emitted[index]? = some byte) :
    ∃ count policy amount, step.event = .send count policy ∧
      step.result.decision = .accepted (.send amount) ∧
      index < count ∧ step.before.pending[index]? = some byte := by
  cases event : step.event with
  | write bytes | read bytes | emitAck bytes | receive bytes | advanceClock bytes | timeout bytes | dispatchAck bytes =>
    simp [Step.emitted, ApplicationTrace.emitted, event] at selected
  | enableRecovery | enableAck | enableStartupRecovery _ =>
    simp [Step.emitted, ApplicationTrace.emitted, event] at selected
  | send count policy =>
    cases decision : step.result.decision with
    | reject reason | unsupported reason | recoveryUnsupported reason | ackUnsupported reason =>
      simp [Step.emitted, ApplicationTrace.emitted, event, decision] at selected
    | accepted action =>
      cases action with
      | write amount | read amount | retry amount => simp [Step.emitted, ApplicationTrace.emitted, event, decision] at selected
      | emitAck | enableRecovery | advanceClock | enableAck | dispatchAck => simp [Step.emitted, ApplicationTrace.emitted, event, decision] at selected
      | receive count size => simp [Step.emitted, ApplicationTrace.emitted, event, decision] at selected
      | send amount =>
        have present : (step.before.pending.take count)[index]? = some byte := by
          simpa only [Step.emitted, ApplicationTrace.emitted, event, decision] using selected
        have bound := (List.getElem?_eq_some_iff.mp present).1
        have inside : index < count := by simp only [List.length_take] at bound; omega
        rw [List.getElem?_take_of_lt inside] at present
        exact ⟨count, policy, amount, rfl, rfl, inside, present⟩

theorem Step.send_amount (step : Step) (count : Nat) (policy : Bool) (amount : Nat)
    (event : step.event = .send count policy)
    (accepted : step.result.decision = .accepted (.send amount)) : amount = count := by
  have selected : (Endpoint.send step.before count policy).decision = .accepted (.send amount) := by
    simpa only [step.computed, event, evaluate] using accepted
  by_cases valid : step.before.Valid
  · cases policy with
    | false => simp [Endpoint.send, valid, Endpoint.rejected] at selected
    | true =>
      by_cases ready : Endpoint.SendReady step.before count
      · cases prepared : Endpoint.ackReady step.before with
        | error reason =>
          simp only [Endpoint.send, valid, not_true_eq_false, ite_false, Bool.not_true, Bool.false_eq_true,
            ready, prepared, Endpoint.ackBlocked] at selected
          split at selected <;> cases selected
        | ok answer =>
          cases answer
          cases encoded : Endpoint.emit step.before (step.before.pending.take count) with
          | error reason => simp [Endpoint.send, valid, ready, prepared, encoded, Endpoint.rejected] at selected
          | ok output =>
            simp only [Endpoint.send, valid, not_true_eq_false, ite_false, Bool.not_true, Bool.false_eq_true,
              ready, prepared, encoded, Endpoint.Decision.accepted.injEq, Endpoint.Accepted.send.injEq] at selected
            exact selected.symm
      · simp only [Endpoint.send, valid, not_true_eq_false, ite_false, Bool.not_true, Bool.false_eq_true,
          ready, not_false_eq_true, ite_true] at selected
        split at selected
        · simp [Endpoint.recoveryBlocked, Recovery.Stop.unsupported] at selected
        · cases selected
  · simp [Endpoint.send, valid, Endpoint.rejected] at selected

theorem Step.written_index (step : Step) (index : Nat) (byte : UInt8)
    (selected : step.written[index]? = some byte) :
    ∃ bytes amount, step.event = .write bytes ∧
      step.result.decision = .accepted (.write amount) ∧ bytes[index]? = some byte := by
  cases event : step.event with
  | send count policy => simp [Step.written, ApplicationTrace.written, event] at selected
  | read count => simp [Step.written, ApplicationTrace.written, event] at selected
  | emitAck policy => simp [Step.written, ApplicationTrace.written, event] at selected
  | receive input => simp [Step.written, ApplicationTrace.written, event] at selected
  | enableRecovery | advanceClock _ | timeout _ | enableAck | dispatchAck _ | enableStartupRecovery _ =>
    simp [Step.written, ApplicationTrace.written, event] at selected
  | write bytes =>
    cases decision : step.result.decision with
    | reject reason | unsupported reason | recoveryUnsupported reason | ackUnsupported reason =>
      simp [Step.written, ApplicationTrace.written, event, decision] at selected
    | accepted action =>
      cases action with
      | write amount =>
        exact ⟨bytes, amount, rfl, rfl, by simpa only [Step.written, ApplicationTrace.written, event, decision] using selected⟩
      | send count | read count | retry count => simp [Step.written, ApplicationTrace.written, event, decision] at selected
      | emitAck | enableRecovery | advanceClock | enableAck | dispatchAck => simp [Step.written, ApplicationTrace.written, event, decision] at selected
      | receive count size => simp [Step.written, ApplicationTrace.written, event, decision] at selected


structure AttemptByteOrigin (initial : Model) (steps : List Step) (attempt : OutputAt steps) (index : Nat) (byte : UInt8) where
  prefixBytes : List UInt8
  rangePrefix : prefixBytes ++ attempt.output.packet.segment.payload <+: (attempt.prior ++ [attempt.step]).flatMap Step.emitted
  sequence : attempt.output.packet.segment.sequence = initial.core.sendNext.add prefixBytes.length
  original : OutputAt steps
  originalIndex : Nat
  count : Nat
  policy : Bool
  originalEvent : original.step.event = .send count policy
  originalAccepted : original.step.result.decision = .accepted (.send count)
  originalByte : original.output.packet.segment.payload[originalIndex]? = some byte
  originalPosition : prefixBytes.length + index = (original.prior.flatMap Step.emitted).length + originalIndex
  noLater : original.step.stamp ≤ attempt.step.stamp
  retryEarlier : ∀ policy, attempt.step.event = .timeout policy → original.step.stamp < attempt.step.stamp
  writerPrior : List Step
  writer : Step
  writerLater : List Step
  writerSplit : original.prior = writerPrior ++ writer :: writerLater
  bytes : List UInt8
  writtenCount : Nat
  writerIndex : Nat
  writerEvent : writer.event = .write bytes
  writerAccepted : writer.result.decision = .accepted (.write writtenCount)
  writerByte : bytes[writerIndex]? = some byte
  writerPosition : (original.prior.flatMap Step.emitted).length + originalIndex =
    (writerPrior.flatMap Step.written).length + writerIndex
  writerEarlier : writer.stamp < original.step.stamp

private theorem prefix_payload_index {α : Type} (prior payload all : List α) (ranged : prior ++ payload <+: all)
    (index : Nat) (byte : α) (selected : payload[index]? = some byte) : all[prior.length + index]? = some byte := by
  obtain ⟨rest, same⟩ := ranged
  have inside := (List.getElem?_eq_some_iff.mp selected).1
  have total : prior.length + index < (prior ++ payload).length := by simp only [List.length_append]; omega
  have after : prior.length ≤ prior.length + index := by omega
  rw [← same, List.getElem?_append_left total, List.getElem?_append_right after]
  simpa only [Nat.add_sub_cancel_left] using selected

theorem OutputAt.byte_origin (attempt : OutputAt steps) (chain : Chain initial steps final)
    (emptySent : initial.core.sent = []) (emptyPending : initial.pending = []) (order : Chronological steps)
    (index : Nat) (byte : UInt8) (selected : attempt.output.packet.segment.payload[index]? = some byte) :
    Nonempty (AttemptByteOrigin initial steps attempt index byte) := by
  obtain ⟨prefixBytes, rangePrefix, coordinate⟩ := attempt.range chain emptySent
  have selectedStream := prefix_payload_index prefixBytes attempt.output.packet.segment.payload _ rangePrefix index byte selected
  obtain ⟨prior, step, later, localIndex, same, position, present⟩ :=
    flatMap_location Step.emitted (attempt.prior ++ [attempt.step]) (prefixBytes.length + index) byte selectedStream
  obtain ⟨count, policy, amount, event, accepted, inside, pendingByte⟩ := step.emitted_index localIndex byte present
  have amountEq := step.send_amount count policy amount event accepted
  subst amount
  have actual : (Endpoint.send step.before count policy).decision = .accepted (.send count) := by
    simpa only [step.computed, event, evaluate] using accepted
  obtain ⟨output, produced, encoded, payload, sequence, _⟩ := Endpoint.send_output _ _ _ actual
  have actualOutput : step.result.output = some output := by
    simpa only [step.computed, event, evaluate] using produced
  have whole : steps = prior ++ step :: (later ++ attempt.later) := by
    have scopeEq : steps = (attempt.prior ++ [attempt.step]) ++ attempt.later := by
      simpa only [List.append_assoc, List.singleton_append] using attempt.same
    rw [same] at scopeEq
    simpa only [List.append_assoc, List.cons_append] using scopeEq
  let original : OutputAt steps := ⟨prior, step, later ++ attempt.later, whole, output, .send count policy event accepted actualOutput⟩
  have noRetry : NoRetry original.step := by intro other conflict; rw [event] at conflict; cases conflict
  have member : step ∈ attempt.prior ++ [attempt.step] := by rw [same]; simp
  have noLater : step.stamp ≤ attempt.step.stamp := by
    rcases List.mem_append.mp member with earlier | current
    · exact Nat.le_of_lt (attempt.prior_before order step earlier)
    · have equal : step = attempt.step := List.mem_singleton.mp current
      rw [equal]
      exact Nat.le_refl _
  have retryEarlier : ∀ policy, attempt.step.event = .timeout policy → step.stamp < attempt.step.stamp := by
    intro retry timeout
    rcases List.mem_append.mp member with earlier | current
    · exact attempt.prior_before order step earlier
    · have equal : step = attempt.step := List.mem_singleton.mp current
      have conflict := event
      rw [equal, timeout] at conflict
      cases conflict
  have originalByte : output.packet.segment.payload[localIndex]? = some byte := by
    rw [payload, List.getElem?_take_of_lt inside]
    exact pendingByte
  have history := chain
  rw [original.same] at history
  have balance := history.cut.1.pending
  change initial.pending ++ prior.flatMap Step.written = prior.flatMap Step.emitted ++ step.before.pending at balance
  simp only [emptyPending, List.nil_append] at balance
  have selectedWritten : (prior.flatMap Step.written)[(prior.flatMap Step.emitted).length + localIndex]? = some byte := by
    rw [balance]
    rw [List.getElem?_append_right (by omega)]
    simpa only [Nat.add_sub_cancel_left] using pendingByte
  obtain ⟨writerPrior, writer, writerLater, writerIndex, writerSplit, writerPosition, writtenByte⟩ :=
    flatMap_location Step.written prior ((prior.flatMap Step.emitted).length + localIndex) byte selectedWritten
  obtain ⟨bytes, writtenCount, writerEvent, writerAccepted, writerByte⟩ := writer.written_index writerIndex byte writtenByte
  have writerMember : writer ∈ original.prior := by change writer ∈ prior; rw [writerSplit]; simp
  exact ⟨⟨prefixBytes, rangePrefix, coordinate, original, localIndex, count, policy, event, accepted, originalByte,
    position, noLater, retryEarlier, writerPrior, writer, writerLater, writerSplit, bytes, writtenCount, writerIndex,
    writerEvent, writerAccepted, writerByte, writerPosition, original.prior_before order writer writerMember⟩⟩

theorem received_byte_origin (sourceChain : Chain sourceInitial sourceSteps sourceFinal)
    (history : DeliveryHistory sourceSteps targetSteps) (emptySent : sourceInitial.core.sent = [])
    (emptyPending : sourceInitial.pending = []) (step : Step) (member : step ∈ targetSteps)
    (index : Nat) (byte : UInt8) (selected : step.acceptedPayload[index]? = some byte) :
    ∃ input count size, step.event = .receive input ∧
      step.result.decision = .accepted (.receive count size) ∧
      ∃ attempt : OutputAt sourceSteps, BytePath attempt.output input ∧ attempt.step.stamp < step.stamp ∧
        Nonempty (AttemptByteOrigin sourceInitial sourceSteps attempt index byte) := by
  have nonempty : step.acceptedPayload ≠ [] := by intro empty; simp [empty] at selected
  obtain ⟨input, count, size, event, accepted, payload⟩ := step.data nonempty
  obtain ⟨attempt, earlier, path⟩ := history.delivered step member input event
  have sourceByte : attempt.output.packet.segment.payload[index]? = some byte := by
    rw [payload, path.fields.1] at selected
    exact selected
  exact ⟨input, count, size, event, accepted, attempt, path, earlier,
    attempt.byte_origin sourceChain emptySent emptyPending history.senderOrder index byte sourceByte⟩

theorem RunReceiptOrigin.attempt_origin (value : RunReceiptOrigin targetSteps run)
    (sourceChain : Chain sourceInitial sourceSteps sourceFinal) (history : DeliveryHistory sourceSteps targetSteps)
    (emptySent : sourceInitial.core.sent = []) (emptyPending : sourceInitial.pending = [])
    (index : Nat) (byte : UInt8) (selected : run.bytes[index]? = some byte) :
    ∃ attempt : OutputAt sourceSteps,
      BytePath attempt.output value.allocation.input ∧ attempt.step.stamp < value.issuer.stamp ∧
      Nonempty (AttemptByteOrigin sourceInitial sourceSteps attempt index byte) := by
  obtain ⟨attempt, earlier, path⟩ := history.delivered value.issuer value.member
    value.allocation.input value.allocation.event
  have sourceByte : attempt.output.packet.segment.payload[index]? = some byte := by
    rw [value.fields.1, path.fields.1] at selected
    exact selected
  exact ⟨attempt, path, earlier,
    attempt.byte_origin sourceChain emptySent emptyPending history.senderOrder index byte sourceByte⟩

theorem ActualReleasedByteOrigin.attempt_origin (value : ActualReleasedByteOrigin targetSteps release index byte)
    (sourceChain : Chain sourceInitial sourceSteps sourceFinal) (history : DeliveryHistory sourceSteps targetSteps)
    (emptySent : sourceInitial.core.sent = []) (emptyPending : sourceInitial.pending = []) :
    ∃ attempt : OutputAt sourceSteps,
      BytePath attempt.output value.origin.allocation.input ∧ attempt.step.stamp < value.origin.issuer.stamp ∧
      Nonempty (AttemptByteOrigin sourceInitial sourceSteps attempt value.localIndex byte) := by
  obtain ⟨attempt, earlier, path⟩ := history.delivered value.origin.issuer value.origin.issuer_member
    value.origin.allocation.input value.origin.allocation.event
  have sourceByte : attempt.output.packet.segment.payload[value.localIndex]? = some byte := by
    rw [← path.fields.1]
    exact value.input_byte
  exact ⟨attempt, path, earlier,
    attempt.byte_origin sourceChain emptySent emptyPending history.senderOrder value.localIndex byte sourceByte⟩

structure ReadReleasedByteOrigin (operations : List Step) (reader : Step) (index : Nat) (byte : UInt8) where
  prior : List Step
  later : List Step
  split : operations = prior ++ reader :: later
  releasePrior : List Step
  release : Step
  releaseLater : List Step
  releaseSplit : prior = releasePrior ++ release :: releaseLater
  releaseIndex : Nat
  releaseByte : release.releasedPayload[releaseIndex]? = some byte
  position : (prior.flatMap Step.readBytes).length + index =
    (releasePrior.flatMap Step.releasedPayload).length + releaseIndex
  origin : ActualReleasedByteOrigin operations release releaseIndex byte
  earlier : release.stamp < reader.stamp

theorem read_byte_origin (chain : Chain initial operations final) (emptyReceived : initial.core.received = [])
    (emptyHeld : initial.receiveStore.held = []) (ordered : Chronological operations)
    (reader : Step) (member : reader ∈ operations) (count : Nat) (event : reader.event = .read count)
    (index : Nat) (byte : UInt8) (selected : reader.readBytes[index]? = some byte) :
    Nonempty (ReadReleasedByteOrigin operations reader index byte) := by
  obtain ⟨prior, later, split, preceding, _⟩ := chain.split reader member
  have noRelease : reader.releasedPayload = [] := by
    simp only [Step.releasedPayload, ApplicationTrace.releasedPayload, event]
  have readerBalance := reader.received_balance
  rw [noRelease, List.append_nil] at readerBalance
  have readBound := (List.getElem?_eq_some_iff.mp selected).1
  have inBuffer : reader.before.core.received[index]? = some byte := by
    rw [readerBalance, List.getElem?_append_left readBound]
    exact selected
  have balance := preceding.received
  simp only [emptyReceived, List.nil_append] at balance
  have inReleases : (prior.flatMap Step.releasedPayload)[(prior.flatMap Step.readBytes).length + index]? = some byte := by
    rw [balance, List.getElem?_append_right (by omega)]
    simpa only [Nat.add_sub_cancel_left] using inBuffer
  obtain ⟨releasePrior, release, releaseLater, releaseIndex, releaseSplit, position, releaseByte⟩ :=
    flatMap_location Step.releasedPayload prior ((prior.flatMap Step.readBytes).length + index) byte inReleases
  have releaseMember : release ∈ prior := by rw [releaseSplit]; simp
  have memberAll : release ∈ operations := by
    have present : release ∈ prior ++ reader :: later := List.mem_append_left _ releaseMember
    exact Eq.mpr (congrArg (fun list => release ∈ list) split) present
  obtain ⟨origin⟩ := released_byte_origin chain emptyHeld release memberAll releaseIndex byte releaseByte
  have earlier : release.stamp < reader.stamp := by
    have pairs := ordered
    unfold Chronological at pairs
    rw [split] at pairs
    exact (List.pairwise_append.mp pairs).2.2 release releaseMember reader (by simp)
  exact ⟨⟨prior, later, split, releasePrior, release, releaseLater, releaseSplit,
    releaseIndex, releaseByte, position, origin, earlier⟩⟩

theorem ReadReleasedByteOrigin.attempt_origin (value : ReadReleasedByteOrigin targetSteps reader index byte)
    (sourceChain : Chain sourceInitial sourceSteps sourceFinal) (history : DeliveryHistory sourceSteps targetSteps)
    (emptySent : sourceInitial.core.sent = []) (emptyPending : sourceInitial.pending = []) :
    ∃ attempt : OutputAt sourceSteps,
      BytePath attempt.output value.origin.origin.allocation.input ∧
      attempt.step.stamp < value.origin.origin.issuer.stamp ∧
      value.origin.origin.issuer.stamp ≤ value.release.stamp ∧ value.release.stamp < reader.stamp ∧
      Nonempty (AttemptByteOrigin sourceInitial sourceSteps attempt value.origin.localIndex byte) := by
  obtain ⟨attempt, path, earlier, provenance⟩ := value.origin.attempt_origin sourceChain history emptySent emptyPending
  exact ⟨attempt, path, earlier, value.origin.origin.no_later history.receiverOrder, value.earlier, provenance⟩

end Netlib.Protocol.TCP.ApplicationTrace
