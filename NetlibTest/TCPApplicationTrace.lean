import Netlib.Protocol.TCP.ApplicationTrace

namespace NetlibTest.TCPApplicationTrace

open Netlib Protocol TCP
namespace A
export Netlib.Protocol.TCP.ApplicationTrace
  (Step Event Chain DeliveryHistory OutputAt OutputOrigin BytePath)
end A

private def sender : Endpoint.State :=
  { core := ⟨⟨3221225986, 3221225985, Packet.Protocol.tcp, 8080, 41000⟩,
      Seq.ofNat 200, 4, [], Seq.ofNat 100, Seq.ofNat 100, []⟩
    pending := []
    pendingLimit := 4
    sendWindow := 4
    sendWL1 := Seq.ofNat 200
    sendWL2 := Seq.ofNat 100
    effectiveMSS := 536
    ipSendLimit := 1500 }

private def receiver : Endpoint.State :=
  { core := ⟨⟨3325256705, 3405803778, Packet.Protocol.tcp, 40000, 8080⟩,
      Seq.ofNat 100, 4, [], Seq.ofNat 200, Seq.ofNat 200, []⟩
    pending := []
    pendingLimit := 4
    sendWindow := 4
    sendWL1 := Seq.ofNat 100
    sendWL2 := Seq.ofNat 200
    effectiveMSS := 536
    ipSendLimit := 1500 }

private theorem sender_valid : sender.Valid := by decide
private theorem receiver_valid : receiver.Valid := by decide

private theorem receiveState_core (before : Endpoint.State) (input : EstablishedReceive.Input)
    (after : EstablishedReceive.State) : (Endpoint.receiveState before input after).core = after := by
  unfold Endpoint.receiveState Endpoint.windowState
  split <;> rfl

structure Witness where
  senderSteps : List A.Step
  receiverSteps : List A.Step
  senderFinal : Endpoint.State
  receiverFinal : Endpoint.State
  senderChain : A.Chain sender senderSteps senderFinal
  receiverChain : A.Chain receiver receiverSteps receiverFinal
  forward : A.DeliveryHistory senderSteps receiverSteps
  backward : A.DeliveryHistory receiverSteps senderSteps
  written : senderSteps.flatMap ApplicationTrace.Step.written = [42]
  read : receiverSteps.flatMap ApplicationTrace.Step.readBytes = [42]
  senderEmpty : senderFinal.core.sent = []
  ackAccepted : ∃ step ∈ senderSteps, step.stamp = 5 ∧
    step.result.decision = .accepted (.receive 1 0)
  application : receiverSteps.flatMap ApplicationTrace.Step.readBytes <+:
      senderSteps.flatMap ApplicationTrace.Step.written ∧
    senderSteps.flatMap ApplicationTrace.Step.readBytes <+:
      receiverSteps.flatMap ApplicationTrace.Step.written

private theorem chronological_three (first second third : A.Step)
    (one : first.stamp < second.stamp) (two : first.stamp < third.stamp)
    (three : second.stamp < third.stamp) : ApplicationTrace.Chronological [first, second, third] := by
  apply List.Pairwise.cons
  · intro item member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl
    · exact one
    · exact two
  · apply List.Pairwise.cons
    · intro item member
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
      cases member
      exact three
    · exact .cons (by intro item member; cases member) .nil

theorem rewritten_application_prefix : Nonempty Witness := by
  obtain ⟨writtenState, writtenEq⟩ : ∃ state, state = Endpoint.writeState sender [42] := ⟨_, rfl⟩
  have writtenValid : writtenState.Valid := by
    rw [writtenEq]
    exact Endpoint.writeState_valid sender [42] sender_valid (by decide)
  have writeResult : Endpoint.write sender [42] =
      ⟨writtenState, .accepted (.write 1), none, [], none⟩ := by
    rw [writtenEq]
    exact Endpoint.write_of_fits sender [42] sender_valid (by decide)
  let write : A.Step := ⟨sender, .write [42],
    ⟨writtenState, .accepted (.write 1), none, [], none⟩, 0, sender_valid, writeResult.symm⟩
  have ready : Endpoint.SendReady writtenState 1 := by rw [writtenEq]; decide
  have writtenAck : writtenState.ackReaction = none := by rw [writtenEq]; rfl
  have prepared : Endpoint.ackReady writtenState = .ok () := by
    simp only [Endpoint.ackReady, Endpoint.AckCoherent, writtenAck, not_true_eq_false, ite_false]
  obtain ⟨output, encoded⟩ := Output.emit_exists writtenState.core
    (writtenState.pending.take 1) writtenValid.1 (by rw [writtenEq]; decide)
  obtain ⟨sentState, sentEq⟩ : ∃ state, state = Endpoint.sendState writtenState 1 := ⟨_, rfl⟩
  have sentValid : sentState.Valid := by
    rw [sentEq]
    exact Endpoint.sendState_valid writtenState 1 writtenValid ready
  have sendResult : Endpoint.send writtenState 1 true =
      ⟨sentState, .accepted (.send 1), some output, [], none⟩ := by
    rw [sentEq]
    apply Endpoint.send_of_ready writtenState 1 writtenValid ready prepared output
    simpa only [Endpoint.emit, writtenAck] using encoded
  let send : A.Step := ⟨writtenState, .send 1 true,
    ⟨sentState, .accepted (.send 1), some output, [], none⟩, 1, writtenValid, sendResult.symm⟩
  let input := output.rewrite receiver.core.inbound 63 rfl
  have fields := Output.emit_transport writtenState.core (writtenState.pending.take 1) output encoded
  have payload : input.packet.segment.payload = [42] := by
    change output.packet.segment.payload = _
    rw [Output.emit_payload _ _ _ encoded, writtenEq]
    rfl
  have sequence : input.packet.segment.sequence = Seq.ofNat 100 := by
    change output.packet.segment.sequence = _
    rw [fields.2.1, writtenEq]
    rfl
  have acknowledgment : input.packet.segment.acknowledgment = Seq.ofNat 200 := by
    change output.packet.segment.acknowledgment = _
    rw [fields.2.2.1, writtenEq]
    rfl
  have flags : input.packet.segment.flags = 16 := fields.2.2.2.2.1
  have options : input.packet.segment.options = [] := fields.2.2.2.2.2.2.1
  have header : input.packet.header = receiver.core.inbound :=
    (TCPRewrite.rewrite output.packet receiver.core.inbound 63 output.valid rfl).header rfl
  have coreReady : EstablishedReceive.Ready receiver.core input.packet.header input.packet.segment := by
    refine ⟨receiver_valid.1, header, ?_, ?_, ?_⟩
    · rw [ReceiveWindow.acceptsSegment, ReceiveWindow.segmentLength, sequence, flags, payload]
      decide
    · rw [EstablishedReceive.control, flags, options]
      decide
    · rw [flags]
      decide
  have coreReceived := EstablishedReceive.receive_old_ack_data receiver.core input coreReady
    (by rw [acknowledgment]; decide) sequence (by rw [payload]; decide)
  obtain ⟨receivedState, receivedEq⟩ : ∃ state,
      state = Endpoint.receiveState receiver input (EstablishedReceive.commit receiver.core [42] 0) := ⟨_, rfl⟩
  have receiveResult : Endpoint.receive receiver input =
      ⟨receivedState, .accepted (.receive 0 1), none, [],
        some (EstablishedReceive.request (EstablishedReceive.commit receiver.core [42] 0) .data)⟩ := by
    rw [receivedEq]
    rw [Endpoint.receive_without_recovery receiver input receiver_valid rfl rfl, coreReceived]
    simp only [payload]
    rfl
  have receivedCore : receivedState.core = EstablishedReceive.commit receiver.core [42] 0 := by
    rw [receivedEq, receiveState_core]
  have receivedValid : receivedState.Valid := by
    rw [receivedEq]
    exact Endpoint.receiveState_valid receiver input _ receiver_valid
      (EstablishedReceive.commit_valid receiver.core [42] 0 receiver_valid.1 (by decide) (by decide))
  let receive : A.Step := ⟨receiver, .receive input,
    ⟨receivedState, .accepted (.receive 0 1), none, [],
      some (EstablishedReceive.request (EstablishedReceive.commit receiver.core [42] 0) .data)⟩,
    2, receiver_valid, receiveResult.symm⟩
  have receivedBytes : receivedState.core.received = [42] := by rw [receivedCore]; rfl
  obtain ⟨readState, readEq⟩ : ∃ state, state = Endpoint.readState receivedState 1 := ⟨_, rfl⟩
  have readValid : readState.Valid := by rw [readEq]; exact Endpoint.readState_valid _ _ receivedValid
  have readResult : Endpoint.read receivedState 1 =
      ⟨readState, .accepted (.read 1), none, [42], none⟩ := by
    rw [readEq]
    have actual := Endpoint.read_of_fits receivedState 1 receivedValid (by rw [receivedBytes]; decide)
    simpa only [receivedBytes, List.take_succ_cons, List.take_zero] using actual
  let read : A.Step := ⟨receivedState, .read 1,
    ⟨readState, .accepted (.read 1), none, [42], none⟩, 3, receivedValid, readResult.symm⟩
  obtain ⟨ackOutput, ackEncoded⟩ := Output.emit_exists readState.core [] readValid.1 (by decide)
  have receivedAck : receivedState.ackReaction = none := by
    rw [receivedEq]
    unfold Endpoint.receiveState Endpoint.windowState
    split <;> rfl
  have readAck : readState.ackReaction = none := by
    rw [readEq]
    simp only [Endpoint.readState, receivedAck, Option.map_none]
  have ackResult : Endpoint.emitAck readState true =
      ⟨readState, .accepted .emitAck, some ackOutput, [], none⟩ := by
    simp only [Endpoint.emitAck, Endpoint.pureAck, Endpoint.responseReady, readValid, not_true_eq_false,
      ite_false, Bool.not_true, Bool.false_eq_true, readAck, Endpoint.ackReady, Endpoint.AckCoherent,
      Endpoint.emit, ackEncoded, Endpoint.outputState, Option.map_none]
    rw [← readAck]
  let ack : A.Step := ⟨readState, .emitAck true,
    ⟨readState, .accepted .emitAck, some ackOutput, [], none⟩, 4, readValid, ackResult.symm⟩
  let ackInput := ackOutput.rewrite sender.core.inbound 63 rfl
  have ackFields := Output.emit_transport readState.core [] ackOutput ackEncoded
  have ackPayload : ackInput.packet.segment.payload = [] := Output.emit_payload readState.core [] ackOutput ackEncoded
  have ackFlags : ackInput.packet.segment.flags = 16 := ackFields.2.2.2.2.1
  have ackOptions : ackInput.packet.segment.options = [] := ackFields.2.2.2.2.2.2.1
  have ackSequence : ackInput.packet.segment.sequence = Seq.ofNat 200 := by
    change ackOutput.packet.segment.sequence = _
    rw [ackFields.2.1, readEq]
    change receivedState.core.sendNext = _
    rw [receivedCore]
    rfl
  have ackNumber : ackInput.packet.segment.acknowledgment = Seq.ofNat 101 := by
    change ackOutput.packet.segment.acknowledgment = _
    rw [ackFields.2.2.1, readEq]
    change receivedState.core.receiveNext = _
    rw [receivedCore]
    rfl
  have ackHeader : ackInput.packet.header = sentState.core.inbound := by
    have actual := (TCPRewrite.rewrite ackOutput.packet sender.core.inbound 63 ackOutput.valid rfl).header rfl
    change ackInput.packet.header = _ at actual
    rw [sentEq, writtenEq]
    exact actual
  have ackReady : EstablishedReceive.Ready sentState.core ackInput.packet.header ackInput.packet.segment := by
    refine ⟨sentValid.1, ackHeader, ?_, ?_, ?_⟩
    · rw [ReceiveWindow.acceptsSegment, ReceiveWindow.segmentLength, ackSequence, ackFlags, ackPayload, sentEq, writtenEq]
      decide
    · rw [EstablishedReceive.control, ackFlags, ackOptions]
      decide
    · rw [ackFlags]
      decide
  have forwardAck : Seq.distance sentState.core.sendUna ackInput.packet.segment.acknowledgment = 1 := by
    rw [ackNumber, sentEq, writtenEq]
    decide
  have ackBound : Seq.distance sentState.core.sendUna ackInput.packet.segment.acknowledgment ≤ sentState.core.sent.length := by
    rw [forwardAck, sentEq, writtenEq]
    decide
  have ackInOrder : ackInput.packet.segment.sequence = sentState.core.receiveNext := by
    rw [ackSequence, sentEq, writtenEq]
    rfl
  have coreReturned : EstablishedReceive.receive sentState.core ackInput =
      ⟨EstablishedReceive.commit sentState.core [] 1, .accepted 1 0, none⟩ := by
    rw [EstablishedReceive.receive, EstablishedReceive.evaluate_of_ready _ _ _ ackReady,
      EstablishedReceive.acknowledgedCount_forward _ _ ackBound, forwardAck]
    dsimp only
    rw [EstablishedReceive.finish_of_fits _ _ _ ackInOrder (by rw [ackPayload]; exact Nat.zero_le _), ackPayload]
    rfl
  obtain ⟨returnedState, returnedEq⟩ : ∃ state,
      state = Endpoint.receiveState sentState ackInput (EstablishedReceive.commit sentState.core [] 1) := ⟨_, rfl⟩
  have returnedResult : Endpoint.receive sentState ackInput =
      ⟨returnedState, .accepted (.receive 1 0), none, [], none⟩ := by
    rw [returnedEq]
    have disabled : sentState.recovery = none := by rw [sentEq, writtenEq]; rfl
    have ackDisabled : sentState.ackReaction = none := by
      rw [sentEq]
      simp only [Endpoint.sendState, Endpoint.outputState, writtenAck, Option.map_none]
    rw [Endpoint.receive_without_recovery sentState ackInput sentValid disabled ackDisabled, coreReturned]
  let returned : A.Step := ⟨sentState, .receive ackInput,
    ⟨returnedState, .accepted (.receive 1 0), none, [], none⟩, 5, sentValid, returnedResult.symm⟩
  let senderSteps := [write, send, returned]
  let receiverSteps := [receive, read, ack]
  have senderChain : A.Chain sender senderSteps returnedState :=
    .cons write (.cons send (.cons returned (.nil returnedState)))
  have receiverChain : A.Chain receiver receiverSteps readState :=
    .cons receive (.cons read (.cons ack (.nil readState)))
  have senderOrder : ApplicationTrace.Chronological senderSteps :=
    chronological_three write send returned (by change 0 < 1; decide) (by change 0 < 5; decide) (by change 1 < 5; decide)
  have receiverOrder : ApplicationTrace.Chronological receiverSteps :=
    chronological_three receive read ack (by change 2 < 3; decide) (by change 2 < 4; decide) (by change 3 < 4; decide)
  have forward : A.DeliveryHistory senderSteps receiverSteps := by
    refine ⟨senderOrder, receiverOrder, ?_⟩
    intro step member value event
    simp only [receiverSteps, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl
    · have same : value = input := ApplicationTrace.Event.receive.inj event.symm
      subst value
      refine ⟨⟨[write], send, [returned], rfl, output, .send 1 true rfl rfl rfl⟩, ?_, ?_⟩
      · change 1 < 2
        decide
      · exact .rewrite receiver.core.inbound 63 rfl rfl
    · cases event
    · cases event
  have backward : A.DeliveryHistory receiverSteps senderSteps := by
    refine ⟨receiverOrder, senderOrder, ?_⟩
    intro step member value event
    simp only [senderSteps, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl
    · cases event
    · cases event
    · have same : value = ackInput := ApplicationTrace.Event.receive.inj event.symm
      subst value
      refine ⟨⟨[receive, read], ack, [], rfl, ackOutput, .ack true rfl rfl rfl⟩, ?_, ?_⟩
      · change 4 < 5
        decide
      · exact .rewrite sender.core.inbound 63 rfl rfl
  have senderWritten : senderSteps.flatMap ApplicationTrace.Step.written = [42] := rfl
  have receiverRead : receiverSteps.flatMap ApplicationTrace.Step.readBytes = [42] := rfl
  have senderEpoch : (senderSteps.flatMap ApplicationTrace.Step.emitted).length < Seq.halfSpace := by
    simp only [senderSteps, List.flatMap_cons, List.flatMap_nil, ApplicationTrace.Step.emitted,
      ApplicationTrace.emitted, write, send, returned, List.nil_append, List.append_nil]
    rw [writtenEq]
    decide
  have receiverEpoch : (receiverSteps.flatMap ApplicationTrace.Step.emitted).length < Seq.halfSpace := by
    change ([] : List UInt8).length < Seq.halfSpace
    decide
  have application := ApplicationTrace.paired_application_prefix senderChain receiverChain forward backward
    rfl rfl rfl rfl rfl rfl rfl rfl senderEpoch receiverEpoch
  have senderEmpty : returnedState.core.sent = [] := by
    rw [returnedEq, receiveState_core]
    change (sentState.core.sent.drop 1) = []
    rw [sentEq, writtenEq]
    rfl
  refine ⟨⟨senderSteps, receiverSteps, returnedState, readState,
    senderChain, receiverChain, forward, backward, senderWritten, receiverRead, senderEmpty, ?_, application⟩⟩
  exact ⟨returned, by simp only [senderSteps, List.mem_cons, List.mem_nil_iff, or_false, or_true], rfl, rfl⟩

end NetlibTest.TCPApplicationTrace
