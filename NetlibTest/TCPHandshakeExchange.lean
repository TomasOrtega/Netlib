import Netlib.Protocol.TCP.HandshakeExchange

namespace NetlibTest.TCPHandshakeExchange

open Netlib Protocol TCP
namespace H
export Netlib.Protocol.TCP.Handshake
  (Socket Local SynSent SynReceived ActiveEstablished PassiveEstablished)
end H
namespace X
export Netlib.Protocol.TCP.HandshakeExchange
  (Input Complete DeliverySpec Delivery Times)
end X
namespace A
export Netlib.Protocol.TCP.ApplicationTrace
  (Step Event Chain DeliveryHistory OutputAt OutputOrigin BytePath)
end A

private def activeConfig : H.Local := ⟨⟨3221225985, 41000⟩, Seq.ofNat 99, 4, 4, 1500, none⟩
private def remote : H.Socket := ⟨3325256706, 8080⟩
private def passiveConfig : H.Local := ⟨⟨3405803778, 8080⟩, Seq.ofNat 199, 4, 4, 1500, none⟩
private def forwardTuple : Packet.Header := ⟨3325256705, 3405803778, Packet.Protocol.tcp, 40000, 8080⟩
private def backwardTuple : Packet.Header := Handshake.inbound activeConfig remote

private theorem activeValid : activeConfig.Valid := by decide
private theorem passiveValid : passiveConfig.Valid := by decide

structure StartupWitness where
  input : X.Input
  value : X.Complete input
  activeConfig : input.active = TCPHandshakeExchange.activeConfig
  passiveConfig : input.passive = TCPHandshakeExchange.passiveConfig
  checked : input.check = .ok value
  times : input.times = ⟨0, 1, 2, 3⟩

theorem ordinary_startup : Nonempty StartupWitness := by
  obtain ⟨pending, opened⟩ := Handshake.activeOpen_exists activeConfig remote activeValid
  have activeFields := Handshake.activeOpen_fields _ _ _ _ opened
  let syn := HandshakeExchange.Delivery.rewritten pending.output forwardTuple 63 rfl
  have synFields := pending.output_fields
  have synHeader : syn.input.packet.header = forwardTuple :=
    (TCPRewrite.rewrite pending.output.packet forwardTuple 63 pending.output.valid rfl).header rfl
  have synSequence : syn.input.packet.segment.sequence = pending.config.iss := synFields.2.1
  have destination : Handshake.destination passiveConfig syn.input := by
    unfold Handshake.destination
    rw [synHeader]
    exact ⟨rfl, rfl⟩
  have profile : Handshake.Profile syn.input 2 := pending.output_profile
  obtain ⟨listener, listened⟩ := Handshake.listenSyn_exists passiveConfig syn.input passiveValid destination profile
  have passiveFields := Handshake.listenSyn_fields _ _ _ _ listened
  let synAck := HandshakeExchange.Delivery.rewritten listener.output backwardTuple 63 rfl
  have synAckFields := listener.output_fields
  have synAckHeader : synAck.input.packet.header = Handshake.inbound pending.config pending.remote := by
    have actual := (TCPRewrite.rewrite listener.output.packet backwardTuple 63 listener.output.valid rfl).header rfl
    rw [activeFields.1, activeFields.2.1]
    exact actual
  have synAckAccepted : Handshake.ActiveAccepted pending synAck.input := by
    refine ⟨synAckHeader, listener.output_profile, ?_⟩
    change listener.output.packet.segment.acknowledgment = _
    rw [synAckFields.2.2.1, passiveFields.2.1, synSequence]
  obtain ⟨active, activeComputed⟩ := Handshake.synSentSynAck_exists pending synAck.input synAckAccepted
  let ack := HandshakeExchange.Delivery.rewritten active.output forwardTuple 63 rfl
  have ackFields := Output.emit_transport _ _ _ active.outputGenerated
  have ackHeader : ack.input.packet.header = listener.input.packet.header := by
    have actual := (TCPRewrite.rewrite active.output.packet forwardTuple 63 active.output.valid rfl).header rfl
    rw [passiveFields.2.1, synHeader]
    exact actual
  have ackAccepted : Handshake.PassiveAccepted listener ack.input := by
    refine ⟨ackHeader, ⟨ackFields.2.2.2.2.1, ackFields.2.2.2.2.2.2.1,
      Output.emit_payload active.seed.core [] active.output active.outputGenerated⟩, ?_, ?_⟩
    · change active.output.packet.segment.sequence = _
      rw [ackFields.2.1, active.derived]
      change pending.config.iss.add 1 = listener.input.packet.segment.sequence.add 1
      rw [passiveFields.2.1, synSequence]
    · change active.output.packet.segment.acknowledgment = _
      rw [ackFields.2.2.1, active.derived]
      change synAck.input.packet.segment.sequence.add 1 = listener.config.iss.add 1
      exact congrArg (fun value : Seq => value.add 1) synAckFields.2.1
  obtain ⟨passive, passiveComputed⟩ := Handshake.synReceivedAck_exists listener ack.input ackAccepted
  let input : X.Input := ⟨activeConfig, remote, passiveConfig, true, true, true,
    ⟨syn.input.bytes, [⟨forwardTuple, 63⟩]⟩,
    ⟨synAck.input.bytes, [⟨backwardTuple, 63⟩]⟩,
    ⟨ack.input.bytes, [⟨forwardTuple, 63⟩]⟩, ⟨0, 1, 2, 3⟩⟩
  let value : X.Complete input := ⟨by change 0 < 1 ∧ 1 < 2 ∧ 2 < 3; decide, pending, opened, syn, listener, listened,
    synAck, active, activeComputed, ack, passive, passiveComputed⟩
  exact ⟨⟨input, value, rfl, rfl, HandshakeExchange.Input.check_of_complete value, rfl⟩⟩


private theorem receiveState_core (before : Endpoint.State) (input : EstablishedReceive.Input)
    (after : EstablishedReceive.State) : (Endpoint.receiveState before input after).core = after := by
  unfold Endpoint.receiveState Endpoint.windowState
  split <;> rfl

private theorem chronological_two (first second : A.Step) (before : first.stamp < second.stamp) :
    ApplicationTrace.Chronological [first, second] := by
  exact .cons (by intro item member; simp only [List.mem_singleton] at member; subst item; exact before)
    (.cons (by intro item member; cases member) .nil)

structure ApplicationWitness where
  startup : StartupWitness
  activeSteps : List A.Step
  passiveSteps : List A.Step
  activeFinal : Endpoint.State
  passiveFinal : Endpoint.State
  activeChain : A.Chain startup.value.activeSeed activeSteps activeFinal
  passiveChain : A.Chain startup.value.passiveSeed passiveSteps passiveFinal
  written : activeSteps.flatMap ApplicationTrace.Step.written = [42]
  read : passiveSteps.flatMap ApplicationTrace.Step.readBytes = [42]
  currentInstance : Nat → EstablishedReceive.Input → Prop
  assurance : HandshakeExchange.ApplicationAssurance startup.value currentInstance activeSteps passiveSteps

theorem startup_to_application : Nonempty ApplicationWitness := by
  obtain ⟨startup⟩ := ordinary_startup
  let activeSeed := startup.value.activeSeed
  let passiveSeed := startup.value.passiveSeed
  have activeValid : activeSeed.Valid := startup.value.valid.1
  have passiveValid : passiveSeed.Valid := startup.value.valid.2
  have activeEmpty : activeSeed.pending = [] := startup.value.empty.1
  have activeSent : activeSeed.core.sent = [] := startup.value.empty.2.1
  have passiveReceived : passiveSeed.core.received = [] := startup.value.empty.2.2.2.2.2
  have passiveSent : passiveSeed.core.sent = [] := startup.value.empty.2.2.2.2.1
  have activeRecovery : activeSeed.recovery = none := by
    simp only [activeSeed, HandshakeExchange.Complete.activeSeed, startup.value.active.derived,
      Handshake.activeSeed]
  have passiveRecovery : passiveSeed.recovery = none := by
    simp only [passiveSeed, HandshakeExchange.Complete.passiveSeed, startup.value.passive.derived,
      Handshake.passiveSeed]
  have pendingLimit : activeSeed.pendingLimit = 4 := by
    rw [startup.value.configuration.2.1, startup.activeConfig]
    rfl
  have peerWindow : activeSeed.sendWindow = 4 := by
    rw [startup.value.peer_capacities.1, startup.passiveConfig]
    rfl
  have receiveWindow : passiveSeed.core.window = 4 := by
    change passiveSeed.core.capacity - passiveSeed.core.received.length = 4
    rw [passiveReceived, startup.value.configuration.2.2.2.1, startup.passiveConfig]
    rfl
  have ipLimit : activeSeed.ipSendLimit = 1500 := by
    rw [startup.value.configuration.2.2.1, startup.activeConfig]
    rfl
  have fits : activeSeed.pending.length + [42].length ≤ activeSeed.pendingLimit := by
    rw [activeEmpty, pendingLimit]
    decide
  obtain ⟨writtenState, writtenEq⟩ : ∃ state, state = Endpoint.writeState activeSeed [42] := ⟨_, rfl⟩
  have writtenValid : writtenState.Valid := by
    rw [writtenEq]
    exact Endpoint.writeState_valid _ _ activeValid fits
  have writeResult : Endpoint.write activeSeed [42] =
      ⟨writtenState, .accepted (.write 1), none, [], none⟩ := by
    rw [writtenEq]
    exact Endpoint.write_of_fits _ _ activeValid fits
  let write : A.Step := ⟨activeSeed, .write [42],
    ⟨writtenState, .accepted (.write 1), none, [], none⟩, 4, activeValid, writeResult.symm⟩
  have pendingBytes : writtenState.pending = [42] := by rw [writtenEq]; simp [Endpoint.writeState, activeEmpty]
  have sendReady : Endpoint.SendReady writtenState 1 := by
    refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [pendingBytes]
      decide
    · rw [writtenEq]
      change activeSeed.core.sent.length + 1 ≤ activeSeed.sendWindow
      rw [activeSent, peerWindow]
      decide
    · rw [writtenEq]
      change activeSeed.core.sent.length + 1 ≤ EstablishedReceive.maxSendWindow
      rw [activeSent]
      decide
    · exact writtenValid.2.2.2.2.1
    · rw [writtenEq]
      change 40 + 1 ≤ activeSeed.ipSendLimit
      rw [ipLimit]
      decide
    · rw [writtenEq]
      simp only [Endpoint.recoveryReady, Endpoint.writeState, activeRecovery]
  obtain ⟨output, encoded⟩ := Output.emit_exists writtenState.core (writtenState.pending.take 1)
    writtenValid.1 (by rw [pendingBytes]; decide)
  obtain ⟨sentState, sentEq⟩ : ∃ state, state = Endpoint.sendState writtenState 1 := ⟨_, rfl⟩
  have sendResult : Endpoint.send writtenState 1 true =
      ⟨sentState, .accepted (.send 1), some output, [], none⟩ := by
    rw [sentEq]
    exact Endpoint.send_of_ready _ _ writtenValid sendReady _ encoded
  let send : A.Step := ⟨writtenState, .send 1 true,
    ⟨sentState, .accepted (.send 1), some output, [], none⟩, 5, writtenValid, sendResult.symm⟩
  let input := output.rewrite passiveSeed.core.inbound 63 passiveValid.1.1
  have fields := Output.emit_transport _ _ _ encoded
  have payload : input.packet.segment.payload = [42] := by
    change output.packet.segment.payload = _
    rw [Output.emit_payload _ _ _ encoded, pendingBytes]
    rfl
  have sequence : input.packet.segment.sequence = passiveSeed.core.receiveNext := by
    change output.packet.segment.sequence = _
    rw [fields.2.1, writtenEq]
    exact startup.value.cursors.2.symm
  have acknowledgment : input.packet.segment.acknowledgment = passiveSeed.core.sendUna := by
    change output.packet.segment.acknowledgment = _
    rw [fields.2.2.1, writtenEq]
    change activeSeed.core.receiveNext = passiveSeed.core.sendUna
    have cursor := passiveValid.1.2.2.2.2.1
    simp only [passiveSent, List.length_nil, Seq.add_zero] at cursor
    exact startup.value.cursors.1.trans cursor.symm
  have flags : input.packet.segment.flags = 16 := fields.2.2.2.2.1
  have options : input.packet.segment.options = [] := fields.2.2.2.2.2.2.1
  have header : input.packet.header = passiveSeed.core.inbound :=
    (TCPRewrite.rewrite output.packet passiveSeed.core.inbound 63 output.valid passiveValid.1.1).header passiveValid.1.1
  have ready : EstablishedReceive.Ready passiveSeed.core input.packet.header input.packet.segment := by
    refine ⟨passiveValid.1, header, ?_, ?_, ?_⟩
    · rw [ReceiveWindow.acceptsSegment, ReceiveWindow.segmentLength, sequence, flags, payload, receiveWindow]
      simp [ReceiveWindow.accepts, Seq.distance_self, Seq.InInterval]
    · rw [EstablishedReceive.control, flags, options]
      decide
    · rw [flags]
      decide
  have dataFits : input.packet.segment.payload.length ≤ passiveSeed.core.window := by
    rw [payload, receiveWindow]
    decide
  have coreReceived := EstablishedReceive.receive_old_ack_data passiveSeed.core input ready
    (by rw [acknowledgment, Seq.distance_self]; decide) sequence dataFits
  obtain ⟨receivedState, receivedEq⟩ : ∃ state,
      state = Endpoint.receiveState passiveSeed input (EstablishedReceive.commit passiveSeed.core [42] 0) := ⟨_, rfl⟩
  have receiveResult : Endpoint.receive passiveSeed input =
      ⟨receivedState, .accepted (.receive 0 1), none, [],
        some (EstablishedReceive.request (EstablishedReceive.commit passiveSeed.core [42] 0) .data)⟩ := by
    rw [receivedEq]
    rw [Endpoint.receive_without_recovery passiveSeed input passiveValid passiveRecovery, coreReceived]
    simp only [payload]
    rfl
  have receivedValid : receivedState.Valid := by
    have valid := Endpoint.receive_valid passiveSeed input passiveValid
    rw [receiveResult] at valid
    exact valid
  let receive : A.Step := ⟨passiveSeed, .receive input,
    ⟨receivedState, .accepted (.receive 0 1), none, [],
      some (EstablishedReceive.request (EstablishedReceive.commit passiveSeed.core [42] 0) .data)⟩,
    6, passiveValid, receiveResult.symm⟩
  have receivedBytes : receivedState.core.received = [42] := by
    rw [receivedEq, receiveState_core]
    simp only [EstablishedReceive.commit, passiveReceived, List.nil_append]
  obtain ⟨readState, readEq⟩ : ∃ state, state = Endpoint.readState receivedState 1 := ⟨_, rfl⟩
  have readResult : Endpoint.read receivedState 1 =
      ⟨readState, .accepted (.read 1), none, [42], none⟩ := by
    rw [readEq]
    have actual := Endpoint.read_of_fits receivedState 1 receivedValid (by rw [receivedBytes]; decide)
    simpa only [receivedBytes, List.take_succ_cons, List.take_zero] using actual
  let read : A.Step := ⟨receivedState, .read 1,
    ⟨readState, .accepted (.read 1), none, [42], none⟩, 7, receivedValid, readResult.symm⟩
  let activeSteps := [write, send]
  let passiveSteps := [receive, read]
  have activeChain : A.Chain activeSeed activeSteps sentState := .cons write (.cons send (.nil _))
  have passiveChain : A.Chain passiveSeed passiveSteps readState := .cons receive (.cons read (.nil _))
  have activeOrder : ApplicationTrace.Chronological activeSteps := chronological_two write send (by change 4 < 5; decide)
  have passiveOrder : ApplicationTrace.Chronological passiveSteps := chronological_two receive read (by change 6 < 7; decide)
  have forward : A.DeliveryHistory activeSteps passiveSteps := by
    refine ⟨activeOrder, passiveOrder, ?_⟩
    intro step member value event
    simp only [passiveSteps, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl
    · have same : value = input := Netlib.Protocol.TCP.ApplicationTrace.Event.receive.inj event.symm
      subst value
      refine ⟨⟨[write], send, [], rfl, output, .send 1 true rfl rfl rfl⟩, by change 5 < 6; decide, ?_⟩
      exact .rewrite passiveSeed.core.inbound 63 passiveValid.1.1 rfl
    · cases event
  have backward : A.DeliveryHistory passiveSteps activeSteps := by
    refine ⟨passiveOrder, activeOrder, ?_⟩
    intro step member value event
    simp only [activeSteps, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl <;> cases event
  have activeEpoch : (activeSteps.flatMap ApplicationTrace.Step.emitted).length < Seq.halfSpace := by
    simp only [activeSteps, List.flatMap_cons, List.flatMap_nil, ApplicationTrace.Step.emitted,
      ApplicationTrace.emitted]
    dsimp only [write, send]
    rw [pendingBytes]
    decide
  have passiveEpoch : (passiveSteps.flatMap ApplicationTrace.Step.emitted).length < Seq.halfSpace := by
    change 0 < Seq.halfSpace
    decide
  let currentInstance : Nat → EstablishedReceive.Input → Prop := fun stamp packet =>
    (stamp = 1 ∧ packet.bytes = startup.value.syn.input.bytes) ∨
    (stamp = 2 ∧ packet.bytes = startup.value.synAck.input.bytes) ∨
    (stamp = 3 ∧ packet.bytes = startup.value.ack.input.bytes) ∨
    (stamp = 6 ∧ packet.bytes = input.bytes)
  have environment : HandshakeExchange.Environment startup.value currentInstance := by
    refine ⟨?_, ?_, ?_⟩ <;> rw [startup.times]
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr (.inl ⟨rfl, rfl⟩)
    · exact .inr (.inr (.inl ⟨rfl, rfl⟩))
  have quiet : HandshakeExchange.QuietBoundary startup.value activeSteps passiveSteps := by
    constructor
    · intro step member
      simp only [activeSteps, List.mem_cons, List.mem_nil_iff, or_false] at member
      rcases member with rfl | rfl
      · rw [startup.times]
        change 3 < 4
        decide
      · rw [startup.times]
        change 3 < 5
        decide
    · intro step member
      simp only [passiveSteps, List.mem_cons, List.mem_nil_iff, or_false] at member
      rcases member with rfl | rfl
      · rw [startup.times]
        change 3 < 6
        decide
      · rw [startup.times]
        change 3 < 7
        decide
  have activeInputs : ∀ step ∈ activeSteps, ∀ packet,
      step.event = .receive packet → currentInstance step.stamp packet := by
    intro step member packet event
    simp only [activeSteps, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl <;> cases event
  have passiveInputs : ∀ step ∈ passiveSteps, ∀ packet,
      step.event = .receive packet → currentInstance step.stamp packet := by
    intro step member packet event
    simp only [passiveSteps, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl
    · have same : packet = input := Netlib.Protocol.TCP.ApplicationTrace.Event.receive.inj event.symm
      subst packet
      exact .inr (.inr (.inr ⟨rfl, rfl⟩))
    · cases event
  have assurance := startup.value.startup_to_application activeChain passiveChain forward backward
    activeEpoch passiveEpoch environment quiet (by rfl) (by rfl) activeInputs passiveInputs
  refine ⟨⟨startup, activeSteps, passiveSteps, sentState, readState, activeChain, passiveChain, ?_, ?_,
    currentInstance, assurance⟩⟩
  · rfl
  · rfl

end NetlibTest.TCPHandshakeExchange
