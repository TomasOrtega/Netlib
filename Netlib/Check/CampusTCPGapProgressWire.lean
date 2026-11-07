import Netlib.Check.CampusTCPGapProgressGateway
import Netlib.Check.CampusTCPGapProgressSender
import Netlib.Check.CampusTCPGapProgressReceiver

/-!
# Packet coordinates for the actual held-gap cut

The current lane coordinates fix the selected lower packet and later outputs.
The original packet keeps its actual historical ACK value.
-/

namespace Netlib.Check.CampusTCPGapProgressWire

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPGapProgressStart

variable {input : Input} {complete : H.Completed input.active input.passive}
  {cut : Cut input complete} {sender : Actor} {lower upper : List UInt8}

structure Geometry (initial : GapInitial cut sender lower upper) : Prop where
  lowerSequence : initial.lowerSource.attempt.output.packet.segment.sequence =
    (initial.gateway.seed.lane sender.direction).base
  observed : (initial.gateway.seed.lane sender.direction).observed = lower.length + upper.length
  senderCursor : (endpoint cut.endpoints sender).core.receiveNext =
    (initial.gateway.seed.peer sender.direction).base.add (initial.gateway.seed.peer sender.direction).observed
  receiverCursor : (endpoint cut.endpoints sender.other).core.sendNext =
    (initial.gateway.seed.peer sender.direction).base.add (initial.gateway.seed.peer sender.direction).highEnd
  lowerAck : initial.lowerSource.attempt.output.packet.segment.acknowledgment =
    (endpoint cut.endpoints sender).core.receiveNext
  peerComplete : (initial.gateway.seed.peer sender.direction).observed =
    (initial.gateway.seed.peer sender.direction).highEnd
  lowerTarget : initial.selected.emission.target = (endpoint cut.endpoints sender.other).core.inbound

structure DataFields (initial : GapInitial cut sender lower upper)
    (produced : Produced input.active input.passive) : Prop where
  header : produced.source.packet.header = initial.gateway.seed.entry.flow.input sender.direction
  sequence : produced.source.packet.segment.sequence = (initial.gateway.seed.lane sender.direction).base
  acknowledgment : produced.source.packet.segment.acknowledgment =
    (initial.gateway.seed.peer sender.direction).base.add (initial.gateway.seed.peer sender.direction).observed
  payload : produced.source.packet.segment.payload = lower
  profile : Admission.DataProfile produced.source.packet.segment
  ttl : 1 < produced.source.packet.ip.packet.ttl.toNat

structure AckFields (initial : GapInitial cut sender lower upper)
    (produced : Produced input.active input.passive) : Prop where
  header : produced.source.packet.header = initial.gateway.seed.entry.flow.input sender.other.direction
  sequence : produced.source.packet.segment.sequence =
    (initial.gateway.seed.peer sender.direction).base.add (initial.gateway.seed.peer sender.direction).highEnd
  acknowledgment : produced.source.packet.segment.acknowledgment =
    (initial.gateway.seed.lane sender.direction).base.add (initial.gateway.seed.lane sender.direction).observed
  payload : produced.source.packet.segment.payload = []
  profile : Admission.DataProfile produced.source.packet.segment
  ttl : 1 < produced.source.packet.ip.packet.ttl.toNat

structure DataLinkFields (initial : GapInitial cut sender lower upper) (served : Served input)
    (emission : WireForwarding.Emission served.ticket.value.source.packet) : Prop where
  source : DataFields initial served.ticket.value.produced
  target : emission.target = (endpoint cut.endpoints sender.other).core.inbound

variable {initial : GapInitial cut sender lower upper} {current : Cut input complete}

private def signature (state : Endpoint.State) := (state.core.inbound, state.effectiveMSS)

private theorem er_inbound (state : EstablishedReceive.State) (header : Packet.Header) (segment : Segment) :
    (EstablishedReceive.evaluate state header segment).state.inbound = state.inbound := by
  simp only [EstablishedReceive.evaluate, EstablishedReceive.finish]
  repeat' first | (solve | rfl) | split

private theorem er_window_inbound (state : EstablishedReceive.State) (value : EstablishedReceive.Input) (window : Nat) :
    (EstablishedReceive.receiveWithWindow state value window).state.inbound = state.inbound := by
  simp only [EstablishedReceive.receiveWithWindow, EstablishedReceive.evaluateWithWindow, EstablishedReceive.finish,
    EstablishedReceive.withAckWindow]
  repeat' first | (solve | rfl) | split

private theorem window_signature (before after : Endpoint.State) (segment : Segment) :
    signature (Endpoint.windowState before after segment) = signature after := by
  unfold Endpoint.windowState
  split <;> rfl

private theorem receive_model_inbound (state : Endpoint.State) (value : EstablishedReceive.Input) :
    (Endpoint.receiveModel state value).state.inbound = state.core.inbound := by
  cases selected : state.ackReaction with
  | none => simpa only [Endpoint.receiveModel, selected, EstablishedReceive.receive] using er_inbound state.core value.packet.header value.packet.segment
  | some reaction => simpa only [Endpoint.receiveModel, selected] using er_window_inbound state.core value reaction.window

private theorem recovery_blocked_signature (state : Endpoint.State) (reason : Recovery.Stop) :
    signature (Endpoint.recoveryBlocked state reason).state = signature state := by
  unfold Endpoint.recoveryBlocked
  split <;> rfl

private theorem ack_blocked_signature (state : Endpoint.State) (reason : AckReaction.Stop) :
    signature (Endpoint.ackBlocked state reason).state = signature state := by
  unfold Endpoint.ackBlocked
  split <;> rfl

private theorem runtime_signature (state : Endpoint.State) (recovery : Option Recovery.State)
    (reaction : Option AckReaction.State) :
    signature { state with recovery, ackReaction := reaction } = signature state := rfl

private theorem receive_state_signature (state : Endpoint.State) (value : EstablishedReceive.Input)
    (core : EstablishedReceive.State) :
    signature (Endpoint.receiveState state value core) = (core.inbound, state.effectiveMSS) := by
  rw [Endpoint.receiveState, window_signature]
  rfl

private theorem in_order_signature (state : Endpoint.State) (value : EstablishedReceive.Input) :
    signature (Endpoint.receiveInOrder state value).state = signature state := by
  by_cases valid : state.Valid
  · by_cases coherent : Endpoint.RecoveryCoherent state
    · by_cases prepared : Endpoint.AckCoherent state
      · have inbound := receive_model_inbound state value
        cases model : Endpoint.receiveModel state value with
        | mk core decision ack =>
          have same : core.inbound = state.core.inbound := by simpa only [model] using inbound
          simp only [Endpoint.receiveInOrder, valid, coherent, prepared, not_true_eq_false, ite_false, model]
          cases decision with
          | blocked reason =>
            cases reason with
            | unsupported reason => rfl
            | reject reason =>
              cases issued : Endpoint.issueRequest state state.core ack 0 with
              | error stop => exact ack_blocked_signature state stop
              | ok reaction => rfl
          | accepted count size =>
            dsimp only
            cases recovery : Endpoint.receiveRecovery state value.packet.segment count with
            | error stop => exact recovery_blocked_signature state stop
            | ok current =>
              dsimp only
              cases issued : Endpoint.issueRequest state core ack size with
              | error stop => exact ack_blocked_signature state stop
              | ok reaction =>
                exact (runtime_signature (Endpoint.receiveState state value core) current reaction).trans
                  ((receive_state_signature state value core).trans (congrArg (fun h => (h, state.effectiveMSS)) same))
      · simpa only [Endpoint.receiveInOrder, valid, coherent, prepared, not_true_eq_false,
          not_false_eq_true, ite_false, ite_true] using ack_blocked_signature state .ledger
    · simpa only [Endpoint.receiveInOrder, valid, coherent, not_true_eq_false,
        not_false_eq_true, ite_false, ite_true] using recovery_blocked_signature state .ledger
  · simp only [Endpoint.receiveInOrder, valid, not_false_eq_true, ite_true]
    rfl

private theorem header_signature (state next : Endpoint.State) (header : ReceiveReassembly.HeaderEffect)
    (inbound : header.after.inbound = state.core.inbound)
    (accepted : Endpoint.applyHeader state header = .ok next) : signature next = signature state := by
  simp only [Endpoint.applyHeader] at accepted
  split at accepted
  · cases accepted
  · cases stored : state.recovery with
    | none =>
      simp only [stored] at accepted
      cases accepted
      rw [window_signature]
      simpa only [signature] using congrArg (fun h => (h, state.effectiveMSS)) inbound
    | some recovery =>
      simp only [stored] at accepted
      cases updated : Recovery.acknowledgeAt recovery header.acknowledged header.run.metadata.receivedAt with
      | error reason => simp only [updated, Except.map] at accepted; cases accepted
      | ok after =>
        simp only [updated, Except.map] at accepted
        cases accepted
        rw [window_signature]
        simpa only [signature] using congrArg (fun h => (h, state.effectiveMSS)) inbound

private theorem process_signature (state : Endpoint.State) (runs : List ReceiveReassembly.Run)
    (processed : Endpoint.ReceiveProcessed) (accepted : Endpoint.processRuns state runs = .ok processed) :
    signature processed.received = signature state := by
  induction runs generalizing state processed with
  | nil => simp only [Endpoint.processRuns.eq_1, Except.ok.injEq] at accepted; subst processed; rfl
  | cons head tail ih =>
    cases first : ReceiveReassembly.applyRun state.core head with
    | error reason => simp only [Endpoint.processRuns.eq_2, first] at accepted; cases accepted
    | ok header =>
      cases applied : Endpoint.applyHeader state header with
      | error reason => simp only [Endpoint.processRuns.eq_2, first, applied] at accepted; cases accepted
      | ok next =>
        cases rest : Endpoint.processRuns next tail with
        | error reason => simp only [Endpoint.processRuns.eq_2, first, applied, rest] at accepted; cases accepted
        | ok result =>
          simp only [Endpoint.processRuns.eq_2, first, applied, rest, Except.ok.injEq] at accepted
          subst processed
          have headerInbound : header.after.inbound = state.core.inbound := by
            rw [(ReceiveReassembly.applyRun_fields _ _ _ first).2.2.2.2.2]
            rfl
          exact (ih next result rest).trans (header_signature state next header headerInbound applied)

private theorem receive_signature (state : Endpoint.State) (value : EstablishedReceive.Input) :
    signature (Endpoint.receive state value).state = signature state := by
  have stopped : ∀ reason ack, signature (Endpoint.receiveStopped state reason ack).state = signature state := by
    intro reason ack
    cases reason with
    | unsupported reason => rfl
    | reject reason =>
      simp only [Endpoint.receiveStopped]
      split
      · unfold Endpoint.ackBlocked; split <;> rfl
      · rfl
  have failed : ∀ receipt failure, signature (Endpoint.receiveFailed state receipt failure).result.state = signature state := by
    intro receipt failure
    cases failure with
    | header value =>
      simp only [Endpoint.receiveFailed]
      split
      · exact stopped _ _
      · rfl
    | recovery value =>
      simp only [Endpoint.receiveFailed]
      split
      · unfold Endpoint.recoveryBlocked; split <;> rfl
      · rfl
  unfold Endpoint.receive Endpoint.receiveEffect
  dsimp only
  split
  · simp only [Endpoint.receiveRaw]
    repeat' first
      | (solve | rfl)
      | (solve | unfold Endpoint.recoveryBlocked; split <;> rfl)
      | (solve | unfold Endpoint.ackBlocked; split <;> rfl)
      | (solve | exact stopped _ _)
      | (solve | exact in_order_signature state value)
      | (solve | exact failed _ _)
      | (solve | exact process_signature _ _ _ (by assumption))
      | split
  · rfl

private theorem evaluate_signature (state : Endpoint.State) (event : ApplicationTrace.Event) :
    signature (ApplicationTrace.evaluate state event).state = signature state := by
  cases event with
  | write bytes =>
    simp only [ApplicationTrace.evaluate, Endpoint.write]
    repeat' first | (solve | rfl) | split
  | read count =>
    simp only [ApplicationTrace.evaluate, Endpoint.read]
    repeat' first | (solve | rfl) | split
  | send count policy =>
    simp only [ApplicationTrace.evaluate, Endpoint.send]
    repeat' first
      | (solve | rfl)
      | (solve | unfold Endpoint.recoveryBlocked; split <;> rfl)
      | (solve | unfold Endpoint.ackBlocked; split <;> rfl)
      | split
  | receive value => exact receive_signature _ _
  | emitAck policy =>
    simp only [ApplicationTrace.evaluate, Endpoint.emitAck, Endpoint.pureAck]
    repeat' first | (solve | rfl) | (solve | unfold Endpoint.ackBlocked; split <;> rfl) | split
  | dispatchAck policy =>
    simp only [ApplicationTrace.evaluate, Endpoint.dispatchAck, Endpoint.pureAck]
    repeat' first | (solve | rfl) | (solve | unfold Endpoint.ackBlocked; split <;> rfl) | split
  | enableRecovery =>
    simp only [ApplicationTrace.evaluate, Endpoint.enableRecovery]
    repeat' first | (solve | rfl) | (solve | unfold Endpoint.recoveryBlocked; split <;> rfl) | split
  | enableStartupRecovery data =>
    simp only [ApplicationTrace.evaluate, Endpoint.enableStartupRecovery]
    repeat' first | (solve | rfl) | (solve | unfold Endpoint.recoveryBlocked; split <;> rfl) | split
  | advanceClock millis =>
    simp only [ApplicationTrace.evaluate, Endpoint.advanceClock]
    repeat' first
      | (solve | rfl)
      | (solve | unfold Endpoint.recoveryBlocked; split <;> rfl)
      | (solve | unfold Endpoint.ackBlocked; split <;> rfl)
      | split
  | timeout policy =>
    simp only [ApplicationTrace.evaluate, Endpoint.timeout]
    repeat' first
      | (solve | rfl)
      | (solve | unfold Endpoint.recoveryBlocked; split <;> rfl)
      | (solve | unfold Endpoint.ackBlocked; split <;> rfl)
      | split
  | enableAck =>
    simp only [ApplicationTrace.evaluate, Endpoint.enableAck]
    repeat' first | (solve | rfl) | (solve | unfold Endpoint.ackBlocked; split <;> rfl) | split


private theorem chain_signature (chain : ApplicationTrace.Chain before steps after) : signature after = signature before := by
  induction chain with
  | nil state => rfl
  | cons head _ ih =>
    apply ih.trans
    rw [head.computed]
    exact evaluate_signature head.before head.event

theorem chain_inbound (chain : ApplicationTrace.Chain before steps after) : after.core.inbound = before.core.inbound :=
  congrArg Prod.fst (chain_signature chain)

theorem chain_effectiveMSS (chain : ApplicationTrace.Chain before steps after) : after.effectiveMSS = before.effectiveMSS :=
  congrArg Prod.snd (chain_signature chain)

theorem endpoint_inbound (cut : Cut input complete) (actor : Actor) :
    (endpoint cut.endpoints actor).core.inbound = (seed complete actor).core.inbound :=
  chain_inbound (endpoint_chain cut actor)

theorem endpoint_effectiveMSS (cut : Cut input complete) (actor : Actor) :
    (endpoint cut.endpoints actor).effectiveMSS = (seed complete actor).effectiveMSS :=
  chain_effectiveMSS (endpoint_chain cut actor)

private theorem original_chain (original : Original cut sender lower) :
    ApplicationTrace.Chain (seed complete sender) original.attempt.prior original.attempt.step.before := by
  have chain := endpoint_chain cut sender
  rw [original.attempt.same] at chain
  exact chain.cut.1

theorem entry_eq (initial : GapInitial cut sender lower upper) : initial.gateway.seed.entry = initial.basis.entry :=
  initial.gateway.identity.entry.trans initial.basis.aligned.entryEq

theorem input_tuple (initial : GapInitial cut sender lower upper) (actor : Actor) :
    Output.reverse (endpoint cut.endpoints actor).core.inbound = initial.gateway.seed.entry.flow.input actor.direction := by
  rw [endpoint_inbound cut actor, entry_eq initial]
  cases actor
  · exact initial.basis.aligned.clientInput
  · exact initial.basis.aligned.serverInput

theorem output_tuple (initial : GapInitial cut sender lower upper) (actor : Actor) :
    initial.gateway.seed.entry.flow.output actor.direction = (endpoint cut.endpoints actor.other).core.inbound := by
  rw [endpoint_inbound cut actor.other, entry_eq initial]
  cases actor
  · exact initial.basis.aligned.serverOutput.symm
  · exact initial.basis.aligned.clientOutput.symm

theorem endpoint_peer_mss (initial : GapInitial cut sender lower upper) (actor : Actor) :
    (endpoint cut.endpoints actor).effectiveMSS ≤ (initial.gateway.seed.peerMSS actor.direction).limit := by
  rw [endpoint_effectiveMSS cut actor]
  cases actor
  · change complete.certificate.activeSeed.effectiveMSS ≤ initial.gateway.seed.serverMSS.limit
    rw [initial.gateway.identity.serverMSS, initial.basis.aligned.serverMSS,
      complete.certificate.directional_mss.2.2.1, complete.activeConfig, complete.passiveConfig]
    exact (Handshake.effectiveMSS_bounds _ _ (CampusTCPRoundStart.active_valid complete)).2.1
  · change complete.certificate.passiveSeed.effectiveMSS ≤ initial.gateway.seed.clientMSS.limit
    rw [initial.gateway.identity.clientMSS, initial.basis.aligned.clientMSS,
      complete.certificate.directional_mss.2.2.2, complete.activeConfig, complete.passiveConfig]
    exact (Handshake.effectiveMSS_bounds _ _ (CampusTCPRoundStart.passive_valid complete)).2.1

private theorem original_encoded (original : Original cut sender lower) :
    Endpoint.emit original.attempt.step.before lower = .ok original.attempt.output := by
  cases original.attempt.origin with
  | send count policy event accepted actual =>
    have selected : (Endpoint.send original.attempt.step.before count policy).decision = .accepted (.send count) := by
      simpa only [original.attempt.step.computed, event, ApplicationTrace.evaluate] using accepted
    obtain ⟨packet, output, encoded, _, _, _⟩ := Endpoint.send_output _ _ _ selected
    have stored : (Endpoint.send original.attempt.step.before count policy).output = some original.attempt.output := by
      simpa only [original.attempt.step.computed, event, ApplicationTrace.evaluate] using actual
    have same := Option.some.inj (output.symm.trans stored)
    subst packet
    have payload := (Endpoint.emit_payload _ _ _ encoded).symm.trans original.payload
    simpa only [payload] using encoded
  | retry count policy event accepted actual => rw [original.event] at event; cases event
  | ack policy event accepted actual => rw [original.event] at event; cases event
  | dispatchAck policy event accepted actual => rw [original.event] at event; cases event

private theorem emit_ttl (state : Endpoint.State) (payload : List UInt8) (packet : EstablishedReceive.Input)
    (encoded : Endpoint.emit state payload = .ok packet) : packet.packet.ip.packet.ttl.toNat = 64 := by
  cases stored : state.ackReaction with
  | none =>
    rw [(Output.emit_fields state.core payload packet (by simpa only [Endpoint.emit, stored] using encoded)).2.2.2]
    rfl
  | some reaction =>
    exact Endpoint.emitAt_ttl state state.core.sendNext payload packet
      (by simpa only [Endpoint.emit, Endpoint.emitAt, stored, Output.emitWindow] using encoded)

private theorem emit_profile (state : Endpoint.State) (payload : List UInt8) (packet : EstablishedReceive.Input)
    (encoded : Endpoint.emit state payload = .ok packet) : Admission.DataProfile packet.packet.segment := by
  have fields := Endpoint.emit_transport state payload packet encoded
  exact ⟨.inl fields.2.2.2.2.1, fields.2.2.2.2.2.2.1⟩

private theorem emitAt_profile (state : Endpoint.State) (sequence : Seq) (payload : List UInt8) (packet : EstablishedReceive.Input)
    (encoded : Endpoint.emitAt state sequence payload = .ok packet) : Admission.DataProfile packet.packet.segment := by
  have fields := Endpoint.emitAt_transport state sequence payload packet encoded
  exact ⟨.inl fields.2.2.2.2.1, fields.2.2.2.2.2.2.1⟩

theorem initial_data_fields (geometry : Geometry initial) : DataFields initial initial.lowerSource.produced := by
  let original := initial.lowerSource
  have encoded := original_encoded original
  have fields := Endpoint.emit_transport _ _ _ encoded
  rw [original.application]
  refine ⟨?_, geometry.lowerSequence, geometry.lowerAck.trans geometry.senderCursor, original.payload,
    emit_profile _ _ _ encoded, ?_⟩
  · change original.attempt.output.packet.header = _
    rw [fields.1, chain_inbound (original_chain original)]
    rw [← endpoint_inbound cut sender]
    exact input_tuple initial sender
  · change 1 < original.attempt.output.packet.ip.packet.ttl.toNat
    rw [emit_ttl _ _ _ encoded]
    decide

theorem lower_mss (initial : GapInitial cut sender lower upper) :
    lower.length ≤ (initial.gateway.seed.peerMSS sender.direction).limit := by
  have full := initial.flight.coherent
  rw [Endpoint.RecoveryCoherent, initial.flight.runtime] at full
  have size := full.1.2.2.2
  have total : Recovery.flight initial.flight.recovery = lower.length + upper.length := by
    simp only [Recovery.flight, initial.flight.ledger, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, initial.flight.headCount, initial.flight.tailCount]
  have currentMSS := endpoint_peer_mss initial sender
  rw [total, full.2.1] at size
  omega



theorem initial_link_fields (geometry : Geometry initial) :
    DataLinkFields initial initial.selected.served initial.selected.emission := by
  refine ⟨?_, geometry.lowerTarget⟩
  rw [initial.selected.source]
  exact initial_data_fields geometry

theorem retry_fields (geometry : Geometry initial) (operation : ApplicationTrace.Step)
    (packet : EstablishedReceive.Input) (origin : ApplicationTrace.OutputOrigin operation packet)
    (flight : CampusTCPGapProgressSender.Flight initial.flight operation.before retries)
    (encoded : Endpoint.emitAt operation.before operation.before.core.sendUna lower = .ok packet) :
    DataFields initial (.application sender operation packet origin) := by
  have fields := Endpoint.emitAt_transport _ _ _ _ encoded
  refine ⟨?_, fields.2.1.trans (flight.headSequence.trans geometry.lowerSequence), ?_,
    Endpoint.emitAt_payload _ _ _ _ encoded, emitAt_profile _ _ _ _ encoded, ?_⟩
  · change packet.packet.header = _
    rw [fields.1, flight.core]
    exact input_tuple initial sender
  · exact fields.2.2.1.trans ((congrArg EstablishedReceive.State.receiveNext flight.core).trans geometry.senderCursor)
  · change 1 < packet.packet.ip.packet.ttl.toNat
    rw [Endpoint.emitAt_ttl _ _ _ _ encoded]
    decide

theorem ack_fields (geometry : Geometry initial) (operation : ApplicationTrace.Step)
    (packet : EstablishedReceive.Input) (origin : ApplicationTrace.OutputOrigin operation packet)
    (receiver : CampusTCPGapProgressReceiver.Facts initial operation.before true)
    (encoded : Endpoint.emit operation.before [] = .ok packet) :
    AckFields initial (.application sender.other operation packet origin) := by
  have fields := Endpoint.emit_transport _ _ _ encoded
  refine ⟨?_, fields.2.1.trans (receiver.sendNext.trans geometry.receiverCursor), ?_,
    Endpoint.emit_payload _ _ _ encoded, emit_profile _ _ _ encoded, ?_⟩
  · change packet.packet.header = _
    rw [fields.1, receiver.core]
    exact input_tuple initial sender.other
  · change packet.packet.segment.acknowledgment = _
    rw [fields.2.2.1, receiver.receiveNext]
    change (CampusTCPGapProgressReceiver.source initial).core.receiveNext.add (lower.length + upper.length) = _
    rw [← receiver.geometry.lowerSequence, geometry.lowerSequence, geometry.observed]
  · change 1 < packet.packet.ip.packet.ttl.toNat
    rw [emit_ttl _ _ _ encoded]
    decide

theorem receiver_sent_empty (initial : GapInitial cut sender lower upper) :
    (endpoint cut.endpoints sender.other).core.sent = [] := by
  have coherent := initial.receiver.coherent
  rw [Endpoint.RecoveryCoherent, initial.receiver.runtime] at coherent
  have flight := coherent.2.2.1
  simp only [Recovery.flight, initial.receiver.idle, List.map_nil, List.sum_nil] at flight
  exact List.length_eq_zero_iff.mp flight.symm

theorem receiver_sendUna_next (initial : GapInitial cut sender lower upper) :
    (endpoint cut.endpoints sender.other).core.sendUna = (endpoint cut.endpoints sender.other).core.sendNext := by
  have span := initial.receiver.valid.1.2.2.2.2.1
  simpa only [receiver_sent_empty initial, List.length_nil, Seq.add_zero] using span

theorem DataFields.ack_old (fields : DataFields initial produced) (geometry : Geometry initial) :
    Seq.distance produced.source.packet.segment.acknowledgment (endpoint cut.endpoints sender.other).core.sendUna ≤
      EstablishedReceive.maxSendWindow := by
  rw [fields.acknowledgment, geometry.peerComplete, ← geometry.receiverCursor, ← receiver_sendUna_next initial,
    Seq.distance_self]
  exact Nat.zero_le _

private theorem shape_peer_base  {first after : Admission.Session} (shape : Shape first after) (direction : Admission.Direction) :
    (after.peer direction).base = (first.peer direction).base := by
  cases direction
  · exact shape.base .reply
  · exact shape.base .original

private theorem shape_peer_highEnd  {first after : Admission.Session} (shape : Shape first after) (direction : Admission.Direction) :
    (after.peer direction).highEnd = (first.peer direction).highEnd := by
  cases direction
  · exact congrArg Netlib.Theory.SparseCoverage.State.highEnd (shape.coverage .reply)
  · exact congrArg Netlib.Theory.SparseCoverage.State.highEnd (shape.coverage .original)

private theorem shape_peer_mss  {first after : Admission.Session} (shape : Shape first after) (direction : Admission.Direction) :
    after.peerMSS direction = first.peerMSS direction := by
  cases direction
  · exact shape.serverMSS
  · exact shape.clientMSS

private theorem other_sender (session : Admission.Session) (sender : Actor) :
    session.sender sender.other.direction = session.peer sender.direction := by cases sender <;> rfl

private theorem other_peer (session : Admission.Session) (sender : Actor) :
    session.peer sender.other.direction = session.lane sender.direction := by cases sender <;> rfl

theorem DataFields.current_header (fields : DataFields initial produced)
    (gateway : CampusTCPGapProgressGateway.Current initial.gateway current) :
    produced.source.packet.header = gateway.session.entry.flow.input sender.direction := by
  rw [fields.header, gateway.shape.entry]

theorem DataFields.current_sequence (fields : DataFields initial produced)
    (gateway : CampusTCPGapProgressGateway.Current initial.gateway current) :
    produced.source.packet.segment.sequence = (gateway.session.lane sender.direction).base := by
  rw [fields.sequence, gateway.shape.base]

theorem DataFields.current_ack (fields : DataFields initial produced)
    (gateway : CampusTCPGapProgressGateway.Current initial.gateway current) :
    produced.source.packet.segment.acknowledgment = (gateway.session.peer sender.direction).base.add
      (gateway.session.peer sender.direction).observed := by
  rw [fields.acknowledgment, shape_peer_base gateway.shape, CampusTCPGapProgressGateway.shape_peer_observed gateway.shape]

theorem DataFields.admission_ready (fields : DataFields initial produced)
    (gateway : CampusTCPGapProgressGateway.Current initial.gateway current) :
    Admission.RepeatedReady gateway.session sender.direction produced.source.packet.segment
      (beforeService input current.report.final .standby).admission.observations := by
  apply gateway.lower_admission_ready initial.lowerRange _ initial.lowerNonempty fields.profile
    (fields.current_sequence gateway) fields.payload (fields.current_ack gateway)
  rw [shape_peer_mss gateway.shape]
  exact lower_mss initial

theorem AckFields.current_header (fields : AckFields initial produced)
    (gateway : CampusTCPGapProgressGateway.Current initial.gateway current) :
    produced.source.packet.header = gateway.session.entry.flow.input sender.other.direction := by
  rw [fields.header, gateway.shape.entry]

theorem AckFields.current_sequence (fields : AckFields initial produced)
    (gateway : CampusTCPGapProgressGateway.Current initial.gateway current) :
    produced.source.packet.segment.sequence = (gateway.session.sender sender.other.direction).base.add
      (gateway.session.sender sender.other.direction).highEnd := by
  rw [fields.sequence, other_sender, shape_peer_base gateway.shape, shape_peer_highEnd gateway.shape]

theorem AckFields.current_ack (fields : AckFields initial produced)
    (gateway : CampusTCPGapProgressGateway.Current initial.gateway current) :
    produced.source.packet.segment.acknowledgment = (gateway.session.peer sender.other.direction).base.add
      (gateway.session.peer sender.other.direction).observed := by
  rw [fields.acknowledgment, other_peer, gateway.shape.base]
  exact congrArg ((initial.gateway.seed.lane sender.direction).base.add)
    (congrArg Netlib.Theory.SparseCoverage.State.frontier (gateway.shape.coverage sender.direction)).symm

theorem AckFields.admission_ready (fields : AckFields initial produced)
    (gateway : CampusTCPGapProgressGateway.Current initial.gateway current) :
    Admission.AckReady gateway.session sender.other.direction produced.source.packet.segment :=
  gateway.covering_ack_ready sender.other.direction _ fields.profile fields.payload
    (fields.current_sequence gateway) (fields.current_ack gateway)

end Netlib.Check.CampusTCPGapProgressWire
