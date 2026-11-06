import Netlib.Check.CampusTCPTwoProgressReceiver
import Netlib.Check.CampusTCPTwoProgressGatewayReady

/-!
# Packet fields for both two-record paths

Sequence positions use the initial endpoint cursors.
ACK window space comes from the current receiver state.
-/

namespace Netlib.Check.CampusTCPTwoProgressWire

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper bytes : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {served : Served input} {produced : Produced input.active input.passive}

theorem acknowledgment_cursor (initial : TwoWriteInitial cut sender gateway lower upper) :
    (endpoint cut.endpoints sender).core.receiveNext = (endpoint cut.endpoints sender.other).core.sendUna := by
  rw [initial.receiverState.idle.cursor, initial.geometry.receiverSequence,
    ← initial.geometry.peerComplete, ← initial.geometry.senderAck]

theorem receiver_sequence (initial : TwoWriteInitial cut sender gateway lower upper) :
    (endpoint cut.endpoints sender.other).core.sendNext = (endpoint cut.endpoints sender).core.receiveNext := by
  rw [initial.geometry.receiverSequence, ← initial.geometry.peerComplete, ← initial.geometry.senderAck]

structure DataFields (initial : TwoWriteInitial cut sender gateway lower upper) (offset : Nat) (bytes : List UInt8)
    (produced : Produced input.active input.passive) : Prop where
  header : produced.source.packet.header = initial.gatewayState.session.entry.flow.input sender.direction
  sequence : produced.source.packet.segment.sequence = (endpoint cut.endpoints sender).core.sendNext.add offset
  acknowledgment : produced.source.packet.segment.acknowledgment = (endpoint cut.endpoints sender).core.receiveNext
  payload : produced.source.packet.segment.payload = bytes
  profile : Admission.DataProfile produced.source.packet.segment
  ttl : 1 < produced.source.packet.ip.packet.ttl.toNat

structure AckFields (initial : TwoWriteInitial cut sender gateway lower upper) (count : Nat)
    (produced : Produced input.active input.passive) : Prop where
  header : produced.source.packet.header = initial.gatewayState.session.entry.flow.input sender.other.direction
  sequence : produced.source.packet.segment.sequence = (endpoint cut.endpoints sender.other).core.sendNext
  acknowledgment : produced.source.packet.segment.acknowledgment = (endpoint cut.endpoints sender).core.sendNext.add count
  payload : produced.source.packet.segment.payload = []
  profile : Admission.DataProfile produced.source.packet.segment
  ttl : 1 < produced.source.packet.ip.packet.ttl.toNat
  window : lower.length + upper.length ≤ count + produced.source.packet.segment.window.val

theorem offeredWindow_le_outputWindow (state : Endpoint.State) (coherent : Endpoint.AckCoherent state) :
    Endpoint.offeredWindow state ≤ Endpoint.outputWindow state := by
  cases runtime : state.ackReaction with
  | none => simp only [Endpoint.offeredWindow, Endpoint.outputWindow, runtime, Nat.le_refl]
  | some reaction =>
    have valid : reaction.advertisement.Valid state.core.window := by
      have prepared : state.recovery.isSome = true ∧ reaction.Coherent state.core.receiveNext state.core.window state.localReceiveMSS.limit := by
        simpa only [Endpoint.AckCoherent, runtime] using coherent
      exact prepared.2.1
    simpa only [Endpoint.offeredWindow, Endpoint.outputWindow, runtime, AckReaction.State.window,
      AckReaction.candidate] using
      (ReceiveAdvertisement.candidate_bounds reaction.advertisement state.core.capacity state.core.window state.effectiveMSS valid).1

theorem ack_fields (initial : TwoWriteInitial cut sender gateway lower upper)
    (operation : ApplicationTrace.Step) (packet : EstablishedReceive.Input)
    (origin : ApplicationTrace.OutputOrigin operation packet)
    (facts : CampusTCPTwoProgressReceiver.Facts initial operation.before stage)
    (encoded : Endpoint.emit operation.before [] = .ok packet) :
    AckFields initial (stage.bytes lower upper).length (.application sender.other operation packet origin) := by
  have fields := Endpoint.emit_transport _ _ _ encoded
  refine ⟨?_, fields.2.1.trans facts.sendNext, ?_, Endpoint.emit_payload _ _ _ encoded,
    (CampusTCPRoundLocal.emit_profile _ _ _ encoded).1, ?_, ?_⟩
  · change packet.packet.header = _
    rw [fields.1, facts.inbound]
    exact initial.input_tuple sender.other
  · change packet.packet.segment.acknowledgment = _
    rw [fields.2.2.1, facts.receiveNext, CampusTCPTwoProgressReceiver.source, initial.geometry.receiverCursor]
  · change 1 < packet.packet.ip.packet.ttl.toNat
    rw [CampusTCPRoundLocal.emit_ttl _ _ _ encoded]
    decide
  · change lower.length + upper.length ≤ _ + packet.packet.segment.window.val
    rw [fields.2.2.2.1]
    exact Nat.le_trans facts.space (Nat.add_le_add_left (offeredWindow_le_outputWindow _ facts.prepared.1) _)

theorem DataFields.receiver (fields : DataFields initial offset bytes served.ticket.value.produced)
    (emission : WireForwarding.Emission served.ticket.value.source.packet)
    (target : emission.target = initial.gatewayState.session.entry.flow.output sender.direction) :
    CampusTCPTwoProgressReceiver.PacketFields initial offset bytes emission.asInput := by
  have controls := CampusTCPRoundEmission.profile_controls (CampusTCPRoundEmission.emission_profile emission fields.profile)
  refine ⟨?_, controls.1, controls.2, ?_, ?_, ?_⟩
  · change emission.decoded.header = _
    rw [emission.header, target]
    exact initial.output_tuple sender
  · exact emission.control.1.trans (fields.sequence.trans (congrArg (fun sequence => sequence.add offset) initial.geometry.receiverCursor.symm))
  · exact emission.control.2.1.trans (fields.acknowledgment.trans (acknowledgment_cursor initial))
  · exact emission.payload.trans fields.payload

theorem AckFields.admission_ready (fields : AckFields initial count produced)
    (view : CampusTCPTwoProgressGatewayState.View initial current)
    (within : initial.geometry.«prefix» + count ≤ (view.gateway.session.lane sender.direction).observed)
    (stale : (view.gateway.session.lane sender.direction).acknowledged ≤ initial.geometry.«prefix» + count + 65535) :
    Admission.AckReady view.gateway.session sender.other.direction produced.source.packet.segment := by
  apply view.receiver_ack_ready produced.source.packet.segment (initial.geometry.«prefix» + count)
    fields.profile fields.payload fields.sequence
  · rw [fields.acknowledgment, initial.geometry.senderCursor, Seq.add_add]
  · exact within
  · exact stale

theorem AckFields.window_reserve (fields : AckFields initial count produced)
    (view : CampusTCPTwoProgressGatewayState.View initial current)
    (within : initial.geometry.«prefix» + count ≤ (view.gateway.session.lane sender.direction).observed) :
    initial.geometry.«prefix» + lower.length + upper.length ≤
      Admission.ackOffset (view.gateway.session.lane sender.direction) produced.source.packet.segment +
        produced.source.packet.segment.window.val := by
  have peerLane : view.gateway.session.peer sender.other.direction = view.gateway.session.lane sender.direction := by
    cases sender <;> rfl
  have offset := CampusTCPTwoProgressGateway.ack_offset_add view.gateway.session sender.other.direction
    produced.source.packet.segment (initial.geometry.«prefix» + count) (by simpa only [peerLane] using within)
    (by rw [peerLane, view.gateway.identity.base, fields.acknowledgment, initial.geometry.senderCursor, Seq.add_add])
  rw [peerLane] at offset
  rw [offset]
  have space := fields.window
  omega

end Netlib.Check.CampusTCPTwoProgressWire
