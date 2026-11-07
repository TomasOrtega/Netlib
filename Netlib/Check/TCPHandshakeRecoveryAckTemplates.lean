import Netlib.Check.TCPHandshakeRecoveryPacketInventory
import Netlib.Protocol.TCP.HandshakeAckEquality

/-!
# Exact startup ACK templates

Current empty-stream cores determine the canonical ACK bytes.
Window markers do not change either ACK template.
-/

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

namespace Phase

def ackTemplate : Phase active passive → Kind → Option H.Input
  | .answered value, .synReplyAck => some (HandshakeDuplicate.syn_received_ack value.pending).output
  | .acknowledged value _, .finalAck => some value.ready.output
  | .acknowledged value _, .synReplyAck => some (HandshakeDuplicate.syn_received_ack value.answered.pending).output
  | .complete value _ _, .finalAck => some value.certificate.active.output
  | .complete value _ _, .synReplyAck => some (HandshakeDuplicate.syn_received_ack value.certificate.passivePending).output
  | _, _ => none

structure AckFrame (before after : Phase active passive) : Prop where
  templates : ∀ kind packet, before.ackTemplate kind = some packet → after.ackTemplate kind = some packet

end Phase

def AckKind (kind : Kind) : Prop := kind = .finalAck ∨ kind = .synReplyAck

structure AckInventory (state : State active passive) : Prop where
  templates : ∀ output ∈ state.emissions, AckKind output.kind → state.phase.ackTemplate output.kind = some output.packet

variable {active passive : H.Local}
variable {before after state : State active passive} {output : Emission}
variable {phase : Phase active passive} {kind : Kind} {packet : H.Input}

theorem Acknowledged.current_ack_eq (acknowledged : O.Acknowledged active passive)
    {client : PreData acknowledged.ready.seed} (clean : PreDataClean acknowledged.ready.seed client)
    (ack : HandshakeDuplicate.BareAck (Output.reverse client.current.core.inbound)
      client.current.core.sendNext client.current.core.receiveNext client.current.core.window client.current.ipSendLimit) :
    ack.output = acknowledged.ready.output := by
  have generated : Output.emit client.current.core [] = .ok acknowledged.ready.output := by
    rw [clean.1.core]
    exact acknowledged.ready.outputGenerated
  exact ack.empty_output client.current.core acknowledged.ready.output generated

theorem Completed.current_active_ack_eq (complete : O.Completed active passive)
    {client : PreData complete.certificate.activeSeed} (clean : PreDataClean complete.certificate.activeSeed client)
    (ack : HandshakeDuplicate.BareAck (Output.reverse client.current.core.inbound)
      client.current.core.sendNext client.current.core.receiveNext client.current.core.window client.current.ipSendLimit) :
    ack.output = complete.certificate.active.output := by
  have generated : Output.emit client.current.core [] = .ok complete.certificate.active.output := by
    rw [clean.1.core]
    exact complete.certificate.active.outputGenerated
  exact ack.empty_output client.current.core complete.certificate.active.output generated

theorem Completed.current_passive_ack_eq (complete : O.Completed active passive)
    {server : PreData complete.certificate.passiveSeed} (clean : PreDataClean complete.certificate.passiveSeed server)
    (ack : HandshakeDuplicate.BareAck (Output.reverse server.current.core.inbound)
      server.current.core.sendNext server.current.core.receiveNext server.current.core.window server.current.ipSendLimit) :
    ack.output = (HandshakeDuplicate.syn_received_ack complete.certificate.passivePending).output := by
  let template := HandshakeDuplicate.syn_received_ack complete.certificate.passivePending
  have core : server.current.core = (Handshake.passiveSeed complete.certificate.passivePending complete.certificate.ack.input).core := by
    exact clean.1.core.trans (congrArg Endpoint.State.core complete.certificate.passive.derived)
  let canonical : HandshakeDuplicate.BareAck (Output.reverse server.current.core.inbound)
      server.current.core.sendNext server.current.core.receiveNext server.current.core.window
      complete.certificate.passivePending.config.ipSendLimit := {
    output := template.output
    generated := by
      rw [core]
      simpa only [Handshake.passiveSeed, EstablishedReceive.State.window, List.length_nil, Nat.sub_zero] using template.generated
    fits := template.fits }
  exact ack.same_output canonical

theorem Phase.ackTemplate_kind (selected : phase.ackTemplate kind = some packet) : AckKind kind := by
  cases phase <;> cases kind <;> simp only [Phase.ackTemplate, reduceCtorEq] at selected
  all_goals first | exact Or.inl rfl | exact Or.inr rfl

theorem Phase.ackTemplate_profile (selected : phase.ackTemplate kind = some packet) : Handshake.Profile packet 16 := by
  cases phase with
  | idle | opened value => cases kind <;> cases selected
  | answered value =>
    cases kind <;> simp only [Phase.ackTemplate, reduceCtorEq, Option.some.injEq] at selected
    subst packet
    exact (HandshakeDuplicate.syn_received_ack value.pending).profile
  | acknowledged value client =>
    cases kind <;> simp only [Phase.ackTemplate, reduceCtorEq, Option.some.injEq] at selected
    · subst packet; exact (Acknowledged.output_shape value).profile
    · subst packet; exact (HandshakeDuplicate.syn_received_ack value.answered.pending).profile
  | complete value client server =>
    cases kind <;> simp only [Phase.ackTemplate, reduceCtorEq, Option.some.injEq] at selected
    · subst packet
      have fields := Output.emit_transport _ _ _ value.certificate.active.outputGenerated
      have payload := Output.emit_payload _ _ _ value.certificate.active.outputGenerated
      exact ⟨fields.2.2.2.2.1, by simpa only [Handshake.optionProfile, ↓reduceIte] using fields.2.2.2.2.2.2.1, payload⟩
    · subst packet; exact (HandshakeDuplicate.syn_received_ack value.certificate.passivePending).profile


theorem Phase.ackTemplate_header (selected : phase.ackTemplate kind = some packet) :
    phase.sourceHeader kind.actor = some packet.packet.header := by
  cases phase with
  | idle | opened value => cases kind <;> cases selected
  | answered value =>
    cases kind <;> simp only [Phase.ackTemplate, reduceCtorEq, Option.some.injEq] at selected
    subst packet
    exact congrArg some (Answered.reply_header value).symm
  | acknowledged value client =>
    cases kind <;> simp only [Phase.ackTemplate, reduceCtorEq, Option.some.injEq] at selected
    · subst packet; exact congrArg some (Acknowledged.output_header value).symm
    · subst packet; exact congrArg some (Answered.reply_header value.answered).symm
  | complete value client server =>
    cases kind <;> simp only [Phase.ackTemplate, reduceCtorEq, Option.some.injEq] at selected
    · subst packet
      exact congrArg some ((Output.emit_transport _ _ _ value.certificate.active.outputGenerated).1.trans
        (Completed.active_header value)).symm
    · subst packet
      exact congrArg some ((HandshakeDuplicate.syn_received_ack value.certificate.passivePending).transport.1.trans
        value.certificate.passivePending.output_fields.1.symm).symm

theorem Phase.AckFrame.refl (phase : Phase active passive) : AckFrame phase phase :=
  ⟨fun _ _ selected => selected⟩

theorem Phase.AckFrame.initial (phase : Phase active passive) : AckFrame .idle phase := by
  constructor
  intro kind packet selected
  cases kind <;> cases selected

theorem Phase.AckFrame.answered (answered : O.Answered active passive) :
    AckFrame (.opened answered.opened) (.answered answered) := by
  constructor
  intro kind packet selected
  cases kind <;> cases selected

theorem Phase.AckFrame.acknowledged (acknowledged : O.Acknowledged active passive)
    (client : PreData acknowledged.ready.seed) :
    AckFrame (.answered acknowledged.answered) (.acknowledged acknowledged client) := by
  constructor
  intro kind packet selected
  cases kind <;> first | exact selected | cases selected

theorem Phase.AckFrame.acknowledged_current (acknowledged : O.Acknowledged active passive)
    (before after : PreData acknowledged.ready.seed) :
    AckFrame (.acknowledged acknowledged before) (.acknowledged acknowledged after) := by
  constructor
  intro kind packet selected
  cases kind <;> exact selected

theorem Phase.AckFrame.complete_current (complete : O.Completed active passive)
    (beforeClient afterClient : PreData complete.certificate.activeSeed)
    (beforeServer afterServer : PreData complete.certificate.passiveSeed) :
    AckFrame (.complete complete beforeClient beforeServer) (.complete complete afterClient afterServer) := by
  constructor
  intro kind packet selected
  cases kind <;> exact selected

theorem Phase.AckFrame.finish (acknowledged : O.Acknowledged active passive) (index : Nat)
    (spec : X.DeliverySpec) (ack : X.Delivery acknowledged.ready.output spec)
    (ready : H.PassiveEstablished acknowledged.answered.pending ack.input)
    (computed : Handshake.synReceivedAck acknowledged.answered.pending ack.input = .ok ready)
    (ordered : acknowledged.answered.opened.index < acknowledged.answered.index ∧
      acknowledged.answered.index < acknowledged.index ∧ acknowledged.index < index)
    (client : PreData acknowledged.ready.seed) :
    AckFrame (.acknowledged acknowledged client)
      (.complete (finish acknowledged index spec ack ready computed ordered) client (PreData.initial ready.seed ready.valid)) := by
  constructor
  intro kind packet selected
  cases kind <;> exact selected

theorem Phase.AckFrame.trans {firstPhase middlePhase lastPhase : Phase active passive}
    (first : AckFrame firstPhase middlePhase) (second : AckFrame middlePhase lastPhase) :
    AckFrame firstPhase lastPhase :=
  ⟨fun kind packet selected => second.templates kind packet (first.templates kind packet selected)⟩

theorem AckInventory.initial : AckInventory (State.initial (active := active) (passive := passive)) := by
  constructor
  intro output member
  cases member

theorem AckInventory.reframe (inventory : AckInventory before)
    (frame : Phase.AckFrame before.phase after.phase) (same : after.emissions = before.emissions) : AckInventory after := by
  constructor
  intro output member kind
  rw [same] at member
  exact frame.templates _ _ (inventory.templates output member kind)

theorem AckInventory.publish (inventory : AckInventory state)
    (template : AckKind output.kind → state.phase.ackTemplate output.kind = some output.packet) :
    AckInventory (publish state output).state := by
  constructor
  intro selected member kind
  rcases List.mem_append.mp member with prior | fresh
  · exact inventory.templates selected prior kind
  · have same := List.mem_singleton.mp fresh
    subst selected
    exact template kind

theorem AckInventory.withTimer (inventory : AckInventory state) (actor : Side) (timer : T.State) (valid : timer.Valid) :
    AckInventory (state.withTimer actor timer valid) := by
  cases actor <;> exact ⟨inventory.templates⟩

theorem AckInventory.retainReceipt (inventory : AckInventory effect.state) (receipt : Receipt) :
    AckInventory (retainReceipt effect receipt).state := ⟨inventory.templates⟩

theorem AckInventory.source (inventory : AckInventory state) (found : state.source index = some output)
    (kind : AckKind output.kind) : state.phase.ackTemplate output.kind = some output.packet :=
  inventory.templates output (List.mem_of_find?_eq_some found) kind

theorem AckInventory.complete_finalAck (inventory : AckInventory state)
    (phase : state.phase = .complete complete client server) (member : output ∈ state.emissions)
    (kind : output.kind = .finalAck) : output.packet = complete.certificate.active.output := by
  have template := inventory.templates output member (Or.inl kind)
  rw [phase, kind, Phase.ackTemplate] at template
  exact (Option.some.inj template).symm

theorem AckInventory.complete_synReplyAck (inventory : AckInventory state)
    (phase : state.phase = .complete complete client server) (member : output ∈ state.emissions)
    (kind : output.kind = .synReplyAck) :
    output.packet = (HandshakeDuplicate.syn_received_ack complete.certificate.passivePending).output := by
  have template := inventory.templates output member (Or.inr kind)
  rw [phase, kind, Phase.ackTemplate] at template
  exact (Option.some.inj template).symm

end Netlib.Check.TCPHandshakeRecovery
