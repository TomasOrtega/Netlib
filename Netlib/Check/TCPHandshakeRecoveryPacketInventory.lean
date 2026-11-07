import Netlib.Check.TCPHandshakeRecoveryOutputShape

/-!
# Headers and exact control templates in startup history

Each phase retains the actual OPEN and first passive response.
The complete phase relates their headers to the checked endpoint seeds.
-/

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

namespace Phase

def sourceHeader : Phase active passive → Side → Option Packet.Header
  | .idle, _ => none
  | .opened value, .active => some value.pending.output.packet.header
  | .opened _, .passive => none
  | .answered value, .active => some value.opened.pending.output.packet.header
  | .answered value, .passive => some value.pending.output.packet.header
  | .acknowledged value _, .active => some value.answered.opened.pending.output.packet.header
  | .acknowledged value _, .passive => some value.answered.pending.output.packet.header
  | .complete value _ _, .active => some value.certificate.activePending.output.packet.header
  | .complete value _ _, .passive => some value.certificate.passivePending.output.packet.header

def controlTemplate : Phase active passive → Kind → Option H.Input
  | .opened value, .syn => some value.pending.output
  | .answered value, .syn => some value.opened.pending.output
  | .answered value, .synAck => some value.pending.output
  | .acknowledged value _, .syn => some value.answered.opened.pending.output
  | .acknowledged value _, .synAck => some value.answered.pending.output
  | .complete value _ _, .syn => some value.certificate.activePending.output
  | .complete value _ _, .synAck => some value.certificate.passivePending.output
  | _, _ => none

structure PacketFrame (before after : Phase active passive) : Prop where
  headers : ∀ actor header, before.sourceHeader actor = some header → after.sourceHeader actor = some header
  templates : ∀ kind packet, before.controlTemplate kind = some packet → after.controlTemplate kind = some packet

end Phase

def TemplateKind (kind : Kind) : Prop := kind = .syn ∨ kind = .synAck

structure PacketInventory (state : State active passive) : Prop where
  headers : ∀ output ∈ state.emissions, state.phase.sourceHeader output.actor = some output.packet.packet.header
  templates : ∀ output ∈ state.emissions, TemplateKind output.kind →
    state.phase.controlTemplate output.kind = some output.packet

variable {active passive : H.Local}
variable {before after state : State active passive} {output : Emission}

private theorem reverse_twice (header : Packet.Header) : Output.reverse (Output.reverse header) = header := by
  cases header
  rfl

theorem Acknowledged.seed_header (acknowledged : O.Acknowledged active passive) :
    Output.reverse acknowledged.ready.seed.core.inbound = acknowledged.answered.opened.pending.output.packet.header := by
  rw [acknowledged.ready.derived]
  change Output.reverse (Handshake.inbound _ _) = _
  rw [Handshake.inbound, reverse_twice, acknowledged.answered.opened.pending.output_fields.1]

theorem Acknowledged.output_header (acknowledged : O.Acknowledged active passive) :
    acknowledged.ready.output.packet.header = acknowledged.answered.opened.pending.output.packet.header :=
  (Output.emit_transport _ _ _ acknowledged.ready.outputGenerated).1.trans (Acknowledged.seed_header acknowledged)

theorem Answered.reply_header (answered : O.Answered active passive) :
    (HandshakeDuplicate.syn_received_ack answered.pending).output.packet.header = answered.pending.output.packet.header :=
  (HandshakeDuplicate.syn_received_ack answered.pending).transport.1.trans answered.pending.output_fields.1.symm

theorem Completed.active_header (complete : O.Completed active passive) :
    Output.reverse complete.certificate.activeSeed.core.inbound = complete.certificate.activePending.output.packet.header := by
  rw [HandshakeExchange.Complete.activeSeed, complete.certificate.active.derived]
  change Output.reverse (Handshake.inbound _ _) = _
  rw [Handshake.inbound, reverse_twice, complete.certificate.activePending.output_fields.1]

theorem Completed.passive_header (complete : O.Completed active passive) :
    Output.reverse complete.certificate.passiveSeed.core.inbound = complete.certificate.passivePending.output.packet.header := by
  rw [HandshakeExchange.Complete.passiveSeed, complete.certificate.passive.derived]
  exact complete.certificate.passivePending.output_fields.1.symm

theorem Acknowledged.current_ack_header (acknowledged : O.Acknowledged active passive)
    {client : PreData acknowledged.ready.seed} (clean : PreDataClean acknowledged.ready.seed client)
    (ack : HandshakeDuplicate.BareAck (Output.reverse client.current.core.inbound)
      client.current.core.sendNext client.current.core.receiveNext client.current.core.window client.current.ipSendLimit) :
    ack.output.packet.header = acknowledged.answered.opened.pending.output.packet.header := by
  rw [ack.transport.1, clean.1.core]
  exact Acknowledged.seed_header acknowledged

theorem Completed.current_active_ack_header (complete : O.Completed active passive)
    {client : PreData complete.certificate.activeSeed} (clean : PreDataClean complete.certificate.activeSeed client)
    (ack : HandshakeDuplicate.BareAck (Output.reverse client.current.core.inbound)
      client.current.core.sendNext client.current.core.receiveNext client.current.core.window client.current.ipSendLimit) :
    ack.output.packet.header = complete.certificate.activePending.output.packet.header := by
  rw [ack.transport.1, clean.1.core]
  exact Completed.active_header complete

theorem Completed.current_passive_ack_header (complete : O.Completed active passive)
    {server : PreData complete.certificate.passiveSeed} (clean : PreDataClean complete.certificate.passiveSeed server)
    (ack : HandshakeDuplicate.BareAck (Output.reverse server.current.core.inbound)
      server.current.core.sendNext server.current.core.receiveNext server.current.core.window server.current.ipSendLimit) :
    ack.output.packet.header = complete.certificate.passivePending.output.packet.header := by
  rw [ack.transport.1, clean.1.core]
  exact Completed.passive_header complete

theorem Phase.PacketFrame.refl (phase : Phase active passive) : PacketFrame phase phase :=
  ⟨fun _ _ present => present, fun _ _ present => present⟩

theorem Phase.PacketFrame.initial (phase : Phase active passive) : PacketFrame .idle phase := by
  constructor
  · intro actor header present; cases present
  · intro kind packet present; cases present

theorem Phase.PacketFrame.answered (answered : O.Answered active passive) :
    PacketFrame (.opened answered.opened) (.answered answered) := by
  constructor
  · intro actor header present
    cases actor
    · exact present
    · cases present
  · intro kind packet present
    cases kind <;> first | exact present | cases present

theorem Phase.PacketFrame.acknowledged (acknowledged : O.Acknowledged active passive)
    (client : PreData acknowledged.ready.seed) :
    PacketFrame (.answered acknowledged.answered) (.acknowledged acknowledged client) :=
by
  constructor
  · intro actor header present
    cases actor <;> exact present
  · intro kind packet present
    cases kind <;> exact present

theorem Phase.PacketFrame.acknowledged_current (acknowledged : O.Acknowledged active passive)
    (before after : PreData acknowledged.ready.seed) :
    PacketFrame (.acknowledged acknowledged before) (.acknowledged acknowledged after) :=
by
  constructor
  · intro actor header present
    cases actor <;> exact present
  · intro kind packet present
    cases kind <;> exact present

theorem Phase.PacketFrame.complete_current (complete : O.Completed active passive)
    (beforeClient afterClient : PreData complete.certificate.activeSeed)
    (beforeServer afterServer : PreData complete.certificate.passiveSeed) :
    PacketFrame (.complete complete beforeClient beforeServer) (.complete complete afterClient afterServer) :=
by
  constructor
  · intro actor header present
    cases actor <;> exact present
  · intro kind packet present
    cases kind <;> exact present

theorem Phase.PacketFrame.finish (acknowledged : O.Acknowledged active passive) (index : Nat)
    (spec : X.DeliverySpec) (ack : X.Delivery acknowledged.ready.output spec)
    (ready : H.PassiveEstablished acknowledged.answered.pending ack.input)
    (computed : Handshake.synReceivedAck acknowledged.answered.pending ack.input = .ok ready)
    (ordered : acknowledged.answered.opened.index < acknowledged.answered.index ∧
      acknowledged.answered.index < acknowledged.index ∧ acknowledged.index < index)
    (client : PreData acknowledged.ready.seed) :
    PacketFrame (.acknowledged acknowledged client)
      (.complete (finish acknowledged index spec ack ready computed ordered) client (PreData.initial ready.seed ready.valid)) :=
by
  constructor
  · intro actor header present
    cases actor <;> exact present
  · intro kind packet present
    cases kind <;> exact present

theorem PacketInventory.initial : PacketInventory (State.initial (active := active) (passive := passive)) := by
  constructor
  · intro output member; cases member
  · intro output member; cases member

theorem PacketInventory.reframe (inventory : PacketInventory before)
    (frame : Phase.PacketFrame before.phase after.phase) (same : after.emissions = before.emissions) : PacketInventory after := by
  constructor
  · intro output member
    rw [same] at member
    exact frame.headers _ _ (inventory.headers output member)
  · intro output member control
    rw [same] at member
    exact frame.templates _ _ (inventory.templates output member control)

theorem PacketInventory.publish (inventory : PacketInventory state)
    (header : state.phase.sourceHeader output.actor = some output.packet.packet.header)
    (template : TemplateKind output.kind → state.phase.controlTemplate output.kind = some output.packet) :
    PacketInventory (publish state output).state := by
  constructor
  · intro selected member
    rcases List.mem_append.mp member with prior | fresh
    · exact inventory.headers selected prior
    · have same : selected = output := List.mem_singleton.mp fresh
      exact same ▸ header
  · intro selected member control
    rcases List.mem_append.mp member with prior | fresh
    · exact inventory.templates selected prior control
    · have same : selected = output := List.mem_singleton.mp fresh
      subst selected
      exact template control


theorem Phase.PacketFrame.trans {firstPhase middlePhase lastPhase : Phase active passive}
    (first : PacketFrame firstPhase middlePhase) (second : PacketFrame middlePhase lastPhase) :
    PacketFrame firstPhase lastPhase :=
  ⟨fun actor header present => second.headers actor header (first.headers actor header present),
    fun kind packet present => second.templates kind packet (first.templates kind packet present)⟩

theorem PacketInventory.source_header (inventory : PacketInventory state) (found : state.source index = some output) :
    state.phase.sourceHeader output.actor = some output.packet.packet.header :=
  inventory.headers output (List.mem_of_find?_eq_some found)

theorem PacketInventory.complete_active_header (inventory : PacketInventory state)
    (phase : state.phase = .complete complete client server) (member : output ∈ state.emissions)
    (actor : output.actor = .active) :
    output.packet.packet.header = Output.reverse complete.certificate.activeSeed.core.inbound := by
  have header := inventory.headers output member
  rw [phase, actor, Phase.sourceHeader] at header
  exact (Option.some.inj header).symm.trans (Completed.active_header complete).symm

theorem PacketInventory.complete_passive_header (inventory : PacketInventory state)
    (phase : state.phase = .complete complete client server) (member : output ∈ state.emissions)
    (actor : output.actor = .passive) :
    output.packet.packet.header = Output.reverse complete.certificate.passiveSeed.core.inbound := by
  have header := inventory.headers output member
  rw [phase, actor, Phase.sourceHeader] at header
  exact (Option.some.inj header).symm.trans (Completed.passive_header complete).symm

theorem PacketInventory.complete_syn (inventory : PacketInventory state)
    (phase : state.phase = .complete complete client server) (member : output ∈ state.emissions)
    (kind : output.kind = .syn) : output.packet = complete.certificate.activePending.output := by
  have template := inventory.templates output member (Or.inl kind)
  rw [phase, kind, Phase.controlTemplate] at template
  exact (Option.some.inj template).symm

theorem PacketInventory.complete_synAck (inventory : PacketInventory state)
    (phase : state.phase = .complete complete client server) (member : output ∈ state.emissions)
    (kind : output.kind = .synAck) : output.packet = complete.certificate.passivePending.output := by
  have template := inventory.templates output member (Or.inr kind)
  rw [phase, kind, Phase.controlTemplate] at template
  exact (Option.some.inj template).symm

end Netlib.Check.TCPHandshakeRecovery
