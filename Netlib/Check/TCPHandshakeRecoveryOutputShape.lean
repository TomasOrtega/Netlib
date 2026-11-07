import Netlib.Check.TCPHandshakeRecoveryInvariantCore

/-!
# Wire shapes of generated startup controls

The shape leaves tuple rewriting separate from local sequence coordinates.
PreData window markers do not change the byte cursors or advertised capacity.
-/

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

namespace Kind

def actor : Kind → Side
  | .syn | .finalAck => .active
  | .synAck | .synReplyAck => .passive

def flags : Kind → UInt8
  | .syn => 2
  | .synAck => 18
  | .finalAck | .synReplyAck => 16

def sequence (active passive : H.Local) : Kind → Seq
  | .syn => active.iss
  | .synAck => passive.iss
  | .finalAck => active.iss.add 1
  | .synReplyAck => passive.iss.add 1

def acknowledgment (active passive : H.Local) : Kind → Seq
  | .syn => Seq.ofNat 0
  | .synAck | .synReplyAck => active.iss.add 1
  | .finalAck => passive.iss.add 1

def capacity (active passive : H.Local) : Kind → Nat
  | .syn | .finalAck => active.capacity
  | .synAck | .synReplyAck => passive.capacity

def options (active passive : H.Local) : Kind → List UInt8
  | .syn => Handshake.options active
  | .synAck => Handshake.options passive
  | .finalAck | .synReplyAck => []

end Kind

structure PacketShape (active passive : H.Local) (actor : Side) (kind : Kind) (packet : H.Input) : Prop where
  actorEq : actor = kind.actor
  profile : Handshake.Profile packet kind.flags
  sequence : packet.packet.segment.sequence = kind.sequence active passive
  acknowledgment : packet.packet.segment.acknowledgment = kind.acknowledgment active passive
  capacity : packet.packet.segment.window.val = kind.capacity active passive
  options : packet.packet.segment.options = kind.options active passive

abbrev OutputShape (active passive : H.Local) (output : Emission) : Prop :=
  PacketShape active passive output.actor output.kind output.packet

def OutputInventory (state : State active passive) : Prop :=
  ∀ output ∈ state.emissions, OutputShape active passive output

variable {active passive : H.Local}
variable {state before after : State active passive} {output : Emission} {source index : Nat} {cause : Cause}

@[simp] theorem OutputInventory.initial : OutputInventory (State.initial (active := active) (passive := passive)) := by
  intro output member
  cases member

theorem PacketShape.payload (shape : PacketShape active passive actor kind packet) : packet.packet.segment.payload = [] :=
  shape.profile.2.2

theorem Opened.output_shape (opened : O.Opened active) : PacketShape active passive .active .syn opened.pending.output := by
  have config := (Handshake.activeOpen_fields _ _ _ _ opened.computed).1
  have fields := opened.pending.output_fields
  refine ⟨rfl, opened.pending.output_profile, ?_, fields.2.2.1, ?_, ?_⟩
  · exact fields.2.1.trans (congrArg (·.iss) config)
  · exact fields.2.2.2.1.trans (congrArg (·.capacity) config)
  · exact fields.2.2.2.2.2.1.trans (congrArg Handshake.options config)

theorem Answered.input_sequence (answered : O.Answered active passive) :
    answered.delivery.input.packet.segment.sequence = active.iss :=
  answered.delivery.path.fields.2.trans (Opened.output_shape (passive := passive) answered.opened).sequence

theorem Answered.output_shape (answered : O.Answered active passive) :
    PacketShape active passive .passive .synAck answered.pending.output := by
  have config := (Handshake.listenSyn_fields _ _ _ _ answered.computed).1
  have input := (Handshake.listenSyn_fields _ _ _ _ answered.computed).2.1
  have fields := answered.pending.output_fields
  refine ⟨rfl, answered.pending.output_profile, ?_, ?_, ?_, ?_⟩
  · exact fields.2.1.trans (congrArg (·.iss) config)
  · rw [fields.2.2.1, input, Answered.input_sequence answered]
    rfl
  · exact fields.2.2.2.1.trans (congrArg (·.capacity) config)
  · exact fields.2.2.2.2.2.1.trans (congrArg Handshake.options config)

theorem Answered.reply_shape (answered : O.Answered active passive) :
    PacketShape active passive .passive .synReplyAck (HandshakeDuplicate.syn_received_ack answered.pending).output := by
  have config := (Handshake.listenSyn_fields _ _ _ _ answered.computed).1
  have input := (Handshake.listenSyn_fields _ _ _ _ answered.computed).2.1
  have fields := (HandshakeDuplicate.syn_received_ack answered.pending).transport
  refine ⟨rfl, (HandshakeDuplicate.syn_received_ack answered.pending).profile, ?_, ?_, ?_, fields.2.2.2.2.2.1⟩
  · rw [fields.2.1, config]
    rfl
  · rw [fields.2.2.1, input, Answered.input_sequence answered]
    rfl
  · exact fields.2.2.2.1.trans (congrArg (·.capacity) config)


theorem Acknowledged.input_sequence (acknowledged : O.Acknowledged active passive) :
    acknowledged.delivery.input.packet.segment.sequence = passive.iss :=
  acknowledged.delivery.path.fields.2.trans (Answered.output_shape acknowledged.answered).sequence

theorem Acknowledged.seed_coordinates (acknowledged : O.Acknowledged active passive) :
    acknowledged.ready.seed.core.sendNext = active.iss.add 1 ∧
      acknowledged.ready.seed.core.receiveNext = passive.iss.add 1 ∧
      acknowledged.ready.seed.core.capacity = active.capacity := by
  have config := (Handshake.activeOpen_fields _ _ _ _ acknowledged.answered.opened.computed).1
  rw [acknowledged.ready.derived]
  simp only [Handshake.activeSeed, config, Acknowledged.input_sequence acknowledged]
  trivial

theorem Acknowledged.output_shape (acknowledged : O.Acknowledged active passive) :
    PacketShape active passive .active .finalAck acknowledged.ready.output := by
  have fields := Output.emit_transport _ _ _ acknowledged.ready.outputGenerated
  have payload := Output.emit_payload _ _ _ acknowledged.ready.outputGenerated
  have coordinates := Acknowledged.seed_coordinates acknowledged
  have window : acknowledged.ready.seed.core.window = active.capacity := by
    rw [acknowledged.ready.derived]
    simp only [EstablishedReceive.State.window, Handshake.activeSeed, List.length_nil, Nat.sub_zero]
    exact congrArg (·.capacity) (Handshake.activeOpen_fields _ _ _ _ acknowledged.answered.opened.computed).1
  refine ⟨rfl, ?_, fields.2.1.trans coordinates.1, fields.2.2.1.trans coordinates.2.1,
    fields.2.2.2.1.trans window, fields.2.2.2.2.2.2.1⟩
  exact ⟨fields.2.2.2.2.1, by simpa only [Handshake.optionProfile, Kind.flags, ite_true] using fields.2.2.2.2.2.2.1, payload⟩

theorem PreDataClean.window (clean : PreDataClean seed current) : current.current.core.window = seed.core.capacity := by
  simp only [EstablishedReceive.State.window, clean.fields.2.2.2.2.2.1, List.length_nil, Nat.sub_zero]
  exact congrArg EstablishedReceive.State.capacity clean.1.core

theorem PacketShape.bare_ack (ack : HandshakeDuplicate.BareAck header sendNext receiveNext window ipLimit)
    (actorEq : actor = kind.actor) (flags : kind.flags = 16) (options : kind.options active passive = [])
    (sequence : sendNext = kind.sequence active passive)
    (acknowledgment : receiveNext = kind.acknowledgment active passive)
    (capacity : window = kind.capacity active passive) : PacketShape active passive actor kind ack.output := by
  have fields := ack.transport
  refine ⟨actorEq, ?_, fields.2.1.trans sequence, fields.2.2.1.trans acknowledgment,
    fields.2.2.2.1.trans capacity, fields.2.2.2.2.2.1.trans options.symm⟩
  rw [flags]
  exact ack.profile

theorem Acknowledged.current_ack_shape (acknowledged : O.Acknowledged active passive) {client : PreData acknowledged.ready.seed}
    (clean : PreDataClean acknowledged.ready.seed client)
    (ack : HandshakeDuplicate.BareAck (Output.reverse client.current.core.inbound)
      client.current.core.sendNext client.current.core.receiveNext client.current.core.window client.current.ipSendLimit) :
    PacketShape active passive .active .finalAck ack.output := by
  have coordinates := Acknowledged.seed_coordinates acknowledged
  apply PacketShape.bare_ack (active := active) (passive := passive) (actor := .active) (kind := .finalAck) ack rfl rfl rfl
  · exact (congrArg EstablishedReceive.State.sendNext clean.1.core).trans coordinates.1
  · exact (congrArg EstablishedReceive.State.receiveNext clean.1.core).trans coordinates.2.1
  · exact clean.window.trans coordinates.2.2

theorem Completed.current_active_ack_shape (complete : O.Completed active passive) {client : PreData complete.certificate.activeSeed}
    (clean : PreDataClean complete.certificate.activeSeed client)
    (ack : HandshakeDuplicate.BareAck (Output.reverse client.current.core.inbound)
      client.current.core.sendNext client.current.core.receiveNext client.current.core.window client.current.ipSendLimit) :
    PacketShape active passive .active .finalAck ack.output := by
  have coordinates := complete.certificate.initial_sequences
  have capacity := complete.certificate.configuration.1
  rw [complete.activeConfig, complete.passiveConfig] at coordinates
  rw [complete.activeConfig] at capacity
  apply PacketShape.bare_ack (active := active) (passive := passive) (actor := .active) (kind := .finalAck) ack rfl rfl rfl
  · exact (congrArg EstablishedReceive.State.sendNext clean.1.core).trans coordinates.2.1
  · exact (congrArg EstablishedReceive.State.receiveNext clean.1.core).trans coordinates.2.2.1
  · exact clean.window.trans capacity

theorem Completed.current_passive_ack_shape (complete : O.Completed active passive) {server : PreData complete.certificate.passiveSeed}
    (clean : PreDataClean complete.certificate.passiveSeed server)
    (ack : HandshakeDuplicate.BareAck (Output.reverse server.current.core.inbound)
      server.current.core.sendNext server.current.core.receiveNext server.current.core.window server.current.ipSendLimit) :
    PacketShape active passive .passive .synReplyAck ack.output := by
  have coordinates := complete.certificate.initial_sequences
  have capacity := complete.certificate.configuration.2.2.2.1
  rw [complete.activeConfig, complete.passiveConfig] at coordinates
  rw [complete.passiveConfig] at capacity
  apply PacketShape.bare_ack (active := active) (passive := passive) (actor := .passive) (kind := .synReplyAck) ack rfl rfl rfl
  · exact (congrArg EstablishedReceive.State.sendNext clean.1.core).trans coordinates.2.2.2.2.1
  · exact (congrArg EstablishedReceive.State.receiveNext clean.1.core).trans coordinates.2.2.2.2.2
  · exact clean.window.trans capacity


theorem PacketShape.kind_fields (shape : PacketShape active passive actor kind packet) :
    (kind = .syn ↔ actor = .active ∧ packet.packet.segment.flags = 2) ∧
      (kind = .synAck ↔ actor = .passive ∧ packet.packet.segment.flags = 18) ∧
      (kind = .finalAck ↔ actor = .active ∧ packet.packet.segment.flags = 16) ∧
      (kind = .synReplyAck ↔ actor = .passive ∧ packet.packet.segment.flags = 16) := by
  have actorEq := shape.actorEq
  have flags := shape.profile.1
  cases kind <;> simp_all only [Kind.actor, Kind.flags, reduceCtorEq, true_and, and_true, false_and, iff_self] <;> decide

theorem OutputShape.copy (shape : OutputShape active passive output) :
    OutputShape active passive { output with index := index, cause := cause } := shape

theorem OutputInventory.source_shape (inventory : OutputInventory state) (found : state.source source = some output) :
    OutputShape active passive output := inventory output (List.mem_of_find?_eq_some found)

theorem OutputInventory.frame (inventory : OutputInventory before) (same : after.emissions = before.emissions) :
    OutputInventory after := by
  intro output member
  rw [same] at member
  exact inventory output member

theorem OutputInventory.publish (inventory : OutputInventory state) (shape : OutputShape active passive output) :
    OutputInventory (publish state output).state := by
  intro selected member
  rcases List.mem_append.mp member with prior | fresh
  · exact inventory selected prior
  · have same : selected = output := List.mem_singleton.mp fresh
    exact same ▸ shape

end Netlib.Check.TCPHandshakeRecovery
