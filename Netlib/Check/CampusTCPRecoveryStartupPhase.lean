import Netlib.Check.CampusTCPRecoveryStartupGeometry
import Netlib.Check.TCPHandshakeRecoveryOutputShape
import Netlib.Check.CampusTCPStartupAlignment

/-!
# Coordinates through actual mixed startup admission

Control learning uses the real admitted input. Stutters retain their exact
admission witness, and data ACKs retain the current window update.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupPhase

open Protocol Protocol.TCP

namespace C
export TCPHandshakeRecovery (Side Kind PacketShape)
end C

namespace G
export CampusTCPRecoveryStartupGeometry (Geometry LaneGeometry)
end G

def sideDirection : C.Side → FlowNAT.Direction
  | .active => .original
  | .passive => .reply

def directionCapacity (active passive : Handshake.Local) : FlowNAT.Direction → Nat
  | .original => active.capacity
  | .reply => passive.capacity

structure SynCoordinates (active : Handshake.Local) (iss : Seq) (window : InternetChecksum.Word) (mss : MSS.Offer) : Prop where
  sequence : iss = active.iss
  capacity : window.val = active.capacity
  offer : mss = Handshake.receiveOffer active

structure SynAckCoordinates (active passive : Handshake.Local) (clientISS : Seq) (clientWindow : InternetChecksum.Word)
    (serverISS : Seq) (serverWindow : InternetChecksum.Word) (clientMSS serverMSS : MSS.Offer) : Prop where
  client : SynCoordinates active clientISS clientWindow clientMSS
  server : SynCoordinates passive serverISS serverWindow serverMSS

def Coordinates (active passive : Handshake.Local) : Admission.Phase → Prop
  | .empty => True
  | .syn _ iss window mss => SynCoordinates active iss window mss
  | .synAck _ clientISS clientWindow serverISS serverWindow clientMSS serverMSS =>
    SynAckCoordinates active passive clientISS clientWindow serverISS serverWindow clientMSS serverMSS
  | .data session => G.Geometry active passive session

variable {active passive : Handshake.Local} {actor : C.Side} {kind : C.Kind} {packet : EstablishedReceive.Input}

theorem PacketShape.window_direction (shape : C.PacketShape active passive actor kind packet)
    (role : direction = sideDirection actor) :
    packet.packet.segment.window.val = directionCapacity active passive direction := by
  subst direction
  rw [shape.capacity, shape.actorEq]
  cases kind <;> rfl

private theorem syn_kind (shape : C.PacketShape active passive actor kind packet)
    (flags : packet.packet.segment.flags = 2) : kind = .syn := by
  have same := shape.profile.1.symm.trans flags
  cases kind with
  | syn => rfl
  | synAck => exact False.elim ((by decide : (18 : UInt8) ≠ 2) same)
  | finalAck | synReplyAck => exact False.elim ((by decide : (16 : UInt8) ≠ 2) same)

private theorem synAck_kind (shape : C.PacketShape active passive actor kind packet)
    (flags : packet.packet.segment.flags = 18) : kind = .synAck := by
  have same := shape.profile.1.symm.trans flags
  cases kind with
  | syn => exact False.elim ((by decide : (2 : UInt8) ≠ 18) same)
  | synAck => rfl
  | finalAck | synReplyAck => exact False.elim ((by decide : (16 : UInt8) ≠ 18) same)

theorem Coordinates.legacy (prior : Coordinates active passive before.phase)
    (result : Admission.Result before packet lifecycle prepared) (shape : C.PacketShape active passive actor kind packet)
    (role : prepared.attachment.direction = sideDirection actor) :
    Coordinates active passive result.state.phase := by
  cases before with
  | mk phase observations =>
    cases phase with
    | empty =>
      have kindEq := syn_kind shape result.admitted.2.2.1
      subst kind
      obtain ⟨offer, read, computed⟩ := result.learned_syn rfl
      rw [shape.options, TCPHandshakeRecovery.Kind.options, Handshake.options_selected] at read
      rw [computed]
      exact ⟨shape.sequence, shape.capacity, (Except.ok.inj read).symm⟩
    | syn entry iss window mss =>
      have kindEq := synAck_kind shape result.admitted.2.2.2.1.1
      subst kind
      obtain ⟨offer, read, computed⟩ := result.learned_synAck rfl
      rw [shape.options, TCPHandshakeRecovery.Kind.options, Handshake.options_selected] at read
      rw [computed]
      exact ⟨prior, shape.sequence, shape.capacity, (Except.ok.inj read).symm⟩
    | synAck entry clientISS clientWindow serverISS serverWindow clientMSS serverMSS =>
      have original := result.admitted.2.2.1
      have activeActor : actor = .active := by
        rw [original] at role
        cases actor
        · rfl
        · cases role
      have flags := result.admitted.2.2.2.1.1
      have kindEq := shape.kind_fields.2.2.1.mpr ⟨activeActor, flags⟩
      subst kind
      obtain ⟨after, computed, selected, originalLane, replyLane, clientOffer, serverOffer⟩ :=
        result.established_lanes rfl
      rw [computed]
      refine ⟨?_, ?_, clientOffer.trans prior.client.offer, serverOffer.trans prior.server.offer⟩
      · rw [originalLane]
        exact ⟨congrArg (fun iss : Seq => iss.add 1) prior.client.sequence, rfl, rfl, prior.server.capacity⟩
      · rw [replyLane]
        exact ⟨congrArg (fun iss : Seq => iss.add 1) prior.server.sequence, rfl, rfl, shape.capacity⟩
    | data session =>
      obtain ⟨after, computed, _, geometry⟩ := prior.legacy_empty result rfl shape.payload (PacketShape.window_direction shape role)
      rw [computed]
      exact geometry

theorem Coordinates.admitted (prior : Coordinates active passive before.phase)
    (result : AdmissionExecution.Result mode before packet lifecycle prepared)
    (shape : C.PacketShape active passive actor kind packet) (role : prepared.attachment.direction = sideDirection actor) :
    Coordinates active passive (AdmissionExecution.Result.state result).phase := by
  rcases AdmissionExecution.Result.legacy_or_stutter result with legacy | ⟨sameMode, stutter⟩
  · have next := prior.legacy (AdmissionExecution.Result.asLegacy result legacy) shape role
    simpa only [AdmissionExecution.Result.asLegacy_state] using next
  · subst mode
    have same := result.phase.trans (AdmissionStartupRecovery.nextPhase_stutter stutter result.admitted)
    rw [same]
    exact prior

end Netlib.Check.CampusTCPRecoveryStartupPhase
