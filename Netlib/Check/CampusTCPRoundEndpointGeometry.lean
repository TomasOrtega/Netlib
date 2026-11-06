import Netlib.Check.CampusTCPRoundLocal
import Netlib.Check.CampusTCPDeliveryEnabled

/-!
# Endpoint packet guards for the first campus round

Startup and the actual setup operations supply the endpoint state.
The selected packet fields determine receive and full-ACK readiness.
-/

namespace Netlib.Check.CampusTCPRoundEndpointGeometry

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundSetup

variable {input : Input} {events : List Event}
variable {complete : H.Completed input.active input.passive}
variable {report : Report input events} {bytes : List UInt8}

theorem prepared_recovery (seed : Endpoint.State) (valid : seed.Valid) (empty : seed.core.sent = []) :
    Endpoint.RecoveryCoherent (preparedSeed seed) := by
  refine ⟨Recovery.initial_valid seed.effectiveMSS valid.2.2.2.2.1, rfl, ?_, valid.2.2.2.1⟩
  simp only [preparedSeed, ackState, recoveryState, Recovery.flight, Recovery.initial, empty,
    List.map_nil, List.sum_nil, List.length_nil]

theorem initial_ack_output (cursor : Seq) (capacity rmss outgoingMSS now : Nat) :
    AckReaction.outputState (AckReaction.initial cursor capacity rmss) now cursor capacity capacity outgoingMSS =
      AckReaction.initial cursor capacity rmss := by
  simp only [AckReaction.outputState, AckReaction.initial, ReceiveAdvertisement.commit,
    ReceiveAdvertisement.candidate, ReceiveAdvertisement.initial, ReceiveAdvertisement.State.window,
    Nat.sub_zero, Nat.sub_self, ite_self, Nat.zero_add, Theory.TimedReaction.initial,
    List.isEmpty_nil, ite_true]

theorem prepared_write_output (seed : Endpoint.State) (bytes : List UInt8) (received : seed.core.received = []) :
    Endpoint.outputState (Endpoint.writeState (preparedSeed seed) bytes) =
      Endpoint.writeState (preparedSeed seed) bytes := by
  have window : seed.core.window = seed.core.capacity := by
    simp only [EstablishedReceive.State.window, received, List.length_nil, Nat.sub_zero]
  simp only [Endpoint.outputState, Endpoint.writeState, preparedSeed, ackState, recoveryState,
    Option.map_some, window]
  rw [initial_ack_output]

theorem server_ready (start : PreparedStart report complete bytes) (packet : EstablishedReceive.Input)
    (tuple : packet.packet.header = complete.certificate.passiveSeed.core.inbound)
    (controls : EstablishedReceive.control packet.packet.segment = none)
    (ack : Flags.ack packet.packet.segment.flags = true)
    (sequence : packet.packet.segment.sequence = input.active.iss.add 1)
    (acknowledgment : packet.packet.segment.acknowledgment = input.passive.iss.add 1)
    (nonempty : packet.packet.segment.payload ≠ [])
    (fits : packet.packet.segment.payload.length ≤ input.passive.capacity) :
    ∃ recovery reaction, CampusTCPDeliveryEnabled.InOrderReady
      (endpoint start.next.endpoints .server) packet recovery reaction := by
  let seed := complete.certificate.passiveSeed
  let recovery := Recovery.initial seed.effectiveMSS
  let reaction := AckReaction.initial seed.core.receiveNext seed.core.capacity seed.localReceiveMSS.limit
  have received : seed.core.received = [] := complete.certificate.empty.2.2.2.2.2
  have sent : seed.core.sent = [] := complete.certificate.empty.2.2.2.2.1
  have store : seed.receiveStore = ReceiveStore.initial := complete.certificate.receiveStore_initial.2
  have fields := complete.certificate.initial_sequences
  refine ⟨recovery, reaction, ?_⟩
  constructor
  · rw [start.server]
    exact prepared_recovery seed complete.certificate.valid.2 sent
  · exact start.server_ack
  · rw [start.server]
    exact CampusTCPRoundLocal.prepared_storage seed received store
  · rw [start.server]; rfl
  · rw [start.server]; rfl
  · simp only [recovery, Recovery.State.SentBy, Recovery.initial, List.not_mem_nil, false_implies, implies_true]
  · rw [start.server]
    change seed.receiveStore.held = []
    rw [store]
    rfl
  · rw [start.server]
    exact tuple
  · exact controls
  · exact ack
  · rw [start.server]
    change packet.packet.segment.sequence = seed.core.receiveNext
    simpa only [seed, fields.2.2.2.2.2, complete.activeConfig] using sequence
  · exact nonempty
  · rw [start.server]
    simpa only [Endpoint.offeredWindow, preparedSeed, ackState, recoveryState, AckReaction.initial,
      AckReaction.State.window, ReceiveAdvertisement.State.window, ReceiveAdvertisement.initial, Nat.sub_zero,
      complete.certificate.configuration.2.2.2.1, complete.passiveConfig] using fits
  · rw [start.server]
    change Seq.distance seed.core.sendUna packet.packet.segment.acknowledgment ≤ seed.core.sent.length
    simp only [seed, fields.2.2.2.1, complete.passiveConfig, acknowledgment, Seq.distance_self,
      sent, List.length_nil, Nat.le_refl]

theorem client_ready (start : PreparedStart report complete bytes) (packet : EstablishedReceive.Input)
    (nonempty : bytes ≠ [])
    (mss : bytes.length ≤ Handshake.effectiveMSS input.active (Handshake.receiveOffer input.passive))
    (window : bytes.length ≤ input.passive.capacity)
    (tuple : packet.packet.header = complete.certificate.activeSeed.core.inbound)
    (controls : EstablishedReceive.control packet.packet.segment = none)
    (ack : Flags.ack packet.packet.segment.flags = true)
    (sequence : packet.packet.segment.sequence = input.passive.iss.add 1)
    (acknowledgment : packet.packet.segment.acknowledgment = (input.active.iss.add 1).add bytes.length)
    (empty : packet.packet.segment.payload = []) :
    ∃ recovery reaction, CampusTCPDeliveryEnabled.FullAckReady
      (Endpoint.sendState (endpoint start.next.endpoints .client) bytes.length) packet recovery reaction := by
  let seed := complete.certificate.activeSeed
  let before := Endpoint.writeState (preparedSeed seed) bytes
  let after := Endpoint.sendState before bytes.length
  let initial := Recovery.initial seed.effectiveMSS
  let recovery := Recovery.sent initial bytes.length
  let reaction := AckReaction.initial seed.core.receiveNext seed.core.capacity seed.localReceiveMSS.limit
  have valid : seed.Valid := complete.certificate.valid.1
  have received : seed.core.received = [] := complete.certificate.empty.2.2.1
  have sent : seed.core.sent = [] := complete.certificate.empty.2.1
  have pending : seed.pending = [] := complete.certificate.empty.1
  have store : seed.receiveStore = ReceiveStore.initial := complete.certificate.receiveStore_initial.1
  have positive : 0 < bytes.length := List.length_pos_iff.mpr nonempty
  have ready := start.send_ready nonempty mss window
  rw [start.client] at ready
  have size : bytes.length ≤ seed.effectiveMSS := ready.2.2.2.2.1
  have recoveryReady : Recovery.SendReady initial bytes.length := by
    exact ⟨positive, by simpa only [initial, Recovery.initial, Recovery.flight, List.map_nil, List.sum_nil,
      Nat.zero_add] using size, by simpa only [initial, Recovery.initial, Recovery.flight, List.map_nil,
        List.sum_nil, Nat.zero_add] using size⟩
  have recoveryValid : recovery.Valid := Recovery.sent_valid initial bytes.length
    (Recovery.initial_valid seed.effectiveMSS valid.2.2.2.2.1) recoveryReady
  have sentBytes : after.core.sent = bytes := by
    simp only [after, Endpoint.sendState, before, Endpoint.writeState, preparedSeed, ackState, recoveryState,
      pending, sent, List.nil_append, List.take_length]
  have bounded : bytes.length < Seq.modulus := by
    have capacity := complete.certificate.configuration.1
    have peer := complete.certificate.peer_capacities.1
    have windowBound := complete.certificate.valid.1.2.2.2.1
    rw [peer, complete.passiveConfig] at windowBound
    unfold Seq.modulus
    omega
  rw [start.client]
  change ∃ recovery reaction, CampusTCPDeliveryEnabled.FullAckReady after packet recovery reaction
  refine ⟨recovery, reaction, ?_⟩
  constructor
  · change recovery.Valid ∧ recovery.smss = seed.effectiveMSS ∧
      Recovery.flight recovery = after.core.sent.length ∧ Endpoint.AckWindowKnown after
    refine ⟨recoveryValid, rfl, ?_, ?_⟩
    · rw [sentBytes]
      change Recovery.flight (Recovery.sent initial bytes.length) = bytes.length
      rw [Recovery.sent_flight]
      simp only [initial, Recovery.flight, Recovery.initial, List.map_nil, List.sum_nil, Nat.zero_add]
    · exact valid.2.2.2.1
  · have prepared := Endpoint.sendState_ackPrepared (endpoint start.next.endpoints .client)
      bytes.length start.client_ack
    simpa only [start.client] using prepared
  · dsimp only [after, Endpoint.sendState, before]
    rw [prepared_write_output seed bytes received]
    change Endpoint.StorageCoherent (preparedSeed seed)
    exact CampusTCPRoundLocal.prepared_storage seed received store
  · rfl
  · dsimp only [after, Endpoint.sendState, before]
    rw [prepared_write_output seed bytes received]
    rfl
  · exact Recovery.sent_positive initial bytes.length (Recovery.initial_positive _) positive
  · rw [sentBytes]
    exact positive
  · change seed.receiveStore.held = []
    rw [store]; rfl
  · exact tuple
  · exact controls
  · exact ack
  · change packet.packet.segment.sequence = seed.core.receiveNext
    simpa only [seed, complete.certificate.initial_sequences.2.2.1, complete.passiveConfig] using sequence
  · exact empty
  · change Seq.distance seed.core.sendUna packet.packet.segment.acknowledgment = after.core.sent.length
    rw [sentBytes]
    simp only [seed, complete.certificate.initial_sequences.1, complete.activeConfig,
      acknowledgment, Seq.distance_add, Nat.mod_eq_of_lt bounded]

end Netlib.Check.CampusTCPRoundEndpointGeometry
