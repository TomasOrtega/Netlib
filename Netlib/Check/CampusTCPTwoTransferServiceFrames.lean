import Netlib.Check.CampusTCPTwoTransferAdmission

/-!
# Current lane frames from actual service

Data settles the peer lane and retains its window floor.
ACK service keeps the peer lane counts and window fixed.
-/

namespace Netlib.Check.CampusTCPTwoTransferServiceFrames

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressSender
open CampusTCPTwoProgressGatewayAt (ViewAt)
open CampusTCPTwoProgressGatewayState (sender_lane)
open CampusTCPTwoTransferState (Retained LiveAt Reserved PeerReserved Settled)
open CampusTCPTwoTransferNetwork (Service)
open CampusTCPTwoTransferAdmission (DataServed AckServed)
open CampusTCPTwoProgressServiceState (processingAt processingAt_admission processingAt_attachment)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {part : Part}
variable {item : Theory.Outstanding.Item (Ticket input.active input.passive)} {hit : FlowNAT.Hit} {session : Admission.Session}
variable {actual : Step input} {served : Served input} {emission : WireForwarding.Emission served.ticket.value.source.packet}
variable {emitted : served.evidence.output = some emission}

private theorem processing_before (value : Service current item hit session actual served emission emitted)
    (located : item.value.gateway = location) : served.before = beforeService input current.report.final location := by
  rw [value.facts.current, located]

private theorem processing_phase (view : ViewAt initial current location)
    (value : Service current item hit view.gateway.session actual served emission emitted) (located : item.value.gateway = location)
    (after : ViewAt initial value.move.after location)
    (processing : CampusTCPService.Processing (input.contextFor served.ticket.value.gateway)
      served.before served.ticket.value.source input.zone) (present : served.evidence.processing = some processing) :
    (processingAt processing (processing_before value located)).admitted.state.phase = .data after.gateway.session := by
  have phase := after.gateway.phase
  have afterBefore := value.after_before processing present
  rw [located] at afterBefore
  rw [afterBefore] at phase
  change processing.nextAdmission.phase = .data after.gateway.session at phase
  rw [← processingAt_admission processing (processing_before value located),
    CampusTCPRoundAdmission.Processing.committed_data _ view.gateway.session view.gateway.phase] at phase
  exact phase

theorem data_acknowledged (view : ViewAt initial current location)
    (value : Service current item ⟨view.gateway.session.entry.flow, sender.direction⟩ view.gateway.session actual served emission emitted)
    (located : item.value.gateway = location) (after : ViewAt initial value.move.after location) :
    (after.gateway.session.lane sender.direction).acknowledged = (view.gateway.session.lane sender.direction).acknowledged := by
  obtain ⟨processing, present, _, _, attached, _⟩ := value.facts.processing
  let selected := processingAt processing (processing_before value located)
  have direction : selected.prepared.attachment.direction = sender.direction := by rw [processingAt_attachment]; exact attached
  have fields := CampusTCPTwoProgressGatewayWindow.result_window_fields selected.admitted view.gateway.phase
    (processing_phase view value located after processing present)
  simpa only [direction, sender_lane] using fields.1

theorem data_peer_lane (view : ViewAt initial current location)
    (value : Service current item ⟨view.gateway.session.entry.flow, sender.direction⟩ view.gateway.session actual served emission emitted)
    (located : item.value.gateway = location) (after : ViewAt initial value.move.after location) :
    after.gateway.session.peer sender.direction =
      Admission.acknowledgedLane (view.gateway.session.peer sender.direction) served.ticket.value.source.packet.segment := by
  obtain ⟨processing, present, _, _, attached, _⟩ := value.facts.processing
  let selected := processingAt processing (processing_before value located)
  have direction : selected.prepared.attachment.direction = sender.direction := by rw [processingAt_attachment]; exact attached
  have fields := CampusTCPTwoProgressGatewayWindow.result_window_fields selected.admitted view.gateway.phase
    (processing_phase view value located after processing present)
  simpa only [direction, WireForwarding.Source.asInput] using fields.2.2

theorem data_settled (view : ViewAt initial current location)
    (value : Service current item ⟨view.gateway.session.entry.flow, sender.direction⟩ view.gateway.session actual served emission emitted)
    (located : item.value.gateway = location) (after : ViewAt initial value.move.after location)
    (ack : item.value.source.packet.segment.acknowledgment = (endpoint cut.endpoints sender).core.receiveNext) : Settled after := by
  intro _
  rw [data_peer_lane view value located after, Admission.acknowledgedLane_count, Admission.acknowledgedLane_observed]
  have selectedAck : served.ticket.value.source.packet.segment.acknowledgment = (endpoint cut.endpoints sender).core.receiveNext := by
    rw [value.facts.ticket]
    exact ack
  rw [view.data_ack_offset _ selectedAck, Nat.max_eq_right (view.gateway.session.peer_valid sender.direction).1]

theorem data_peer_reserved (view : ViewAt initial current location) (space : PeerReserved view)
    (value : Service current item ⟨view.gateway.session.entry.flow, sender.direction⟩ view.gateway.session actual served emission emitted)
    (located : item.value.gateway = location) (after : ViewAt initial value.move.after location)
    (fields : CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper) item.value.produced) :
    PeerReserved after := by
  rw [PeerReserved, data_peer_lane view value located after]
  apply CampusTCPTwoProgressGatewayPeerWindow.acknowledgedLane_floor _ _ _ space
  rw [value.facts.ticket]
  exact Nat.le_trans (Nat.min_le_right _ _) fields.window

theorem ack_peer_fields (view : ViewAt initial current location)
    (value : Service current item ⟨view.gateway.session.entry.flow, sender.other.direction⟩ view.gateway.session actual served emission emitted)
    (located : item.value.gateway = location) (after : ViewAt initial value.move.after location) :
    (after.gateway.session.peer sender.direction).acknowledged = (view.gateway.session.peer sender.direction).acknowledged ∧
      (after.gateway.session.peer sender.direction).peerWindow = (view.gateway.session.peer sender.direction).peerWindow := by
  obtain ⟨processing, present, _, _, attached, _⟩ := value.facts.processing
  let selected := processingAt processing (processing_before value located)
  have direction : selected.prepared.attachment.direction = sender.other.direction := by rw [processingAt_attachment]; exact attached
  have senderPeer : ∀ session : Admission.Session,
      session.sender selected.prepared.attachment.direction = session.peer sender.direction := by
    intro session
    rw [direction]
    cases sender <;> rfl
  have fields := CampusTCPTwoProgressGatewayWindow.result_window_fields selected.admitted view.gateway.phase
    (processing_phase view value located after processing present)
  exact ⟨by simpa only [senderPeer] using fields.1, by simpa only [senderPeer] using fields.2.1⟩

theorem ack_peer_reserved (view : ViewAt initial current location) (space : PeerReserved view)
    (value : Service current item ⟨view.gateway.session.entry.flow, sender.other.direction⟩ view.gateway.session actual served emission emitted)
    (located : item.value.gateway = location) (after : ViewAt initial value.move.after location) : PeerReserved after := by
  rw [PeerReserved, (ack_peer_fields view value located after).2]
  exact space

theorem ack_settled (view : ViewAt initial current location) (settled : Settled view)
    (value : Service current item ⟨view.gateway.session.entry.flow, sender.other.direction⟩ view.gateway.session actual served emission emitted)
    (located : item.value.gateway = location) (after : ViewAt initial value.move.after location)
    (lowerRun : after.ranges.lowerRun = view.ranges.lowerRun) (upperRun : after.ranges.upperRun = view.ranges.upperRun) : Settled after := by
  intro present
  rw [(ack_peer_fields view value located after).1, after.peer_observed, ← view.peer_observed]
  apply settled
  simpa only [lowerRun, upperRun] using present

theorem data_frames (view : ViewAt initial current location) (value : DataServed view item part actual)
    (located : item.value.gateway = location)
    (fields : CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper) item.value.produced)
    (space : PeerReserved view) :
    (value.next.gateway.session.lane sender.direction).acknowledged = (view.gateway.session.lane sender.direction).acknowledged ∧
      Settled value.next ∧ PeerReserved value.next :=
  ⟨data_acknowledged view value.value located value.next,
    data_settled view value.value located value.next fields.acknowledgment,
    data_peer_reserved view space value.value located value.next fields⟩

theorem ack_frames (view : ViewAt initial current location) (value : AckServed view item count actual)
    (located : item.value.gateway = location) (settled : Settled view) (space : PeerReserved view) :
    Settled value.next ∧ PeerReserved value.next ∧
      (value.next.gateway.session.peer sender.direction).acknowledged = (view.gateway.session.peer sender.direction).acknowledged ∧
      (value.next.gateway.session.peer sender.direction).peerWindow = (view.gateway.session.peer sender.direction).peerWindow :=
  ⟨ack_settled view settled value.value located value.next value.lowerRun value.upperRun,
    ack_peer_reserved view space value.value located value.next, ack_peer_fields view value.value located value.next⟩

theorem retained_after (retained : Retained cut current) (value : Service current item hit session actual served emission emitted) :
    Retained cut value.move.after :=
  ⟨retained.retained.trans value.move.retained, fun gateway => (retained.policy gateway).trans
    (CampusTCPRoundEnvironment.service_environment _ _ value.environment gateway)⟩

def live_after (live : LiveAt initial current location sent timeouts received)
    (value : Service current item hit session actual served emission emitted)
    (after : ViewAt initial value.move.after location) (space : Reserved after) :
    LiveAt initial value.move.after location sent timeouts received := by
  exact ⟨⟨retained_after live.anchor.toRetained value, by rw [value.endpoints]; exact live.anchor.guards⟩,
    by rw [value.endpoints]; exact live.senderFlight,
    by rw [value.endpoints]; exact live.receiverFacts,
    after, space, live.history.same (by rw [value.endpoints])⟩

end Netlib.Check.CampusTCPTwoTransferServiceFrames
