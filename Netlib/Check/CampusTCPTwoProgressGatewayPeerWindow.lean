import Netlib.Check.CampusTCPTwoProgressGatewayWindow

/-!
# The opposite gateway lane's window floor

Data service uses the same packet's advertisement.
ACK service keeps this lane's window unchanged.
-/

namespace Netlib.Check.CampusTCPTwoProgressGatewayPeerWindow

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressGatewayState
open CampusTCPTwoProgressNetwork (ServiceMove)
open CampusTCPTwoProgressServiceState (processingAt processingAt_admission processingAt_attachment)

theorem acknowledgedLane_floor (lane : Admission.Lane) (segment : Segment) (floor : Nat)
    (old : floor ≤ lane.peerWindow.val) (incoming : floor ≤ segment.window.val) :
    floor ≤ (Admission.acknowledgedLane lane segment).peerWindow.val := by
  unfold Admission.acknowledgedLane
  split <;> assumption

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}

def floor (initial : TwoWriteInitial cut sender gateway lower upper) : Nat :=
  min (initial.gatewayState.session.peer sender.direction).peerWindow.val
    (Endpoint.offeredWindow (endpoint cut.endpoints sender))

def Reserved (view : View initial current) : Prop :=
  floor initial ≤ (view.gateway.session.peer sender.direction).peerWindow.val

theorem initial_reserved (initial : TwoWriteInitial cut sender gateway lower upper) :
    Reserved (View.ofInitial initial) := Nat.min_le_left _ _

variable {item : Theory.Outstanding.Item (Ticket input.active input.passive)}
variable {hit : Protocol.FlowNAT.Hit} {session : Admission.Session} {actual : Step input} {served : Served input}
variable {emission : WireForwarding.Emission served.ticket.value.source.packet} {emitted : served.evidence.output = some emission}

private theorem processing_phase (view : View initial current)
    (value : ServiceMove initial current item hit session actual served emission emitted)
    (next : View initial value.move.after)
    (processing : CampusTCPService.Processing (input.contextFor served.ticket.value.gateway)
      served.before served.ticket.value.source input.zone) (present : value.ordinaryEvidence.processing = some processing)
    (previous : served.before = beforeService input current.report.final gateway) :
    (processingAt processing previous).admitted.state.phase = .data next.gateway.session := by
  have phase := next.gateway.phase
  rw [value.after_ordinary_before processing present] at phase
  change processing.nextAdmission.phase = .data next.gateway.session at phase
  rw [← processingAt_admission processing previous,
    CampusTCPRoundAdmission.Processing.committed_data (processingAt processing previous) view.gateway.session view.gateway.phase] at phase
  exact phase

theorem sender_service_reserved (view : View initial current) (space : Reserved view)
    (value : ServiceMove initial current item hit session actual served emission emitted)
    (next : View initial value.move.after) (direction : hit.direction = sender.direction)
    (incoming : floor initial ≤ served.ticket.value.source.packet.segment.window.val) : Reserved next := by
  obtain ⟨processing, present, _, _, attached, _⟩ := value.ordinary_processing
  have previous : served.before = beforeService input current.report.final gateway := by
    rw [value.facts.current, value.selected]
  let selected := processingAt processing previous
  have selectedDirection : selected.prepared.attachment.direction = sender.direction := by
    rw [processingAt_attachment]
    exact attached.trans direction
  have fields := CampusTCPTwoProgressGatewayWindow.result_window_fields selected.admitted view.gateway.phase
    (processing_phase view value next processing present previous)
  have peer : next.gateway.session.peer sender.direction =
      Admission.acknowledgedLane (view.gateway.session.peer sender.direction) served.ticket.value.source.packet.segment := by
    simpa only [selectedDirection, WireForwarding.Source.asInput] using fields.2.2
  rw [Reserved, peer]
  exact acknowledgedLane_floor _ _ _ space incoming

theorem receiver_service_reserved (view : View initial current) (space : Reserved view)
    (value : ServiceMove initial current item hit session actual served emission emitted)
    (next : View initial value.move.after) (direction : hit.direction = sender.other.direction) : Reserved next := by
  obtain ⟨processing, present, _, _, attached, _⟩ := value.ordinary_processing
  have previous : served.before = beforeService input current.report.final gateway := by
    rw [value.facts.current, value.selected]
  let selected := processingAt processing previous
  have selectedDirection : selected.prepared.attachment.direction = sender.other.direction := by
    rw [processingAt_attachment]
    exact attached.trans direction
  have peerLane : ∀ session : Admission.Session,
      session.sender selected.prepared.attachment.direction = session.peer sender.direction := by
    intro session
    rw [selectedDirection]
    cases sender <;> rfl
  have fields := CampusTCPTwoProgressGatewayWindow.result_window_fields selected.admitted view.gateway.phase
    (processing_phase view value next processing present previous)
  have window : (next.gateway.session.peer sender.direction).peerWindow =
      (view.gateway.session.peer sender.direction).peerWindow := by
    simpa only [peerLane] using fields.2.1
  rw [Reserved, window]
  exact space

end Netlib.Check.CampusTCPTwoProgressGatewayPeerWindow
