import Netlib.Check.CampusTCPTwoProgressGatewayPeerWindow
import Netlib.Check.CampusTCPTwoProgressGatewayRanges

/-!
# Opposite-lane settlement from actual data service

The stored data ACK covers the unchanged peer frontier.
Later opposite-direction ACK service preserves that settlement.
-/

namespace Netlib.Check.CampusTCPTwoProgressGatewayPeerSettled

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressGatewayState
open CampusTCPTwoProgressNetwork (ServiceMove)
open CampusTCPTwoProgressServiceState (processingAt processingAt_admission processingAt_attachment)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current next : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}

def Settled (view : View initial current) : Prop :=
  (view.ranges.lowerRun.isSome = true ∨ view.ranges.upperRun.isSome = true) →
    (view.gateway.session.peer sender.direction).acknowledged = (view.gateway.session.peer sender.direction).observed

theorem initial_settled (initial : TwoWriteInitial cut sender gateway lower upper) :
    Settled (View.ofInitial initial) := by
  intro present
  cases present with
  | inl impossible => cases impossible
  | inr impossible => cases impossible

theorem same_service (before : View initial current) (after : View initial next) (settled : Settled before)
    (same : beforeService input next.report.final gateway = beforeService input current.report.final gateway) : Settled after := by
  have ranges := before.ranges_same after same
  have phase := after.gateway.phase
  rw [same, before.gateway.phase] at phase
  have session : after.gateway.session = before.gateway.session := (Admission.Phase.data.inj phase).symm
  intro present
  rw [session]
  apply settled
  simpa only [ranges.1, ranges.2] using present

variable {item : Theory.Outstanding.Item (Ticket input.active input.passive)}
variable {hit : Protocol.FlowNAT.Hit} {session : Admission.Session} {actual : Step input} {served : Served input}
variable {emission : WireForwarding.Emission served.ticket.value.source.packet} {emitted : served.evidence.output = some emission}

private theorem processing_phase (view : View initial current)
    (value : ServiceMove initial current item hit session actual served emission emitted)
    (next : View initial value.move.after)
    (processing : CampusTCPService.Processing (input.contextFor served.ticket.value.gateway)
      served.before served.ticket.value.source input.zone) (present : served.evidence.processing = some processing)
    (previous : served.before = beforeService input current.report.final gateway) :
    (processingAt processing previous).admitted.state.phase = .data next.gateway.session := by
  have phase := next.gateway.phase
  rw [value.after_before processing present] at phase
  change processing.nextAdmission.phase = .data next.gateway.session at phase
  rw [← processingAt_admission processing previous,
    CampusTCPRoundAdmission.Processing.committed_data (processingAt processing previous) view.gateway.session view.gateway.phase] at phase
  exact phase

theorem sender_service_settled (view : View initial current)
    (value : ServiceMove initial current item hit session actual served emission emitted)
    (next : View initial value.move.after) (direction : hit.direction = sender.direction)
    (ack : served.ticket.value.source.packet.segment.acknowledgment = (endpoint cut.endpoints sender).core.receiveNext) :
    Settled next := by
  obtain ⟨processing, present, _, _, attached, _⟩ := value.facts.processing
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
  intro _
  rw [peer, Admission.acknowledgedLane_count, Admission.acknowledgedLane_observed,
    view.data_ack_offset _ ack, Nat.max_eq_right (view.gateway.session.peer_valid sender.direction).1]

theorem receiver_service_settled (view : View initial current) (settled : Settled view)
    (value : ServiceMove initial current item hit session actual served emission emitted)
    (next : View initial value.move.after) (direction : hit.direction = sender.other.direction)
    (lowerRun : next.ranges.lowerRun = view.ranges.lowerRun)
    (upperRun : next.ranges.upperRun = view.ranges.upperRun) : Settled next := by
  obtain ⟨processing, present, _, _, attached, _⟩ := value.facts.processing
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
  have acknowledged : (next.gateway.session.peer sender.direction).acknowledged =
      (view.gateway.session.peer sender.direction).acknowledged := by simpa only [peerLane] using fields.1
  intro present
  rw [acknowledged, next.peer_observed, ← view.peer_observed]
  apply settled
  simpa only [lowerRun, upperRun] using present

end Netlib.Check.CampusTCPTwoProgressGatewayPeerSettled
