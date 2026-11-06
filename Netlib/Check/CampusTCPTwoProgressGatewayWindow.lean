import Netlib.Check.CampusTCPTwoProgressGatewayReady
import Netlib.Check.CampusTCPTwoProgressServiceState

/-!
# Current gateway window space for two TCP records

ACK processing keeps enough space when either window branch has it.
Missing-range left bounds follow from the current coverage frontier.
-/

namespace Netlib.Check.CampusTCPTwoProgressGatewayWindow

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressGatewayState

theorem acknowledgedLane_space (lane : Admission.Lane) (segment : Segment) (target : Nat)
    (old : target ≤ lane.acknowledged + lane.peerWindow.val)
    (incoming : target ≤ Admission.ackOffset lane segment + segment.window.val) :
    target ≤ (Admission.acknowledgedLane lane segment).acknowledged +
      (Admission.acknowledgedLane lane segment).peerWindow.val := by
  unfold Admission.acknowledgedLane
  split <;> dsimp only <;> omega

private theorem sentLane_window (lane : Admission.Lane) (segment : Segment) (source : Nat) :
    (Admission.sentLane lane segment source).acknowledged = lane.acknowledged ∧
      (Admission.sentLane lane segment source).peerWindow = lane.peerWindow := by
  unfold Admission.sentLane
  split <;> exact ⟨rfl, rfl⟩

theorem result_window_fields (result : Admission.Result before packet lifecycle prepared)
    (phase : before.phase = .data session) (afterPhase : result.state.phase = .data after) :
    (after.sender prepared.attachment.direction).acknowledged = (session.sender prepared.attachment.direction).acknowledged ∧
      (after.sender prepared.attachment.direction).peerWindow = (session.sender prepared.attachment.direction).peerWindow ∧
      after.peer prepared.attachment.direction = Admission.acknowledgedLane (session.peer prepared.attachment.direction) packet.packet.segment := by
  have allowed : Admission.Allowed (.data session) prepared.attachment packet.packet.segment before.observations :=
    phase ▸ result.admitted
  have computed : Admission.Phase.data after = Admission.nextPhase (.data session) prepared.attachment packet.packet.segment allowed :=
    afterPhase.symm.trans (by simpa only [phase] using result.phase)
  simp only [Admission.nextPhase] at computed
  repeat' split at computed
  all_goals
    have equal := Admission.Phase.data.inj computed
    rw [equal]
    simp_all only [Admission.Session.sender, Admission.Session.peer, and_true]
  all_goals first
    | exact sentLane_window _ _ _
    | trivial

theorem result_sender_space (result : Admission.Result before packet lifecycle prepared)
    (phase : before.phase = .data session) (afterPhase : result.state.phase = .data after) (target : Nat)
    (old : target ≤ (session.sender prepared.attachment.direction).acknowledged +
      (session.sender prepared.attachment.direction).peerWindow.val) :
    target ≤ (after.sender prepared.attachment.direction).acknowledged +
      (after.sender prepared.attachment.direction).peerWindow.val := by
  have fields := result_window_fields result phase afterPhase
  rw [fields.1, fields.2.1]
  exact old

theorem result_peer_space (result : Admission.Result before packet lifecycle prepared)
    (phase : before.phase = .data session) (afterPhase : result.state.phase = .data after) (target : Nat)
    (old : target ≤ (session.peer prepared.attachment.direction).acknowledged +
      (session.peer prepared.attachment.direction).peerWindow.val)
    (incoming : target ≤ Admission.ackOffset (session.peer prepared.attachment.direction) packet.packet.segment +
      packet.packet.segment.window.val) :
    target ≤ (after.peer prepared.attachment.direction).acknowledged +
      (after.peer prepared.attachment.direction).peerWindow.val := by
  rw [(result_window_fields result phase afterPhase).2.2]
  exact acknowledgedLane_space _ _ target old incoming

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}

def Reserved (view : View initial current) : Prop :=
  initial.geometry.«prefix» + lower.length + upper.length ≤
    (view.gateway.session.lane sender.direction).acknowledged +
      (view.gateway.session.lane sender.direction).peerWindow.val

theorem initial_reserved (initial : TwoWriteInitial cut sender gateway lower upper) :
    Reserved (View.ofInitial initial) := by
  change initial.geometry.«prefix» + lower.length + upper.length ≤
    (initial.gatewayState.session.lane sender.direction).acknowledged +
      (initial.gatewayState.session.lane sender.direction).peerWindow.val
  rw [initial.geometry.acknowledged]
  have space := initial.geometry.window
  omega

theorem lower_left (view : View initial current) (missing : view.ranges.lowerRun = none) :
    (view.gateway.session.lane sender.direction).acknowledged ≤ initial.geometry.«prefix» := by
  have valid := (view.gateway.session.sender_valid sender.direction).1
  rw [sender_lane, view.observed, missing] at valid
  exact valid

theorem upper_left (view : View initial current) (missing : view.ranges.upperRun = none) :
    (view.gateway.session.lane sender.direction).acknowledged ≤ initial.geometry.«prefix» + lower.length := by
  have valid := (view.gateway.session.sender_valid sender.direction).1
  rw [sender_lane, view.observed, missing] at valid
  simp only [Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_zero] at valid
  split at valid <;> omega

theorem lower_fresh (view : View initial current) (space : Reserved view) (segment : Segment)
    (missing : view.ranges.lowerRun = none)
    (sequence : segment.sequence = (endpoint cut.endpoints sender).core.sendNext)
    (payload : segment.payload = lower) (profile : Admission.DataProfile segment)
    (mss : segment.payload.length ≤ (view.gateway.session.peerMSS sender.direction).limit)
    (ack : segment.acknowledgment = (endpoint cut.endpoints sender).core.receiveNext) :
    Admission.FreshReady view.gateway.session sender.direction segment := by
  apply view.lower_fresh segment missing sequence payload profile mss ack (lower_left view missing)
  exact Nat.le_trans (by omega) space

theorem upper_fresh (view : View initial current) (space : Reserved view) (segment : Segment)
    (missing : view.ranges.upperRun = none)
    (sequence : segment.sequence = (endpoint cut.endpoints sender).core.sendNext.add lower.length)
    (payload : segment.payload = upper) (profile : Admission.DataProfile segment)
    (mss : segment.payload.length ≤ (view.gateway.session.peerMSS sender.direction).limit)
    (ack : segment.acknowledgment = (endpoint cut.endpoints sender).core.receiveNext) :
    Admission.FreshReady view.gateway.session sender.direction segment :=
  view.upper_fresh segment missing sequence payload profile mss ack (upper_left view missing) space

open CampusTCPTwoProgressNetwork (ServiceMove)
open CampusTCPTwoProgressServiceState (processingAt processingAt_admission processingAt_attachment)

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

theorem sender_service_reserved (view : View initial current) (space : Reserved view)
    (value : ServiceMove initial current item hit session actual served emission emitted)
    (next : View initial value.move.after) (direction : hit.direction = sender.direction) : Reserved next := by
  obtain ⟨processing, present, _, _, attached, _⟩ := value.facts.processing
  have previous : served.before = beforeService input current.report.final gateway := by
    rw [value.facts.current, value.selected]
  let selected := processingAt processing previous
  have selectedDirection : selected.prepared.attachment.direction = sender.direction := by
    rw [processingAt_attachment]
    exact attached.trans direction
  have old : initial.geometry.«prefix» + lower.length + upper.length ≤
      (view.gateway.session.sender selected.prepared.attachment.direction).acknowledged +
        (view.gateway.session.sender selected.prepared.attachment.direction).peerWindow.val := by
    simpa only [Reserved, selectedDirection, sender_lane] using space
  have retained := result_sender_space selected.admitted view.gateway.phase
    (processing_phase view value next processing present previous) _ old
  simpa only [Reserved, selectedDirection, sender_lane] using retained

theorem receiver_service_reserved (view : View initial current) (space : Reserved view)
    (value : ServiceMove initial current item hit session actual served emission emitted)
    (next : View initial value.move.after) (direction : hit.direction = sender.other.direction)
    (incoming : initial.geometry.«prefix» + lower.length + upper.length ≤
      Admission.ackOffset (view.gateway.session.lane sender.direction) served.ticket.value.source.packet.segment +
        served.ticket.value.source.packet.segment.window.val) : Reserved next := by
  obtain ⟨processing, present, _, _, attached, _⟩ := value.facts.processing
  have previous : served.before = beforeService input current.report.final gateway := by
    rw [value.facts.current, value.selected]
  let selected := processingAt processing previous
  have selectedDirection : selected.prepared.attachment.direction = sender.other.direction := by
    rw [processingAt_attachment]
    exact attached.trans direction
  have peerLane : ∀ session : Admission.Session,
      session.peer selected.prepared.attachment.direction = session.lane sender.direction := by
    intro session
    rw [selectedDirection]
    cases sender <;> rfl
  have retained := result_peer_space selected.admitted view.gateway.phase
    (processing_phase view value next processing present previous)
    (initial.geometry.«prefix» + lower.length + upper.length)
    (by simpa only [Reserved, peerLane] using space)
    (by simpa only [peerLane, WireForwarding.Source.asInput] using incoming)
  simpa only [Reserved, peerLane] using retained

end Netlib.Check.CampusTCPTwoProgressGatewayWindow
