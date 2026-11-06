import Netlib.Check.CampusTCPTwoProgressGatewayState

/-!
# Admission from the current two-record gateway view

A missing range needs space only for its own end position.
Repeated ranges use the actual resident coverage sources.
-/

namespace Netlib.Check.CampusTCPTwoProgressGatewayState

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressGateway

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway}
variable {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}

theorem View.peer_base (view : View initial current) :
    (view.gateway.session.peer sender.direction).base =
      (initial.gatewayState.session.peer sender.direction).base := by
  cases sender
  · exact view.gateway.identity.base .reply
  · exact view.gateway.identity.base .original

theorem View.peer_observed (view : View initial current) :
    (view.gateway.session.peer sender.direction).observed =
      (initial.gatewayState.session.peer sender.direction).observed :=
  congrArg Theory.SparseCoverage.State.frontier view.peerCoverage

theorem View.peer_highEnd (view : View initial current) :
    (view.gateway.session.peer sender.direction).highEnd =
      (initial.gatewayState.session.peer sender.direction).highEnd :=
  congrArg Theory.SparseCoverage.State.highEnd view.peerCoverage

theorem View.lower_position (view : View initial current) (segment : Segment)
    (sequence : segment.sequence = (endpoint cut.endpoints sender).core.sendNext) :
    Seq.distance (view.gateway.session.lane sender.direction).base segment.sequence = initial.geometry.«prefix» := by
  have bounded : initial.geometry.«prefix» < Seq.modulus := by
    have epoch := initial.geometry.epoch
    unfold Seq.halfSpace Seq.modulus at *
    omega
  rw [sequence, initial.geometry.senderCursor, view.gateway.identity.base, Seq.distance_add,
    Nat.mod_eq_of_lt bounded]

theorem View.upper_position (view : View initial current) (segment : Segment)
    (sequence : segment.sequence = (endpoint cut.endpoints sender).core.sendNext.add lower.length) :
    Seq.distance (view.gateway.session.lane sender.direction).base segment.sequence =
      initial.geometry.«prefix» + lower.length := by
  have bounded : initial.geometry.«prefix» + lower.length < Seq.modulus := by
    have epoch := initial.geometry.epoch
    unfold Seq.halfSpace Seq.modulus at *
    omega
  rw [sequence, initial.geometry.senderCursor, Seq.add_add, view.gateway.identity.base,
    Seq.distance_add, Nat.mod_eq_of_lt bounded]

theorem View.data_ack_offset (view : View initial current) (segment : Segment)
    (ack : segment.acknowledgment = (endpoint cut.endpoints sender).core.receiveNext) :
    Admission.ackOffset (view.gateway.session.peer sender.direction) segment =
      (view.gateway.session.peer sender.direction).observed := by
  apply ack_offset_add _ _ _ _ (Nat.le_refl _)
  rw [ack, initial.geometry.senderAck, view.peer_base, view.peer_observed]

theorem View.lower_disjoint (view : View initial current) (missing : view.ranges.lowerRun = none)
    (run : Admission.Coverage.Run Nat) (member : run ∈ (view.gateway.session.lane sender.direction).coverage.runs) :
    initial.geometry.«prefix» + lower.length ≤ run.position ∨ run.limit ≤ initial.geometry.«prefix» := by
  rw [view.ranges.runs, missing, Option.toList_none, List.append_nil] at member
  rcases List.mem_append.mp member with old | upperMember
  · right
    have bound := Theory.SparseCoverage.State.limit_le_highEnd _ run old
    change run.limit ≤ (initial.gatewayState.session.lane sender.direction).highEnd at bound
    rwa [initial.geometry.highEnd] at bound
  · left
    simp only [(view.ranges.upperFields run upperMember).1, Nat.le_refl]

theorem View.upper_disjoint (view : View initial current) (missing : view.ranges.upperRun = none)
    (run : Admission.Coverage.Run Nat) (member : run ∈ (view.gateway.session.lane sender.direction).coverage.runs) :
    initial.geometry.«prefix» + lower.length + upper.length ≤ run.position ∨
      run.limit ≤ initial.geometry.«prefix» + lower.length := by
  rw [view.ranges.runs, missing, Option.toList_none, List.append_nil] at member
  rcases List.mem_append.mp member with old | lowerMember
  · right
    have bound := Theory.SparseCoverage.State.limit_le_highEnd _ run old
    change run.limit ≤ (initial.gatewayState.session.lane sender.direction).highEnd at bound
    rw [initial.geometry.highEnd] at bound
    omega
  · right
    have fields := view.ranges.lowerFields run lowerMember
    simp only [Theory.SparseCoverage.Run.limit, fields.1, fields.2, Nat.le_refl]

theorem View.lower_fresh (view : View initial current) (segment : Segment)
    (missing : view.ranges.lowerRun = none)
    (sequence : segment.sequence = (endpoint cut.endpoints sender).core.sendNext)
    (payload : segment.payload = lower) (profile : Admission.DataProfile segment)
    (mss : segment.payload.length ≤ (view.gateway.session.peerMSS sender.direction).limit)
    (ack : segment.acknowledgment = (endpoint cut.endpoints sender).core.receiveNext)
    (left : (view.gateway.session.lane sender.direction).acknowledged ≤ initial.geometry.«prefix»)
    (right : initial.geometry.«prefix» + lower.length ≤
      (view.gateway.session.lane sender.direction).acknowledged +
        (view.gateway.session.lane sender.direction).peerWindow.val) :
    Admission.FreshReady view.gateway.session sender.direction segment := by
  have position := view.lower_position segment sequence
  have offset := view.data_ack_offset segment ack
  refine ⟨profile, ?_, mss, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [payload] using initial.lowerNonempty
  · rw [sender_lane, position, payload]
    have epoch := initial.geometry.epoch
    omega
  · simpa only [sender_lane, position] using left
  · simpa only [sender_lane, position, payload] using right
  · intro run member
    simpa only [sender_lane, position, payload] using
      view.lower_disjoint missing run (by simpa only [sender_lane] using member)
  · simp only [offset, Nat.le_refl]
  · rw [offset]
    have bound := (view.gateway.session.peer_valid sender.direction).1
    omega

theorem View.upper_fresh (view : View initial current) (segment : Segment)
    (missing : view.ranges.upperRun = none)
    (sequence : segment.sequence = (endpoint cut.endpoints sender).core.sendNext.add lower.length)
    (payload : segment.payload = upper) (profile : Admission.DataProfile segment)
    (mss : segment.payload.length ≤ (view.gateway.session.peerMSS sender.direction).limit)
    (ack : segment.acknowledgment = (endpoint cut.endpoints sender).core.receiveNext)
    (left : (view.gateway.session.lane sender.direction).acknowledged ≤ initial.geometry.«prefix» + lower.length)
    (right : initial.geometry.«prefix» + lower.length + upper.length ≤
      (view.gateway.session.lane sender.direction).acknowledged +
        (view.gateway.session.lane sender.direction).peerWindow.val) :
    Admission.FreshReady view.gateway.session sender.direction segment := by
  have position := view.upper_position segment sequence
  have offset := view.data_ack_offset segment ack
  refine ⟨profile, ?_, mss, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [payload] using initial.upperNonempty
  · simpa only [sender_lane, position, payload] using initial.geometry.epoch
  · simpa only [sender_lane, position] using left
  · simpa only [sender_lane, position, payload] using right
  · intro run member
    simpa only [sender_lane, position, payload] using
      view.upper_disjoint missing run (by simpa only [sender_lane] using member)
  · simp only [offset, Nat.le_refl]
  · rw [offset]
    have bound := (view.gateway.session.peer_valid sender.direction).1
    omega

theorem View.lower_repeated (view : View initial current) (run : Admission.Coverage.Run Nat)
    (available : view.ranges.lowerRun = some run) (segment : Segment)
    (sequence : segment.sequence = (endpoint cut.endpoints sender).core.sendNext)
    (payload : segment.payload = lower) (profile : Admission.DataProfile segment)
    (mss : segment.payload.length ≤ (view.gateway.session.peerMSS sender.direction).limit)
    (ack : segment.acknowledgment = (endpoint cut.endpoints sender).core.receiveNext) :
    Admission.RepeatedReady view.gateway.session sender.direction segment
      (beforeService input current.report.final gateway).admission.observations := by
  have offset := view.data_ack_offset segment ack
  refine ⟨profile, ?_, mss, ?_, ?_⟩
  · simpa only [sender_lane] using view.lower_known run available segment (view.lower_position segment sequence) payload
  · simp only [offset, Nat.le_refl]
  · rw [offset]
    have bound := (view.gateway.session.peer_valid sender.direction).1
    omega

theorem View.upper_repeated (view : View initial current) (run : Admission.Coverage.Run Nat)
    (available : view.ranges.upperRun = some run) (segment : Segment)
    (sequence : segment.sequence = (endpoint cut.endpoints sender).core.sendNext.add lower.length)
    (payload : segment.payload = upper) (profile : Admission.DataProfile segment)
    (mss : segment.payload.length ≤ (view.gateway.session.peerMSS sender.direction).limit)
    (ack : segment.acknowledgment = (endpoint cut.endpoints sender).core.receiveNext) :
    Admission.RepeatedReady view.gateway.session sender.direction segment
      (beforeService input current.report.final gateway).admission.observations := by
  have offset := view.data_ack_offset segment ack
  refine ⟨profile, ?_, mss, ?_, ?_⟩
  · simpa only [sender_lane] using view.upper_known run available segment (view.upper_position segment sequence) payload
  · simp only [offset, Nat.le_refl]
  · rw [offset]
    have bound := (view.gateway.session.peer_valid sender.direction).1
    omega

theorem View.receiver_ack_ready (view : View initial current) (segment : Segment) (count : Nat)
    (profile : Admission.DataProfile segment) (empty : segment.payload = [])
    (sequence : segment.sequence = (endpoint cut.endpoints sender.other).core.sendNext)
    (ack : segment.acknowledgment = (initial.gatewayState.session.lane sender.direction).base.add count)
    (countBound : count ≤ (view.gateway.session.lane sender.direction).observed)
    (stale : (view.gateway.session.lane sender.direction).acknowledged ≤ count + 65535) :
    Admission.AckReady view.gateway.session sender.other.direction segment := by
  have senderPeer : view.gateway.session.sender sender.other.direction = view.gateway.session.peer sender.direction := by
    cases sender <;> rfl
  have peerLane : view.gateway.session.peer sender.other.direction = view.gateway.session.lane sender.direction := by
    cases sender <;> rfl
  apply view.gateway.ack_ready sender.other.direction segment
    (initial.gatewayState.session.peer sender.direction).highEnd count profile empty
  · rw [senderPeer, view.peer_base, sequence, initial.geometry.receiverSequence]
  · simp only [senderPeer, view.peer_highEnd, Nat.le_refl]
  · rw [peerLane, view.gateway.identity.base]
    exact ack
  · simpa only [peerLane] using countBound
  · simpa only [peerLane] using stale

end Netlib.Check.CampusTCPTwoProgressGatewayState
