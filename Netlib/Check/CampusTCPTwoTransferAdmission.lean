import Netlib.Check.CampusTCPTwoProgressGatewayAtRanges
import Netlib.Check.CampusTCPTwoTransferNative
import Netlib.Check.CampusTCPTwoTransferNetwork
import Netlib.Check.CampusTCPTwoProgressPathsReady

/-!
# Packet admission at the actual gateway location

Current ranges select fresh or repeated data admission.
Each service uses its ticket's selected gateway and current native checks.
-/

namespace Netlib.Check.CampusTCPTwoProgressGatewayAt

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressGateway
open CampusTCPTwoProgressGatewayState (sender_lane)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway}
variable {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}

theorem ViewAt.peer_base (view : ViewAt initial current location) :
    (view.gateway.session.peer sender.direction).base =
      (initial.gatewayState.session.peer sender.direction).base := by
  cases sender
  · exact view.gateway.identity.base .reply
  · exact view.gateway.identity.base .original

theorem ViewAt.peer_observed (view : ViewAt initial current location) :
    (view.gateway.session.peer sender.direction).observed =
      (initial.gatewayState.session.peer sender.direction).observed :=
  congrArg Theory.SparseCoverage.State.frontier view.peerCoverage

theorem ViewAt.peer_highEnd (view : ViewAt initial current location) :
    (view.gateway.session.peer sender.direction).highEnd =
      (initial.gatewayState.session.peer sender.direction).highEnd :=
  congrArg Theory.SparseCoverage.State.highEnd view.peerCoverage

theorem ViewAt.lower_position (view : ViewAt initial current location) (segment : Segment)
    (sequence : segment.sequence = (endpoint cut.endpoints sender).core.sendNext) :
    Seq.distance (view.gateway.session.lane sender.direction).base segment.sequence = initial.geometry.«prefix» := by
  have bounded : initial.geometry.«prefix» < Seq.modulus := by
    have epoch := initial.geometry.epoch
    unfold Seq.halfSpace Seq.modulus at *
    omega
  rw [sequence, initial.geometry.senderCursor, view.gateway.identity.base, Seq.distance_add,
    Nat.mod_eq_of_lt bounded]

theorem ViewAt.upper_position (view : ViewAt initial current location) (segment : Segment)
    (sequence : segment.sequence = (endpoint cut.endpoints sender).core.sendNext.add lower.length) :
    Seq.distance (view.gateway.session.lane sender.direction).base segment.sequence =
      initial.geometry.«prefix» + lower.length := by
  have bounded : initial.geometry.«prefix» + lower.length < Seq.modulus := by
    have epoch := initial.geometry.epoch
    unfold Seq.halfSpace Seq.modulus at *
    omega
  rw [sequence, initial.geometry.senderCursor, Seq.add_add, view.gateway.identity.base,
    Seq.distance_add, Nat.mod_eq_of_lt bounded]

theorem ViewAt.data_ack_offset (view : ViewAt initial current location) (segment : Segment)
    (ack : segment.acknowledgment = (endpoint cut.endpoints sender).core.receiveNext) :
    Admission.ackOffset (view.gateway.session.peer sender.direction) segment =
      (view.gateway.session.peer sender.direction).observed := by
  apply ack_offset_add _ _ _ _ (Nat.le_refl _)
  rw [ack, initial.geometry.senderAck, view.peer_base, view.peer_observed]

theorem ViewAt.lower_disjoint (view : ViewAt initial current location) (missing : view.ranges.lowerRun = none)
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

theorem ViewAt.upper_disjoint (view : ViewAt initial current location) (missing : view.ranges.upperRun = none)
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

theorem ViewAt.lower_fresh (view : ViewAt initial current location) (segment : Segment)
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

theorem ViewAt.upper_fresh (view : ViewAt initial current location) (segment : Segment)
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

theorem ViewAt.lower_repeated (view : ViewAt initial current location)
    (retained : cut.report.steps <+: current.report.steps) (run : Admission.Coverage.Run Nat)
    (available : view.ranges.lowerRun = some run) (segment : Segment)
    (sequence : segment.sequence = (endpoint cut.endpoints sender).core.sendNext)
    (payload : segment.payload = lower) (profile : Admission.DataProfile segment)
    (mss : segment.payload.length ≤ (view.gateway.session.peerMSS sender.direction).limit)
    (ack : segment.acknowledgment = (endpoint cut.endpoints sender).core.receiveNext) :
    Admission.RepeatedReady view.gateway.session sender.direction segment
      (beforeService input current.report.final location).admission.observations := by
  have offset := view.data_ack_offset segment ack
  refine ⟨profile, ?_, mss, ?_, ?_⟩
  · simpa only [sender_lane] using view.lower_known retained run available segment (view.lower_position segment sequence) payload
  · simp only [offset, Nat.le_refl]
  · rw [offset]
    have bound := (view.gateway.session.peer_valid sender.direction).1
    omega

theorem ViewAt.upper_repeated (view : ViewAt initial current location)
    (retained : cut.report.steps <+: current.report.steps) (run : Admission.Coverage.Run Nat)
    (available : view.ranges.upperRun = some run) (segment : Segment)
    (sequence : segment.sequence = (endpoint cut.endpoints sender).core.sendNext.add lower.length)
    (payload : segment.payload = upper) (profile : Admission.DataProfile segment)
    (mss : segment.payload.length ≤ (view.gateway.session.peerMSS sender.direction).limit)
    (ack : segment.acknowledgment = (endpoint cut.endpoints sender).core.receiveNext) :
    Admission.RepeatedReady view.gateway.session sender.direction segment
      (beforeService input current.report.final location).admission.observations := by
  have offset := view.data_ack_offset segment ack
  refine ⟨profile, ?_, mss, ?_, ?_⟩
  · simpa only [sender_lane] using view.upper_known retained run available segment (view.upper_position segment sequence) payload
  · simp only [offset, Nat.le_refl]
  · rw [offset]
    have bound := (view.gateway.session.peer_valid sender.direction).1
    omega

theorem ViewAt.receiver_ack_ready (view : ViewAt initial current location)
    (retained : cut.report.steps <+: current.report.steps) (segment : Segment) (count : Nat)
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
  apply view.gateway.ack_ready retained sender.other.direction segment
    (initial.gatewayState.session.peer sender.direction).highEnd count profile empty
  · rw [senderPeer, view.peer_base, sequence, initial.geometry.receiverSequence]
  · simp only [senderPeer, view.peer_highEnd, Nat.le_refl]
  · rw [peerLane, view.gateway.identity.base]
    exact ack
  · simpa only [peerLane] using countBound
  · simpa only [peerLane] using stale

end Netlib.Check.CampusTCPTwoProgressGatewayAt

namespace Netlib.Check.CampusTCPTwoTransferAdmission

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressSender
open CampusTCPTwoProgressGatewayAt (ViewAt)
open CampusTCPTwoProgressGatewayState (sender_lane)
open CampusTCPTwoTransferState (Retained Reserved)
open CampusTCPTwoTransferNative (Checks)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current next : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {part : Part} {produced : Produced input.active input.passive}

def rangeAt (view : ViewAt initial current location) : Part → Option (Admission.Coverage.Run Nat)
  | .lower => view.ranges.lowerRun
  | .upper => view.ranges.upperRun

theorem peer_mss (view : ViewAt initial current location) (part : Part) :
    (part.bytes lower upper).length ≤ (view.gateway.session.peerMSS sender.direction).limit := by
  have total := Nat.le_trans initial.senderState.mss (initial.endpoint_peer_mss sender)
  have same : view.gateway.session.peerMSS sender.direction = initial.gatewayState.session.peerMSS sender.direction := by
    cases sender
    · exact view.gateway.identity.serverMSS
    · exact view.gateway.identity.clientMSS
  rw [same]
  cases part <;> simp only [Part.bytes] <;> omega

private theorem lower_left (view : ViewAt initial current location) (missing : view.ranges.lowerRun = none) :
    (view.gateway.session.lane sender.direction).acknowledged ≤ initial.geometry.«prefix» := by
  have valid := (view.gateway.session.sender_valid sender.direction).1
  rw [sender_lane, view.observed, missing] at valid
  exact valid

private theorem upper_left (view : ViewAt initial current location) (missing : view.ranges.upperRun = none) :
    (view.gateway.session.lane sender.direction).acknowledged ≤ initial.geometry.«prefix» + lower.length := by
  have valid := (view.gateway.session.sender_valid sender.direction).1
  rw [sender_lane, view.observed, missing] at valid
  simp only [Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_zero] at valid
  split at valid <;> omega

inductive DataAdmission (view : ViewAt initial current location) (produced : Produced input.active input.passive) : Part → Prop where
  | lower (missing : view.ranges.lowerRun = none)
      (ready : Admission.FreshReady view.gateway.session sender.direction produced.source.packet.segment) :
      DataAdmission view produced .lower
  | upper (missing : view.ranges.upperRun = none)
      (ready : Admission.FreshReady view.gateway.session sender.direction produced.source.packet.segment) :
      DataAdmission view produced .upper
  | repeated {part : Part} (present : (rangeAt view part).isSome = true)
      (ready : Admission.RepeatedReady view.gateway.session sender.direction produced.source.packet.segment
        (beforeService input current.report.final location).admission.observations) : DataAdmission view produced part

theorem data_admission (view : ViewAt initial current location) (retained : cut.report.steps <+: current.report.steps)
    (space : Reserved view)
    (fields : CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper) produced) :
    DataAdmission view produced part := by
  have mss : produced.source.packet.segment.payload.length ≤ (view.gateway.session.peerMSS sender.direction).limit := by
    rw [fields.payload]
    exact peer_mss view part
  cases part with
  | lower =>
    have sequence : produced.source.packet.segment.sequence = (endpoint cut.endpoints sender).core.sendNext := by
      simpa only [Part.offset, Seq.add_zero] using fields.sequence
    cases present : view.ranges.lowerRun with
    | none =>
      exact .lower present (view.lower_fresh _ present sequence fields.payload fields.profile mss fields.acknowledgment
        (lower_left view present) (Nat.le_trans (by omega) space))
    | some run =>
      exact .repeated (by simp only [rangeAt, present, Option.isSome_some])
        (view.lower_repeated retained run present _ sequence fields.payload fields.profile mss fields.acknowledgment)
  | upper =>
    cases present : view.ranges.upperRun with
    | none =>
      exact .upper present (view.upper_fresh _ present fields.sequence fields.payload fields.profile mss fields.acknowledgment
        (upper_left view present) space)
    | some run =>
      exact .repeated (by simp only [rangeAt, present, Option.isSome_some])
        (view.upper_repeated retained run present _ fields.sequence fields.payload fields.profile mss fields.acknowledgment)

theorem current_zone (view : ViewAt initial current location) (actor : Actor) :
    view.gateway.session.entry.flow.zone actor.direction = input.zone := by
  rw [view.gateway.identity.entry, initial.entry_eq]
  cases actor
  · exact initial.basis.aligned.originalZone
  · exact initial.basis.aligned.replyZone

theorem data_header (view : ViewAt initial current location)
    (fields : CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper) produced) :
    produced.source.packet.header = view.gateway.session.entry.flow.input sender.direction := by
  rw [view.gateway.identity.entry]
  exact fields.header

theorem ack_header (view : ViewAt initial current location) (fields : CampusTCPTwoProgressWire.AckFields initial count produced) :
    produced.source.packet.header = view.gateway.session.entry.flow.input sender.other.direction := by
  rw [view.gateway.identity.entry]
  exact fields.header

theorem ack_admission (view : ViewAt initial current location) (retained : cut.report.steps <+: current.report.steps)
    (fields : CampusTCPTwoProgressWire.AckFields initial count produced)
    (within : initial.geometry.«prefix» + count ≤ (view.gateway.session.lane sender.direction).observed)
    (stale : (view.gateway.session.lane sender.direction).acknowledged ≤ initial.geometry.«prefix» + count + 65535) :
    Admission.AckReady view.gateway.session sender.other.direction produced.source.packet.segment := by
  apply view.receiver_ack_ready retained _ (initial.geometry.«prefix» + count) fields.profile fields.payload fields.sequence
  · rw [fields.acknowledgment, initial.geometry.senderCursor, Seq.add_add]
  · exact within
  · exact stale

private def fresh_ready (view : ViewAt initial current location) (retained : Retained cut current)
    (checks : Checks cut initial.gatewayState.session.entry)
    (fields : CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper) produced)
    (data : Admission.DataReady view.gateway.session sender.direction produced.source.packet.segment) :
    CampusTCPService.ExistingDataReady (input.contextFor location) (beforeService input current.report.final location)
      produced.source input.zone (checks.ingress location sender)
      ⟨view.gateway.session.entry.flow, sender.direction⟩ view.gateway.session sender.nextHop :=
  view.gateway.existing_ready retained.retained (checks.paths location sender) (retained.policy location)
    produced.source input.zone (data_header view fields) (current_zone view sender) data fields.ttl

private def repeated_ready (view : ViewAt initial current location) (retained : Retained cut current)
    (checks : Checks cut initial.gatewayState.session.entry)
    (fields : CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper) produced)
    (data : Admission.RepeatedReady view.gateway.session sender.direction produced.source.packet.segment
      (beforeService input current.report.final location).admission.observations) :
    CampusTCPService.ExistingRepeatedReady (input.contextFor location) (beforeService input current.report.final location)
      produced.source input.zone (checks.ingress location sender)
      ⟨view.gateway.session.entry.flow, sender.direction⟩ view.gateway.session sender.nextHop :=
  view.gateway.repeated_ready retained.retained (checks.paths location sender) (retained.policy location)
    produced.source input.zone (data_header view fields) (current_zone view sender) data fields.ttl

private def ack_ready (view : ViewAt initial current location) (retained : Retained cut current)
    (checks : Checks cut initial.gatewayState.session.entry) (fields : CampusTCPTwoProgressWire.AckFields initial count produced)
    (within : initial.geometry.«prefix» + count ≤ (view.gateway.session.lane sender.direction).observed)
    (stale : (view.gateway.session.lane sender.direction).acknowledged ≤ initial.geometry.«prefix» + count + 65535) :
    CampusTCPService.ExistingDataReady (input.contextFor location) (beforeService input current.report.final location)
      produced.source input.zone (checks.ingress location sender.other)
      ⟨view.gateway.session.entry.flow, sender.other.direction⟩ view.gateway.session sender.other.nextHop :=
  view.gateway.existing_ready retained.retained (checks.paths location sender.other) (retained.policy location)
    produced.source input.zone (ack_header view fields) (current_zone view sender.other)
    (.inr (ack_admission view retained.retained fields within stale)) fields.ttl

open CampusTCPTwoTransferNetwork (Service)
open CampusTCPTwoProgressServiceState (processingAt processingAt_outcome processingAt_admission processingAt_attachment)

variable {item : Theory.Outstanding.Item (Ticket input.active input.passive)} {hit : FlowNAT.Hit} {session : Admission.Session}
variable {actual : Step input} {served : Served input} {emission : WireForwarding.Emission served.ticket.value.source.packet}
variable {emitted : served.evidence.output = some emission}

private theorem processing_before (value : Service current item hit session actual served emission emitted)
    (located : item.value.gateway = location) : served.before = beforeService input current.report.final location := by
  rw [value.facts.current, located]

private theorem admission_after (value : Service current item hit session actual served emission emitted)
    (located : item.value.gateway = location)
    (processing : CampusTCPService.Processing (input.contextFor served.ticket.value.gateway)
      served.before served.ticket.value.source input.zone) (present : served.evidence.processing = some processing) :
    (beforeService input value.move.after.report.final location).admission =
      (processingAt processing (processing_before value located)).nextAdmission := by
  have after := value.after_before processing present
  rw [located] at after
  rw [after, processingAt_admission]
  rfl

private theorem tracker_after (value : Service current item hit session actual served emission emitted)
    (located : item.value.gateway = location)
    (processing : CampusTCPService.Processing (input.contextFor served.ticket.value.gateway)
      served.before served.ticket.value.source input.zone) (present : served.evidence.processing = some processing) :
    (beforeService input value.move.after.report.final location).tracker =
      (processingAt processing (processing_before value located)).outcome.state := by
  have after := value.after_before processing present
  rw [located] at after
  rw [after, processingAt_outcome]
  rfl

private theorem lower_service (view : ViewAt initial current location) (retained : Retained cut current)
    (value : Service current item ⟨view.gateway.session.entry.flow, sender.direction⟩ view.gateway.session actual served emission emitted)
    (located : item.value.gateway = location)
    (ready : Admission.FreshReady view.gateway.session sender.direction served.ticket.value.source.packet.segment)
    (missing : view.ranges.lowerRun = none)
    (position : Seq.distance (view.gateway.session.lane sender.direction).base
      served.ticket.value.source.packet.segment.sequence = initial.geometry.«prefix»)
    (payload : served.ticket.value.source.packet.segment.payload = lower) :
    ∃ result : ViewAt initial value.move.after location, result.ranges.upperRun = view.ranges.upperRun ∧
      ∃ run, result.ranges.lowerRun = some run := by
  obtain ⟨processing, present, _, _, attached, _⟩ := value.facts.processing
  let selected := processingAt processing (processing_before value located)
  have direction : selected.prepared.attachment.direction = sender.direction := by
    rw [processingAt_attachment]
    exact attached
  obtain ⟨result, upperRun, run, lowerRun, _⟩ := view.lower_service retained.retained selected direction
    (by rw [direction]; exact ready) missing position payload
    (admission_after value located processing present) (tracker_after value located processing present)
  exact ⟨result, upperRun, run, lowerRun⟩

private theorem upper_service (view : ViewAt initial current location) (retained : Retained cut current)
    (value : Service current item ⟨view.gateway.session.entry.flow, sender.direction⟩ view.gateway.session actual served emission emitted)
    (located : item.value.gateway = location)
    (ready : Admission.FreshReady view.gateway.session sender.direction served.ticket.value.source.packet.segment)
    (missing : view.ranges.upperRun = none)
    (position : Seq.distance (view.gateway.session.lane sender.direction).base
      served.ticket.value.source.packet.segment.sequence = initial.geometry.«prefix» + lower.length)
    (payload : served.ticket.value.source.packet.segment.payload = upper) :
    ∃ result : ViewAt initial value.move.after location, result.ranges.lowerRun = view.ranges.lowerRun ∧
      ∃ run, result.ranges.upperRun = some run := by
  obtain ⟨processing, present, _, _, attached, _⟩ := value.facts.processing
  let selected := processingAt processing (processing_before value located)
  have direction : selected.prepared.attachment.direction = sender.direction := by
    rw [processingAt_attachment]
    exact attached
  obtain ⟨result, lowerRun, run, upperRun, _⟩ := view.upper_service retained.retained selected direction
    (by rw [direction]; exact ready) missing position payload
    (admission_after value located processing present) (tracker_after value located processing present)
  exact ⟨result, lowerRun, run, upperRun⟩

private theorem repeat_service (view : ViewAt initial current location) (retained : Retained cut current)
    (value : Service current item ⟨view.gateway.session.entry.flow, sender.direction⟩ view.gateway.session actual served emission emitted)
    (located : item.value.gateway = location)
    (known : Admission.KnownRange (view.gateway.session.lane sender.direction) view.gateway.session.entry sender.direction
      served.ticket.value.source.packet.segment (beforeService input current.report.final location).admission.observations) :
    ∃ result : ViewAt initial value.move.after location, result.ranges.lowerRun = view.ranges.lowerRun ∧
      result.ranges.upperRun = view.ranges.upperRun := by
  obtain ⟨processing, present, _, _, attached, _⟩ := value.facts.processing
  let selected := processingAt processing (processing_before value located)
  have direction : selected.prepared.attachment.direction = sender.direction := by
    rw [processingAt_attachment]
    exact attached
  exact view.repeat_service retained.retained selected (by rw [direction]; exact known)
    (admission_after value located processing present) (tracker_after value located processing present)

private theorem service_phase (view : ViewAt initial current location)
    (value : Service current item hit view.gateway.session actual served emission emitted) (located : item.value.gateway = location)
    (after : ViewAt initial value.move.after location)
    (processing : CampusTCPService.Processing (input.contextFor served.ticket.value.gateway)
      served.before served.ticket.value.source input.zone) (present : served.evidence.processing = some processing) :
    (processingAt processing (processing_before value located)).admitted.state.phase = .data after.gateway.session := by
  have phase := after.gateway.phase
  rw [admission_after value located processing present,
    CampusTCPRoundAdmission.Processing.committed_data _ view.gateway.session view.gateway.phase] at phase
  exact phase

theorem data_reserved (view : ViewAt initial current location) (space : Reserved view)
    (value : Service current item ⟨view.gateway.session.entry.flow, sender.direction⟩ view.gateway.session actual served emission emitted)
    (located : item.value.gateway = location) (after : ViewAt initial value.move.after location) : Reserved after := by
  obtain ⟨processing, present, _, _, attached, _⟩ := value.facts.processing
  let selected := processingAt processing (processing_before value located)
  have direction : selected.prepared.attachment.direction = sender.direction := by rw [processingAt_attachment]; exact attached
  have result := CampusTCPTwoProgressGatewayWindow.result_sender_space selected.admitted view.gateway.phase
    (service_phase view value located after processing present) (initial.geometry.«prefix» + lower.length + upper.length)
    (by simpa only [direction, sender_lane, Reserved] using space)
  simpa only [direction, sender_lane, Reserved] using result

private def ticket_fresh_ready (view : ViewAt initial current location) (retained : Retained cut current)
    (checks : Checks cut initial.gatewayState.session.entry) (located : item.value.gateway = location)
    (ingress : item.value.ingress = checks.ingress location sender) (actor : item.value.produced.actor = sender)
    (fields : CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper) item.value.produced)
    (data : Admission.DataReady view.gateway.session sender.direction item.value.source.packet.segment) :
    CampusTCPService.ExistingDataReady (input.contextFor item.value.gateway) (beforeService input current.report.final item.value.gateway)
      item.value.source input.zone item.value.ingress ⟨view.gateway.session.entry.flow, sender.direction⟩
      view.gateway.session item.value.produced.actor.nextHop := by
  rw [located, ingress, actor]
  exact fresh_ready view retained checks fields data

private def ticket_repeated_ready (view : ViewAt initial current location) (retained : Retained cut current)
    (checks : Checks cut initial.gatewayState.session.entry) (located : item.value.gateway = location)
    (ingress : item.value.ingress = checks.ingress location sender) (actor : item.value.produced.actor = sender)
    (fields : CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper) item.value.produced)
    (data : Admission.RepeatedReady view.gateway.session sender.direction item.value.source.packet.segment
      (beforeService input current.report.final location).admission.observations) :
    CampusTCPService.ExistingRepeatedReady (input.contextFor item.value.gateway) (beforeService input current.report.final item.value.gateway)
      item.value.source input.zone item.value.ingress ⟨view.gateway.session.entry.flow, sender.direction⟩
      view.gateway.session item.value.produced.actor.nextHop := by
  rw [located, ingress, actor]
  exact repeated_ready view retained checks fields data

structure DataServed (view : ViewAt initial current location) (item : Theory.Outstanding.Item (Ticket input.active input.passive))
    (part : Part) (actual : Step input) where
  served : Served input
  emission : WireForwarding.Emission served.ticket.value.source.packet
  emitted : served.evidence.output = some emission
  value : Service current item ⟨view.gateway.session.entry.flow, sender.direction⟩ view.gateway.session actual served emission emitted
  next : ViewAt initial value.move.after location
  reserved : Reserved next
  covered : (rangeAt next part).isSome = true
  preserved : ∀ role, (rangeAt view role).isSome = true → (rangeAt next role).isSome = true

theorem serve_data_at (view : ViewAt initial current location) (retained : Retained cut current)
    (checks : Checks cut initial.gatewayState.session.entry) (space : Reserved view)
    (item : Theory.Outstanding.Item (Ticket input.active input.passive)) (member : item ∈ current.report.final.work.pending)
    (phase : CampusTCPGatewayEnabled.ServicePhaseReady current.report.final item.value.gateway)
    (located : item.value.gateway = location) (ingress : item.value.ingress = checks.ingress location sender)
    (actor : item.value.produced.actor = sender)
    (fields : CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper) item.value.produced) :
    ∃ actual, Nonempty (DataServed view item part actual) := by
  have admitted := data_admission view retained.retained space fields
  cases admitted with
  | lower missing ready =>
    obtain ⟨actual, served, emission, emitted, ⟨value⟩⟩ := CampusTCPTwoTransferNetwork.serve_at current item member phase
      ⟨view.gateway.session.entry.flow, sender.direction⟩ view.gateway.session
      (ticket_fresh_ready view retained checks located ingress actor fields (.inl ready))
    have selectedReady : Admission.FreshReady view.gateway.session sender.direction served.ticket.value.source.packet.segment := by
      rw [value.facts.ticket]
      exact ready
    have position : Seq.distance (view.gateway.session.lane sender.direction).base
        served.ticket.value.source.packet.segment.sequence = initial.geometry.«prefix» := by
      rw [value.facts.ticket]
      exact view.lower_position _ (by simpa only [Part.offset, Seq.add_zero, Ticket.source] using fields.sequence)
    obtain ⟨after, upperRun, run, lowerRun⟩ := lower_service view retained value located selectedReady missing position
      (by rw [value.facts.ticket]; exact fields.payload)
    have covered : (rangeAt after .lower).isSome = true := by simp only [rangeAt, lowerRun, Option.isSome_some]
    refine ⟨actual, ⟨⟨served, emission, emitted, value, after, data_reserved view space value located after, covered, ?_⟩⟩⟩
    intro role before
    cases role
    · exact covered
    · simpa only [rangeAt, upperRun] using before
  | upper missing ready =>
    obtain ⟨actual, served, emission, emitted, ⟨value⟩⟩ := CampusTCPTwoTransferNetwork.serve_at current item member phase
      ⟨view.gateway.session.entry.flow, sender.direction⟩ view.gateway.session
      (ticket_fresh_ready view retained checks located ingress actor fields (.inl ready))
    have selectedReady : Admission.FreshReady view.gateway.session sender.direction served.ticket.value.source.packet.segment := by
      rw [value.facts.ticket]
      exact ready
    have position : Seq.distance (view.gateway.session.lane sender.direction).base
        served.ticket.value.source.packet.segment.sequence = initial.geometry.«prefix» + lower.length := by
      rw [value.facts.ticket]
      exact view.upper_position _ fields.sequence
    obtain ⟨after, lowerRun, run, upperRun⟩ := upper_service view retained value located selectedReady missing position
      (by rw [value.facts.ticket]; exact fields.payload)
    have covered : (rangeAt after .upper).isSome = true := by simp only [rangeAt, upperRun, Option.isSome_some]
    refine ⟨actual, ⟨⟨served, emission, emitted, value, after, data_reserved view space value located after, covered, ?_⟩⟩⟩
    intro role before
    cases role
    · simpa only [rangeAt, lowerRun] using before
    · exact covered
  | repeated present ready =>
    obtain ⟨actual, served, emission, emitted, ⟨value⟩⟩ := CampusTCPTwoTransferNetwork.serve_repeated_at current item member phase
      ⟨view.gateway.session.entry.flow, sender.direction⟩ view.gateway.session
      (ticket_repeated_ready view retained checks located ingress actor fields ready)
    have known : Admission.KnownRange (view.gateway.session.lane sender.direction) view.gateway.session.entry sender.direction
        served.ticket.value.source.packet.segment (beforeService input current.report.final location).admission.observations := by
      rw [value.facts.ticket]
      simpa only [sender_lane, Ticket.source] using ready.known
    obtain ⟨after, lowerRun, upperRun⟩ := repeat_service view retained value located known
    have preserved : ∀ role, (rangeAt view role).isSome = true → (rangeAt after role).isSome = true := by
      intro role before
      cases role
      · simpa only [rangeAt, lowerRun] using before
      · simpa only [rangeAt, upperRun] using before
    exact ⟨actual, ⟨⟨served, emission, emitted, value, after, data_reserved view space value located after,
      preserved part present, preserved⟩⟩⟩

theorem ack_offset (view : ViewAt initial current location)
    (fields : CampusTCPTwoProgressWire.AckFields initial count produced)
    (within : initial.geometry.«prefix» + count ≤ (view.gateway.session.lane sender.direction).observed) :
    Admission.ackOffset (view.gateway.session.lane sender.direction) produced.source.packet.segment =
      initial.geometry.«prefix» + count := by
  have peerLane : view.gateway.session.peer sender.other.direction = view.gateway.session.lane sender.direction := by cases sender <;> rfl
  have result := CampusTCPTwoProgressGateway.ack_offset_add view.gateway.session sender.other.direction
    produced.source.packet.segment (initial.geometry.«prefix» + count) (by simpa only [peerLane] using within)
    (by rw [peerLane, view.gateway.identity.base, fields.acknowledgment, initial.geometry.senderCursor, Seq.add_add])
  simpa only [peerLane] using result

private theorem ack_reserved (view : ViewAt initial current location) (space : Reserved view)
    (value : Service current item ⟨view.gateway.session.entry.flow, sender.other.direction⟩ view.gateway.session actual served emission emitted)
    (located : item.value.gateway = location) (after : ViewAt initial value.move.after location)
    (fields : CampusTCPTwoProgressWire.AckFields initial count item.value.produced)
    (within : initial.geometry.«prefix» + count ≤ (view.gateway.session.lane sender.direction).observed) : Reserved after := by
  obtain ⟨processing, present, _, _, attached, _⟩ := value.facts.processing
  let selected := processingAt processing (processing_before value located)
  have direction : selected.prepared.attachment.direction = sender.other.direction := by rw [processingAt_attachment]; exact attached
  have peerLane : ∀ session : Admission.Session, session.peer selected.prepared.attachment.direction = session.lane sender.direction := by
    intro session
    rw [direction]
    cases sender <;> rfl
  have incoming : initial.geometry.«prefix» + lower.length + upper.length ≤
      Admission.ackOffset (view.gateway.session.peer selected.prepared.attachment.direction)
        served.ticket.value.source.packet.segment + served.ticket.value.source.packet.segment.window.val := by
    rw [peerLane, value.facts.ticket]
    change initial.geometry.«prefix» + lower.length + upper.length ≤
      Admission.ackOffset (view.gateway.session.lane sender.direction) item.value.produced.source.packet.segment +
        item.value.produced.source.packet.segment.window.val
    rw [ack_offset view fields within]
    have advertised := fields.window
    omega
  have result := CampusTCPTwoProgressGatewayWindow.result_peer_space selected.admitted view.gateway.phase
    (service_phase view value located after processing present) (initial.geometry.«prefix» + lower.length + upper.length)
    (by simpa only [peerLane, Reserved] using space) incoming
  simpa only [peerLane, Reserved] using result

private theorem acknowledged_after (view : ViewAt initial current location)
    (value : Service current item ⟨view.gateway.session.entry.flow, sender.other.direction⟩ view.gateway.session actual served emission emitted)
    (located : item.value.gateway = location) (after : ViewAt initial value.move.after location)
    (fields : CampusTCPTwoProgressWire.AckFields initial count item.value.produced)
    (within : initial.geometry.«prefix» + count ≤ (view.gateway.session.lane sender.direction).observed)
    (oldAck : (view.gateway.session.lane sender.direction).acknowledged ≤ initial.geometry.«prefix» + count) :
    (after.gateway.session.lane sender.direction).acknowledged = initial.geometry.«prefix» + count := by
  obtain ⟨processing, present, _, _, attached, _⟩ := value.facts.processing
  let selected := processingAt processing (processing_before value located)
  have direction : selected.prepared.attachment.direction = sender.other.direction := by rw [processingAt_attachment]; exact attached
  have peerLane : ∀ session : Admission.Session, session.peer selected.prepared.attachment.direction = session.lane sender.direction := by
    intro session
    rw [direction]
    cases sender <;> rfl
  have learned := CampusTCPTwoProgressGatewayWindow.result_window_fields selected.admitted view.gateway.phase
    (service_phase view value located after processing present)
  have lane : after.gateway.session.lane sender.direction =
      Admission.acknowledgedLane (view.gateway.session.lane sender.direction) served.ticket.value.source.packet.segment := by
    simpa only [peerLane, WireForwarding.Source.asInput] using learned.2.2
  rw [lane, Admission.acknowledgedLane_count]
  have offset : Admission.ackOffset (view.gateway.session.lane sender.direction)
      served.ticket.value.source.packet.segment = initial.geometry.«prefix» + count := by
    rw [value.facts.ticket]
    exact ack_offset view fields within
  rw [offset, Nat.max_eq_right oldAck]

structure AckServed (view : ViewAt initial current location) (item : Theory.Outstanding.Item (Ticket input.active input.passive))
    (count : Nat) (actual : Step input) where
  served : Served input
  emission : WireForwarding.Emission served.ticket.value.source.packet
  emitted : served.evidence.output = some emission
  value : Service current item ⟨view.gateway.session.entry.flow, sender.other.direction⟩ view.gateway.session actual served emission emitted
  next : ViewAt initial value.move.after location
  reserved : Reserved next
  acknowledged : (next.gateway.session.lane sender.direction).acknowledged = initial.geometry.«prefix» + count
  lowerRun : next.ranges.lowerRun = view.ranges.lowerRun
  upperRun : next.ranges.upperRun = view.ranges.upperRun

theorem serve_ack_at (view : ViewAt initial current location) (retained : Retained cut current)
    (checks : Checks cut initial.gatewayState.session.entry) (space : Reserved view)
    (item : Theory.Outstanding.Item (Ticket input.active input.passive)) (member : item ∈ current.report.final.work.pending)
    (phase : CampusTCPGatewayEnabled.ServicePhaseReady current.report.final item.value.gateway)
    (located : item.value.gateway = location) (ingress : item.value.ingress = checks.ingress location sender.other)
    (actor : item.value.produced.actor = sender.other) (fields : CampusTCPTwoProgressWire.AckFields initial count item.value.produced)
    (within : initial.geometry.«prefix» + count ≤ (view.gateway.session.lane sender.direction).observed)
    (oldAck : (view.gateway.session.lane sender.direction).acknowledged ≤ initial.geometry.«prefix» + count) :
    ∃ actual, Nonempty (AckServed view item count actual) := by
  have ready : CampusTCPService.ExistingDataReady (input.contextFor item.value.gateway)
      (beforeService input current.report.final item.value.gateway) item.value.source input.zone item.value.ingress
      ⟨view.gateway.session.entry.flow, sender.other.direction⟩ view.gateway.session item.value.produced.actor.nextHop := by
    rw [located, ingress, actor]
    exact ack_ready view retained checks fields within (by omega)
  obtain ⟨actual, served, emission, emitted, ⟨value⟩⟩ := CampusTCPTwoTransferNetwork.serve_at current item member phase
    ⟨view.gateway.session.entry.flow, sender.other.direction⟩ view.gateway.session ready
  obtain ⟨processing, present, _, _, _, _⟩ := value.facts.processing
  obtain ⟨after, lowerRun, upperRun⟩ := view.empty_service retained.retained (processingAt processing (processing_before value located))
    (by rw [value.facts.ticket]; exact fields.payload)
    (admission_after value located processing present) (tracker_after value located processing present)
  exact ⟨actual, ⟨⟨served, emission, emitted, value, after, ack_reserved view space value located after fields within,
    acknowledged_after view value located after fields within oldAck, lowerRun, upperRun⟩⟩⟩

end Netlib.Check.CampusTCPTwoTransferAdmission
