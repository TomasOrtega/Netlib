import Netlib.Check.CampusTCPRecoveryRoundGateway
import Netlib.Check.CampusTCPRoundStart
import Netlib.Protocol.TCP.AdmissionCoverageFacts

/-!
# Admission of one actual range through retries

The first service records its actual observation index.
Later services retain that source through repeats and covering ACKs.
-/

namespace Netlib.Check.CampusTCPRecoveryRoundAdmission

open Packet Protocol
open Protocol.TCP CampusTCPModel CampusTCPRoundStart
open Protocol.TCP.Admission
open CampusTCPRecoveryRoundGateway (Geometry)

structure Observed (seed : Admission.Session) (bytes : List UInt8) (actual : TCP.Admission.State) where
  session : Admission.Session
  phase : actual.phase = .data session
  firstSource : Nat
  firstSeen : Seen
  selected : actual.observations[firstSource]? = some firstSeen
  geometry : Geometry seed session bytes firstSource
  entry : firstSeen.attachment.entry = seed.entry
  direction : firstSeen.attachment.direction = .original
  profile : DataProfile firstSeen.segment
  sequence : firstSeen.segment.sequence = seed.original.base
  payload : firstSeen.segment.payload = bytes

inductive RangeState (seed : Admission.Session) (bytes : List UInt8) (actual : TCP.Admission.State) where
  | unseen (phase : actual.phase = .data seed)
  | observed (value : Observed seed bytes actual)

def RangeState.session (range : RangeState seed bytes actual) : Admission.Session :=
  match range with | .unseen _ => seed | .observed value => value.session

theorem RangeState.phase (range : RangeState seed bytes actual) : actual.phase = .data range.session := by
  cases range with
  | unseen phase => exact phase
  | observed value => exact value.phase

def RangeState.frame (range : RangeState seed bytes before) (same : before = after) : RangeState seed bytes after :=
  same ▸ range

def Observed.frame (value : Observed seed bytes before) (same : before = after) : Observed seed bytes after :=
  same ▸ value

variable {input : CampusTCPModel.Input} {events : List CampusTCPModel.Event} {report : Report input events}
  {complete : H.Completed input.active input.passive} {request : Request input}

def initial_actualphase (initial : Initial report complete request) :
    RangeState initial.session request.bytes initial.beforeService.admission := .unseen initial.phase

theorem Observed.known (value : Observed seed bytes actual) (segment : TCP.Segment)
    (nonempty : bytes ≠ []) (sequence : segment.sequence = seed.original.base) (payload : segment.payload = bytes) :
    KnownRange value.session.original value.session.entry .original segment actual.observations :=
  value.geometry.known segment nonempty (sequence.trans value.geometry.originalBase.symm) payload
    actual.observations value.firstSeen value.selected (value.entry.trans value.geometry.entry.symm)
    value.direction value.profile (value.sequence.trans value.geometry.originalBase.symm) value.payload

theorem Observed.repeated_ready (value : Observed seed bytes actual) (segment : TCP.Segment)
    (nonempty : bytes ≠ []) (profile : DataProfile segment)
    (sequence : segment.sequence = seed.original.base) (acknowledgment : segment.acknowledgment = seed.reply.base)
    (payload : segment.payload = bytes) (mss : bytes.length ≤ seed.serverMSS.limit) :
    RepeatedReady value.session .original segment actual.observations := by
  refine ⟨profile, value.known segment nonempty sequence payload, ?_, ?_, ?_⟩
  · simpa only [Admission.Session.peerMSS, value.geometry.serverMSS, payload] using mss
  · simp only [Admission.Session.peer, ackOffset, acknowledgment, value.geometry.replyBase, Seq.distance_self, Nat.zero_le]
  · simp only [Admission.Session.peer, value.geometry.reply_acknowledged, Nat.zero_le]

theorem Observed.ack_ready (value : Observed seed bytes actual) (segment : TCP.Segment)
    (profile : DataProfile segment) (empty : segment.payload = [])
    (sequence : segment.sequence = seed.reply.base)
    (acknowledgment : segment.acknowledgment = seed.original.base.add bytes.length) :
    AckReady value.session .reply segment :=
  value.geometry.ack_ready segment profile empty sequence acknowledgment

theorem Observed.coverageSources (value : Observed seed bytes actual) : actual.CoverageSources := by
  simp only [Admission.State.CoverageSources, value.phase]
  constructor
  · intro run member
    rw [value.geometry.originalCoverage] at member
    have same : run = (⟨0, bytes, 0, value.firstSource⟩ : Theory.SparseCoverage.Run Nat) := by
      simpa only [CampusTCPRoundAdmission.rangeCoverage, List.mem_singleton] using member
    subst run
    refine ⟨value.firstSeen, value.selected, value.entry.trans value.geometry.entry.symm,
      value.direction, ?_, value.payload.symm⟩
    rw [value.sequence, value.geometry.originalBase, Seq.distance_self]
  · intro run member
    rw [value.geometry.replyCoverage] at member
    cases member

variable {initial : Initial report complete request}

theorem RangeState.original_ready
    (range : RangeState initial.session request.bytes actual) (segment : TCP.Segment)
    (profile : DataProfile segment) (sequence : segment.sequence = input.active.iss.add 1)
    (acknowledgment : segment.acknowledgment = input.passive.iss.add 1) (payload : segment.payload = request.bytes) :
    FreshReady range.session .original segment ∨ RepeatedReady range.session .original segment actual.observations := by
  cases range with
  | unseen phase =>
    apply Or.inl
    exact CampusTCPRoundAdmission.initial_fresh_ready initial.session segment initial.aligned.originalCoverage
      initial.aligned.originalAcknowledged initial.aligned.replyCoverage initial.aligned.replyAcknowledged
      (sequence.trans initial.aligned.originalBase.symm) (acknowledgment.trans initial.aligned.replyBase.symm)
      profile (by simpa only [payload] using request.nonempty)
      (by simpa only [payload, initial.aligned.serverMSS] using request.peer_mss complete)
      (by simpa only [payload, initial.aligned.originalWindow] using request.receiveFits)
      (by simpa only [payload] using request.epoch complete)
  | observed value =>
    apply Or.inr
    exact value.repeated_ready segment request.nonempty profile (sequence.trans initial.aligned.originalBase.symm)
      (acknowledgment.trans initial.aligned.replyBase.symm) payload
      (by simpa only [initial.aligned.serverMSS] using request.peer_mss complete)

def RangeState.original_service_ready (native : NativeEnv initial) (current : CampusTCPService.Before)
    (range : RangeState initial.session request.bytes current.admission)
    (same : initial.beforeService.environment = current.environment) (source : TCP.WireForwarding.Source)
    (header : source.packet.header = Output.reverse complete.certificate.activeSeed.core.inbound)
    (valid : current.tracker.Valid) (records : current.tracker.records = [⟨initial.entry, true⟩])
    (profile : DataProfile source.packet.segment) (sequence : source.packet.segment.sequence = input.active.iss.add 1)
    (acknowledgment : source.packet.segment.acknowledgment = input.passive.iss.add 1)
    (payload : source.packet.segment.payload = request.bytes) (ttl : 1 < source.packet.ip.packet.ttl.toNat) :
    Sum (CampusTCPService.ExistingDataReady (input.contextFor .primary) current source input.zone native.dataIngress
      ⟨initial.entry.flow, .original⟩ range.session "server")
      (CampusTCPService.ExistingRepeatedReady (input.contextFor .primary) current source input.zone native.dataIngress
      ⟨initial.entry.flow, .original⟩ range.session "server") := by
  cases range with
  | unseen phase =>
    exact .inl (CampusTCPRoundGateway.original_ready input complete initial.aligned native.original current same source
      header valid records phase sequence acknowledgment profile (by simpa only [payload] using request.nonempty)
      (by simpa only [payload] using request.peer_mss complete) (by simpa only [payload] using request.receiveFits)
      (by simpa only [payload] using request.epoch complete) ttl)
  | observed value =>
    apply Sum.inr
    exact CampusTCPRecoveryRoundGateway.repeated_ready native.original current same source input.zone
      (header.trans initial.aligned.clientInput) initial.aligned.originalZone valid records value.session
      (value.geometry.entry.trans initial.aligned.entryEq) value.phase
      (value.repeated_ready source.packet.segment request.nonempty profile (sequence.trans initial.aligned.originalBase.symm)
        (acknowledgment.trans initial.aligned.replyBase.symm) payload
        (by simpa only [initial.aligned.serverMSS] using request.peer_mss complete)) ttl

def Observed.ack_service_ready (native : NativeEnv initial) (current : CampusTCPService.Before)
    (value : Observed initial.session request.bytes current.admission)
    (same : initial.beforeService.environment = current.environment) (source : TCP.WireForwarding.Source)
    (header : source.packet.header = Output.reverse complete.certificate.passiveSeed.core.inbound)
    (valid : current.tracker.Valid) (records : current.tracker.records = [⟨initial.entry, true⟩])
    (profile : DataProfile source.packet.segment) (empty : source.packet.segment.payload = [])
    (sequence : source.packet.segment.sequence = input.passive.iss.add 1)
    (acknowledgment : source.packet.segment.acknowledgment = (input.active.iss.add 1).add request.bytes.length)
    (ttl : 1 < source.packet.ip.packet.ttl.toNat) :
    CampusTCPService.ExistingDataReady (input.contextFor .primary) current source input.zone native.ackIngress
      ⟨initial.entry.flow, .reply⟩ value.session "client" :=
  CampusTCPRoundGateway.existing_ready native.reply current same source input.zone
    (header.trans initial.aligned.serverInput) initial.aligned.replyZone valid records value.session
    (value.geometry.entry.trans initial.aligned.entryEq) value.phase
    (.inr (value.ack_ready source.packet.segment profile empty (sequence.trans initial.aligned.replyBase.symm)
      (by simpa only [initial.aligned.originalBase] using acknowledgment))) ttl

private theorem processing_observations (processing : CampusTCPService.Processing context before packet zone)
    (session : Admission.Session) (phase : before.admission.phase = .data session) :
    processing.nextAdmission.observations = before.admission.observations ++
      [observe packet.asInput (CampusTCPService.packetInput before packet zone).lifecycle processing.prepared] := by
  rw [CampusTCPRoundAdmission.Processing.committed_data processing session phase]
  exact processing.admitted.ledger

theorem fresh_processing (initial : Initial report complete request)
    (processing : CampusTCPService.Processing context before packet zone)
    (phase : before.admission.phase = .data initial.session)
    (direction : processing.prepared.attachment.direction = .original)
    (profile : DataProfile packet.packet.segment) (sequence : packet.packet.segment.sequence = input.active.iss.add 1)
    (acknowledgment : packet.packet.segment.acknowledgment = input.passive.iss.add 1)
    (payload : packet.packet.segment.payload = request.bytes) :
    Nonempty (Observed initial.session request.bytes processing.nextAdmission) := by
  obtain ⟨after, afterPhase, fresh⟩ := CampusTCPRoundAdmission.Processing.original_empty_geometry processing
    initial.session phase direction initial.aligned.originalCoverage initial.aligned.originalAcknowledged
    initial.aligned.replyCoverage initial.aligned.replyAcknowledged
    (sequence.trans initial.aligned.originalBase.symm) (acknowledgment.trans initial.aligned.replyBase.symm)
    profile (by simpa only [payload] using request.nonempty)
    (by simpa only [payload, initial.aligned.serverMSS] using request.peer_mss complete)
    (by simpa only [payload, initial.aligned.originalWindow] using request.receiveFits)
    (by simpa only [payload] using request.epoch complete)
  have allowed : Allowed (.data initial.session) processing.prepared.attachment packet.packet.segment before.admission.observations :=
    phase ▸ processing.admitted.admitted
  refine ⟨⟨after, afterPhase, before.admission.observations.length,
    observe packet.asInput (CampusTCPService.packetInput before packet zone).lifecycle processing.prepared, ?_,
    Geometry.of_fresh fresh payload initial.aligned.replyCoverage, allowed.1, direction,
    profile, sequence.trans initial.aligned.originalBase.symm, payload⟩⟩
  rw [processing_observations processing initial.session phase]
  simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]

theorem Observed.repeated_processing (value : Observed seed bytes before.admission)
    (processing : CampusTCPService.Processing context before packet zone)
    (direction : processing.prepared.attachment.direction = .original) (nonempty : bytes ≠ [])
    (sequence : packet.packet.segment.sequence = seed.original.base) (payload : packet.packet.segment.payload = bytes) :
    Nonempty (Observed seed bytes processing.nextAdmission) := by
  obtain ⟨after, phase, geometry⟩ := CampusTCPRecoveryRoundGateway.Processing.original_repeat_geometry
    processing value.session value.phase direction value.geometry (value.known packet.packet.segment nonempty sequence payload)
  refine ⟨⟨after, phase, value.firstSource, value.firstSeen, ?_, geometry,
    value.entry, value.direction, value.profile, value.sequence, value.payload⟩⟩
  rw [processing_observations processing value.session value.phase]
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp value.selected).1]
  exact value.selected

theorem RangeState.original_processing (initial : Initial report complete request)
    (range : RangeState initial.session request.bytes before.admission)
    (processing : CampusTCPService.Processing context before packet zone)
    (direction : processing.prepared.attachment.direction = .original)
    (profile : DataProfile packet.packet.segment) (sequence : packet.packet.segment.sequence = input.active.iss.add 1)
    (acknowledgment : packet.packet.segment.acknowledgment = input.passive.iss.add 1)
    (payload : packet.packet.segment.payload = request.bytes) :
    Nonempty (Observed initial.session request.bytes processing.nextAdmission) := by
  cases range with
  | unseen phase => exact fresh_processing initial processing phase direction profile sequence acknowledgment payload
  | observed value =>
    exact value.repeated_processing processing direction request.nonempty
      (sequence.trans initial.aligned.originalBase.symm) payload

theorem Observed.ack_processing (value : Observed seed bytes before.admission)
    (processing : CampusTCPService.Processing context before packet zone)
    (direction : processing.prepared.attachment.direction = .reply)
    (profile : DataProfile packet.packet.segment) (empty : packet.packet.segment.payload = [])
    (sequence : packet.packet.segment.sequence = seed.reply.base)
    (acknowledgment : packet.packet.segment.acknowledgment = seed.original.base.add bytes.length) :
    ∃ next : Observed seed bytes processing.nextAdmission, next.session.original.acknowledged = bytes.length := by
  obtain ⟨after, phase, geometry, acknowledged⟩ := CampusTCPRecoveryRoundGateway.Processing.reply_covering_geometry
    processing value.session value.phase direction value.geometry profile empty sequence acknowledgment
  refine ⟨⟨after, phase, value.firstSource, value.firstSeen, ?_, geometry,
    value.entry, value.direction, value.profile, value.sequence, value.payload⟩, acknowledged⟩
  rw [processing_observations processing value.session value.phase]
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp value.selected).1]
  exact value.selected

end Netlib.Check.CampusTCPRecoveryRoundAdmission
