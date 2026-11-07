import Netlib.Check.CampusTCPTwoProgressGatewayState
import Netlib.Check.CampusTCPTransferFacts

/-!
# Current gateway evidence at its actual location

Installation changes the location and keeps the original task and range identities.
-/

namespace Netlib.Check.CampusTCPTwoProgressGatewayAt

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart CampusTCPTwoProgressCoverage

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {anchor current next : Cut input complete} {basis : StartupBasis anchor} {origin location target : Gateway}

structure CurrentAt (start : GatewayStart anchor basis origin) (current : Cut input complete) (location : Gateway) where
  session : Admission.Session
  phase : (beforeService input current.report.final location).admission.phase = .data session
  identity : Identity start.session session
  observations : (beforeService input anchor.report.final origin).admission.observations <+:
    (beforeService input current.report.final location).admission.observations
  trackerValid : (beforeService input current.report.final location).tracker.Valid
  record : ConntrackLifecycle.Record
  member : record ∈ (beforeService input current.report.final location).tracker.records
  entry : record.entry = session.entry
  confirmed : record.seenReply = true

variable {start : GatewayStart anchor basis origin}

def CurrentAt.ofCurrent (value : CampusTCPTwoProgressGateway.Current start current) : CurrentAt start current origin :=
  ⟨value.session, value.phase, value.identity, value.observations, value.trackerValid,
    value.record, value.member, value.entry, value.confirmed⟩

def CurrentAt.toCurrent (value : CurrentAt start current origin) : CampusTCPTwoProgressGateway.Current start current :=
  ⟨value.session, value.phase, value.identity, value.observations, value.trackerValid,
    value.record, value.member, value.entry, value.confirmed⟩

@[simp] theorem CurrentAt.toCurrent_ofCurrent (value : CampusTCPTwoProgressGateway.Current start current) :
    (CurrentAt.ofCurrent value).toCurrent = value := by cases value; rfl

@[simp] theorem CurrentAt.ofCurrent_toCurrent (value : CurrentAt start current origin) :
    CurrentAt.ofCurrent value.toCurrent = value := by cases value; rfl

def CurrentAt.ofStart (start : GatewayStart anchor basis origin) : CurrentAt start anchor origin :=
  CurrentAt.ofCurrent (CampusTCPTwoProgressGateway.Current.ofStart start)

def CurrentAt.reframe (value : CurrentAt start current location)
    (same : beforeService input next.report.final location = beforeService input current.report.final location) :
    CurrentAt start next location :=
  ⟨value.session, by rw [same]; exact value.phase, value.identity,
    by rw [same]; exact value.observations, by rw [same]; exact value.trackerValid,
    value.record, by rw [same]; exact value.member, value.entry, value.confirmed⟩

def CurrentAt.relocate (value : CurrentAt start current location)
    (copied : (next.report.final.resident target).transport = (current.report.final.resident location).transport) :
    CurrentAt start next target where
  session := value.session
  phase := by change (next.report.final.resident target).transport.admission.phase = _; rw [copied]; exact value.phase
  identity := value.identity
  observations := by
    change _ <+: (next.report.final.resident target).transport.admission.observations
    rw [copied]
    exact value.observations
  trackerValid := by change (next.report.final.resident target).transport.tracker.Valid; rw [copied]; exact value.trackerValid
  record := value.record
  member := by change value.record ∈ (next.report.final.resident target).transport.tracker.records; rw [copied]; exact value.member
  entry := value.entry
  confirmed := value.confirmed

@[simp] theorem CurrentAt.relocate_session (value : CurrentAt start current location)
    (copied : (next.report.final.resident target).transport = (current.report.final.resident location).transport) :
    (value.relocate copied).session = value.session := rfl

@[simp] theorem CurrentAt.relocate_record (value : CurrentAt start current location)
    (copied : (next.report.final.resident target).transport = (current.report.final.resident location).transport) :
    (value.relocate copied).record = value.record := rfl

theorem CurrentAt.coverage_sources (_value : CurrentAt start current location) :
    (beforeService input current.report.final location).admission.CoverageSources :=
  (current.report.final.resident location).history.coverage_sources

def CurrentAt.source (value : CurrentAt start current location) (direction : Admission.Direction)
    (run : Admission.Coverage.Run Nat) (member : run ∈ (value.session.lane direction).coverage.runs) :
    Admission.CoverageSource (beforeService input current.report.final location).admission.observations
      value.session.entry direction (value.session.lane direction) run :=
  (value.session.lane direction).coverageSource _ _ _
    (Admission.State.coverage_sources_lane _ value.coverage_sources value.session value.phase direction) run member

def CurrentAt.coverage_origin (value : CurrentAt start current location) (direction : Admission.Direction)
    (run : Admission.Coverage.Run Nat) (member : run ∈ (value.session.lane direction).coverage.runs) :
    Checkpoint.CoverageOrigin (current.report.final.resident location).history value.session direction run :=
  (current.report.final.resident location).history.coverageOrigin value.session value.phase direction run member

theorem CurrentAt.lookup (value : CurrentAt start current location) (direction : Admission.Direction) :
    (beforeService input current.report.final location).tracker.model.lookup
      (value.session.entry.flow.zone direction) (value.session.entry.flow.input direction) =
      some ⟨value.session.entry.flow, direction⟩ := by
  have member : value.session.entry.flow ∈ (beforeService input current.report.final location).tracker.model.entries :=
    List.mem_map.mpr ⟨value.record, value.member, congrArg NetfilterNAT.Entry.flow value.entry⟩
  simpa only [FlowNAT.Hit.key, FlowNAT.Entry.key] using FlowNAT.Snapshot.lookup_complete _
    value.trackerValid.1 ⟨value.session.entry.flow, direction⟩ member

theorem install_transport (move : Move current actual) (executionNS : IngressAttachment.NamespaceRef)
    (event : actual.event = .installCheckpoint executionNS) (installation : InstalledCheckpoint)
    (present : actual.result.installation = some installation) :
    move.after.report.final.standby.transport = current.report.final.primary.transport := by
  have source := CampusTCPTransferFacts.installation_origin actual executionNS event installation present
  rw [move.final, source.copied, ← source.cut, move.beforeEq]

private theorem installation_history (installation : Checkpoint.Installation snapshot history prior) :
    HEq installation.history snapshot.history := by
  unfold Checkpoint.Installation.history
  exact eqRec_heq installation.copied.symm snapshot.history

theorem install_history (move : Move current actual) (executionNS : IngressAttachment.NamespaceRef)
    (event : actual.event = .installCheckpoint executionNS) (installation : InstalledCheckpoint)
    (present : actual.result.installation = some installation) :
    HEq move.after.report.final.standby.history installation.checkpoint.snapshot.history := by
  obtain ⟨effect, custody, computed, result⟩ := actual.processed
  have selected : effect.installation = some installation := by simpa only [result] using present
  rw [event] at computed
  simp only [processCore, transferControl] at computed
  repeat' first
    | (cases computed <;> simp only at selected <;> cases selected)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  all_goals
    rw [move.final, result]
    exact installation_history _

theorem install_tracker (move : Move current actual) (executionNS : IngressAttachment.NamespaceRef)
    (event : actual.event = .installCheckpoint executionNS) (installation : InstalledCheckpoint)
    (present : actual.result.installation = some installation) :
    (beforeService input move.after.report.final .standby).tracker =
      (beforeService input current.report.final .primary).tracker :=
  congrArg Checkpoint.Gateway.tracker (install_transport move executionNS event installation present)

def CurrentAt.after_install (value : CurrentAt start current .primary) (move : Move current actual)
    (executionNS : IngressAttachment.NamespaceRef) (event : actual.event = .installCheckpoint executionNS)
    (installation : InstalledCheckpoint) (present : actual.result.installation = some installation) :
    CurrentAt start move.after .standby :=
  value.relocate (install_transport move executionNS event installation present)

theorem CurrentAt.after_install_observations (_value : CurrentAt start current .primary) (move : Move current actual)
    (executionNS : IngressAttachment.NamespaceRef) (event : actual.event = .installCheckpoint executionNS)
    (installation : InstalledCheckpoint) (present : actual.result.installation = some installation) :
    (beforeService input move.after.report.final .standby).admission.observations =
      (beforeService input current.report.final .primary).admission.observations :=
  congrArg (fun gateway : Checkpoint.Gateway => gateway.admission.observations)
    (install_transport move executionNS event installation present)

variable {cut : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}

structure ViewAt (initial : TwoWriteInitial cut sender gateway lower upper) (current : Cut input complete) (location : Gateway) where
  gateway : CurrentAt initial.gatewayState current location
  ranges : TwoRanges (initial.gatewayState.session.lane sender.direction).coverage
    (gateway.session.lane sender.direction).coverage initial.geometry.«prefix» lower upper
  peerCoverage : (gateway.session.peer sender.direction).coverage =
    (initial.gatewayState.session.peer sender.direction).coverage

def ViewAt.ofView (value : CampusTCPTwoProgressGatewayState.View initial current) : ViewAt initial current gateway :=
  ⟨CurrentAt.ofCurrent value.gateway, value.ranges, value.peerCoverage⟩

def ViewAt.toView (value : ViewAt initial current gateway) : CampusTCPTwoProgressGatewayState.View initial current :=
  ⟨value.gateway.toCurrent, value.ranges, value.peerCoverage⟩

@[simp] theorem ViewAt.toView_ofView (value : CampusTCPTwoProgressGatewayState.View initial current) :
    (ViewAt.ofView value).toView = value := by cases value; rfl

@[simp] theorem ViewAt.ofView_toView (value : ViewAt initial current gateway) :
    ViewAt.ofView value.toView = value := by cases value; rfl

def ViewAt.ofInitial (initial : TwoWriteInitial cut sender gateway lower upper) : ViewAt initial cut gateway :=
  ViewAt.ofView (CampusTCPTwoProgressGatewayState.View.ofInitial initial)

def ViewAt.reframe (value : ViewAt initial current location)
    (same : beforeService input next.report.final location = beforeService input current.report.final location) :
    ViewAt initial next location :=
  ⟨value.gateway.reframe same, value.ranges, value.peerCoverage⟩

def ViewAt.relocate (value : ViewAt initial current location)
    (copied : (next.report.final.resident target).transport = (current.report.final.resident location).transport) :
    ViewAt initial next target :=
  ⟨value.gateway.relocate copied, value.ranges, value.peerCoverage⟩

@[simp] theorem ViewAt.relocate_session (value : ViewAt initial current location)
    (copied : (next.report.final.resident target).transport = (current.report.final.resident location).transport) :
    (value.relocate copied).gateway.session = value.gateway.session := rfl

@[simp] theorem ViewAt.relocate_lower (value : ViewAt initial current location)
    (copied : (next.report.final.resident target).transport = (current.report.final.resident location).transport) :
    (value.relocate copied).ranges.lowerRun = value.ranges.lowerRun := rfl

@[simp] theorem ViewAt.relocate_upper (value : ViewAt initial current location)
    (copied : (next.report.final.resident target).transport = (current.report.final.resident location).transport) :
    (value.relocate copied).ranges.upperRun = value.ranges.upperRun := rfl

def ViewAt.after_install (value : ViewAt initial current .primary) (move : Move current actual)
    (executionNS : IngressAttachment.NamespaceRef) (event : actual.event = .installCheckpoint executionNS)
    (installation : InstalledCheckpoint) (present : actual.result.installation = some installation) :
    ViewAt initial move.after .standby :=
  value.relocate (install_transport move executionNS event installation present)

theorem ViewAt.after_install_fields (value : ViewAt initial current .primary) (move : Move current actual)
    (executionNS : IngressAttachment.NamespaceRef) (event : actual.event = .installCheckpoint executionNS)
    (installation : InstalledCheckpoint) (present : actual.result.installation = some installation) :
    (value.after_install move executionNS event installation present).gateway.session = value.gateway.session ∧
      (value.after_install move executionNS event installation present).ranges.lowerRun = value.ranges.lowerRun ∧
      (value.after_install move executionNS event installation present).ranges.upperRun = value.ranges.upperRun :=
  ⟨rfl, rfl, rfl⟩

def ViewAt.coverage_origin (value : ViewAt initial current location) (direction : Admission.Direction)
    (run : Admission.Coverage.Run Nat) (member : run ∈ (value.gateway.session.lane direction).coverage.runs) :
    Checkpoint.CoverageOrigin (current.report.final.resident location).history value.gateway.session direction run :=
  value.gateway.coverage_origin direction run member

def ViewAt.after_install_origin (value : ViewAt initial current .primary) (move : Move current actual)
    (executionNS : IngressAttachment.NamespaceRef) (event : actual.event = .installCheckpoint executionNS)
    (installation : InstalledCheckpoint) (present : actual.result.installation = some installation)
    (direction : Admission.Direction) (run : Admission.Coverage.Run Nat)
    (member : run ∈ (value.gateway.session.lane direction).coverage.runs) :
    Checkpoint.CoverageOrigin move.after.report.final.standby.history value.gateway.session direction run :=
  (value.after_install move executionNS event installation present).coverage_origin direction run member

end Netlib.Check.CampusTCPTwoProgressGatewayAt
