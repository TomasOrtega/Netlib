import Netlib.Check.CampusTCPTwoProgressGatewayAt
import Netlib.Check.CampusTCPTwoProgressReframe

/-!
# Admission at the current gateway location

The local gateway start retains the actual startup prefix.
Admission results lift back to the original task and its observation history.
-/

namespace Netlib.Check.CampusTCPTwoProgressGatewayAt

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart

namespace G
export CampusTCPTwoProgressGateway (Current)
end G

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {anchor current next : Cut input complete} {basis : StartupBasis anchor}
variable {origin location : Gateway} {start : GatewayStart anchor basis origin}

def CurrentAt.start_at (value : CurrentAt start current location)
    (retained : anchor.report.steps <+: current.report.steps) :
    GatewayStart current (CampusTCPTwoProgressReframe.retain_basis basis retained) location where
  session := value.session
  identity := start.identity.trans value.identity
  phase := value.phase
  trackerValid := value.trackerValid
  record := value.record
  member := value.member
  entry := value.entry
  confirmed := value.confirmed

@[simp] theorem CurrentAt.start_at_session (value : CurrentAt start current location)
    (retained : anchor.report.steps <+: current.report.steps) :
    (value.start_at retained).session = value.session := rfl

@[simp] theorem CurrentAt.start_at_record (value : CurrentAt start current location)
    (retained : anchor.report.steps <+: current.report.steps) :
    (value.start_at retained).record = value.record := rfl

def CurrentAt.local_current (value : CurrentAt start current location)
    (retained : anchor.report.steps <+: current.report.steps) :
    G.Current (value.start_at retained) current :=
  CampusTCPTwoProgressGateway.Current.ofStart (value.start_at retained)

@[simp] theorem CurrentAt.local_current_session (value : CurrentAt start current location)
    (retained : anchor.report.steps <+: current.report.steps) :
    (value.local_current retained).session = value.session := rfl

@[simp] theorem CurrentAt.local_current_record (value : CurrentAt start current location)
    (retained : anchor.report.steps <+: current.report.steps) :
    (value.local_current retained).record = value.record := rfl

def CurrentAt.lift_current (value : CurrentAt start current location)
    (retained : anchor.report.steps <+: current.report.steps)
    (later : G.Current (value.start_at retained) next) : CurrentAt start next location where
  session := later.session
  phase := later.phase
  identity := value.identity.trans later.identity
  observations := value.observations.trans later.observations
  trackerValid := later.trackerValid
  record := later.record
  member := later.member
  entry := later.entry
  confirmed := later.confirmed

@[simp] theorem CurrentAt.lift_current_session (value : CurrentAt start current location)
    (retained : anchor.report.steps <+: current.report.steps)
    (later : G.Current (value.start_at retained) next) :
    (value.lift_current retained later).session = later.session := rfl

@[simp] theorem CurrentAt.lift_current_record (value : CurrentAt start current location)
    (retained : anchor.report.steps <+: current.report.steps)
    (later : G.Current (value.start_at retained) next) :
    (value.lift_current retained later).record = later.record := rfl

theorem CurrentAt.known_of_slice (value : CurrentAt start current location)
    (retained : anchor.report.steps <+: current.report.steps) (direction : Admission.Direction)
    (segment : Segment) (run : Admission.Coverage.Run Nat)
    (member : run ∈ (value.session.lane direction).coverage.runs)
    (nonempty : segment.payload ≠ []) (offset : Nat)
    (slice : Theory.SparseCoverage.Slice run (Seq.distance (value.session.lane direction).base segment.sequence)
      segment.payload offset) :
    Admission.KnownRange (value.session.lane direction) value.session.entry direction segment
      (beforeService input current.report.final location).admission.observations :=
  (value.local_current retained).known_of_slice direction segment run member nonempty offset slice

theorem CurrentAt.binding (value : CurrentAt start current location)
    (retained : anchor.report.steps <+: current.report.steps) (record : ConntrackLifecycle.Record)
    (member : record ∈ (beforeService input current.report.final location).tracker.records)
    (same : record.entry.flow = value.session.entry.flow) : record.entry = value.session.entry :=
  (value.local_current retained).binding record member same

theorem CurrentAt.confirmed_binding (value : CurrentAt start current location)
    (retained : anchor.report.steps <+: current.report.steps) (record : ConntrackLifecycle.Record)
    (member : record ∈ (beforeService input current.report.final location).tracker.records)
    (same : record.entry.flow = value.session.entry.flow) : record = ⟨value.session.entry, true⟩ :=
  (value.local_current retained).confirmed_binding record member same

private def current_native (value : CurrentAt start current location)
    (native : CampusTCPRoundGateway.Native context before ingress start.session.entry direction hop) :
    CampusTCPRoundGateway.Native context before ingress value.session.entry direction hop := by
  rw [value.identity.entry]
  exact native

theorem CurrentAt.tracker_ready (value : CurrentAt start current location)
    (retained : anchor.report.steps <+: current.report.steps)
    (native : CampusTCPRoundGateway.Native context before ingress start.session.entry direction hop)
    (same : before.environment = (beforeService input current.report.final location).environment)
    (source : WireForwarding.Source) (zone : Nat)
    (header : source.packet.header = value.session.entry.flow.input direction)
    (zoneEq : value.session.entry.flow.zone direction = zone) :
    ConntrackLifecycle.ExistingReady
      ((beforeService input current.report.final location).configuration.pipeline context.routing)
      (beforeService input current.report.final location).tracker
      (CampusTCPService.packetInput (beforeService input current.report.final location) source zone).lifecycle
      ⟨value.session.entry.flow, direction⟩ hop :=
  (value.local_current retained).tracker_ready (current_native value native) same source zone header zoneEq

def CurrentAt.existing_ready (value : CurrentAt start current location)
    (retained : anchor.report.steps <+: current.report.steps)
    (native : CampusTCPRoundGateway.Native context before ingress start.session.entry direction hop)
    (same : before.environment = (beforeService input current.report.final location).environment)
    (source : WireForwarding.Source) (zone : Nat)
    (header : source.packet.header = value.session.entry.flow.input direction)
    (zoneEq : value.session.entry.flow.zone direction = zone)
    (data : Admission.DataReady value.session direction source.packet.segment)
    (ttl : 1 < source.packet.ip.packet.ttl.toNat) :
    CampusTCPService.ExistingDataReady context (beforeService input current.report.final location) source zone ingress
      ⟨value.session.entry.flow, direction⟩ value.session hop :=
  (value.local_current retained).existing_ready (current_native value native) same source zone header zoneEq data ttl

def CurrentAt.repeated_ready (value : CurrentAt start current location)
    (retained : anchor.report.steps <+: current.report.steps)
    (native : CampusTCPRoundGateway.Native context before ingress start.session.entry direction hop)
    (same : before.environment = (beforeService input current.report.final location).environment)
    (source : WireForwarding.Source) (zone : Nat)
    (header : source.packet.header = value.session.entry.flow.input direction)
    (zoneEq : value.session.entry.flow.zone direction = zone)
    (data : Admission.RepeatedReady value.session direction source.packet.segment
      (beforeService input current.report.final location).admission.observations)
    (ttl : 1 < source.packet.ip.packet.ttl.toNat) :
    CampusTCPService.ExistingRepeatedReady context (beforeService input current.report.final location) source zone ingress
      ⟨value.session.entry.flow, direction⟩ value.session hop :=
  (value.local_current retained).repeated_ready (current_native value native) same source zone header zoneEq data ttl

theorem CurrentAt.ack_ready (value : CurrentAt start current location)
    (retained : anchor.report.steps <+: current.report.steps) (direction : Admission.Direction)
    (segment : Segment) (position count : Nat) (profile : Admission.DataProfile segment)
    (empty : segment.payload = [])
    (sequence : segment.sequence = (value.session.sender direction).base.add position)
    (positionBound : position ≤ (value.session.sender direction).highEnd)
    (ack : segment.acknowledgment = (value.session.peer direction).base.add count)
    (countBound : count ≤ (value.session.peer direction).observed)
    (stale : (value.session.peer direction).acknowledged ≤ count + 65535) :
    Admission.AckReady value.session direction segment :=
  (value.local_current retained).ack_ready direction segment position count profile empty sequence positionBound ack countBound stale

variable {source : WireForwarding.Source}

theorem CurrentAt.processing_tracker (value : CurrentAt start current location)
    (retained : anchor.report.steps <+: current.report.steps)
    (processing : CampusTCPService.Processing context (beforeService input current.report.final location) source zone) :
    processing.outcome.state = (beforeService input current.report.final location).tracker :=
  (value.local_current retained).processing_tracker processing

theorem CurrentAt.processing_fields (value : CurrentAt start current location)
    (retained : anchor.report.steps <+: current.report.steps)
    (processing : CampusTCPService.Processing context (beforeService input current.report.final location) source zone) :
    ∃ after, processing.nextAdmission.phase = .data after ∧ Identity start.session after ∧
      processing.nextAdmission.observations = (beforeService input current.report.final location).admission.observations ++
        [Admission.observe source.asInput
          (CampusTCPService.packetInput (beforeService input current.report.final location) source zone).lifecycle
          processing.prepared] ∧
      processing.outcome.state = (beforeService input current.report.final location).tracker := by
  obtain ⟨after, phase, identity, observations, tracker⟩ := (value.local_current retained).processing_fields processing
  exact ⟨after, phase, value.identity.trans identity, observations, tracker⟩

theorem CurrentAt.after_processing (value : CurrentAt start current location)
    (retained : anchor.report.steps <+: current.report.steps)
    (processing : CampusTCPService.Processing context (beforeService input current.report.final location) source zone)
    (admission : (beforeService input next.report.final location).admission = processing.nextAdmission)
    (tracker : (beforeService input next.report.final location).tracker = processing.outcome.state) :
    Nonempty (CurrentAt start next location) := by
  obtain ⟨later⟩ := (value.local_current retained).after_processing processing admission tracker
  exact ⟨value.lift_current retained later⟩

end Netlib.Check.CampusTCPTwoProgressGatewayAt
