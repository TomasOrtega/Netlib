import Netlib.Check.CampusTCPStartupServiceEnabled
import Netlib.Check.CampusTCPRoundEnvironment
import Netlib.Check.CampusTCPGapProgressGateway

/-!
# Native startup checks from the installed cold environment

The candidate comes from the installed NAT program and original header.
Existing original controls retain the real record's seen-reply flag.
-/

namespace Netlib.Check.CampusTCPStartupNative

open Packet Protocol CampusTCPService

abbrev Direction := FlowNAT.Direction

def selectedEntry (before : Before) (zone : Nat) (header : Header) : NetfilterNAT.Entry :=
  before.configuration.nat.candidate zone header

structure Path (context : CampusTCPService.Context) (before : Before) (entry : NetfilterNAT.Entry) (direction : Direction) where
  ingress : I.InterfaceRef
  hop : String
  checks : Checks context before ingress
  budget : checks.budget = 100000
  forwardComparison : checks.forward.passed = true
  guardComparison : checks.guard.passed = true
  ingressPermit : before.guard.permits ingress.ifindex.val (entry.flow.input direction) = true
  covered : context.application.any (·.accepts (entry.flow.input direction)) = true
  route : Routing.nextHop (before.configuration.pipeline context.routing).routes
    ((ConntrackLifecycle.destinationStage entry direction).apply (entry.flow.input direction)).destination = some hop
  forward : StatefulACL.Policy.evaluate (before.configuration.pipeline context.routing).forwardDefault
    (before.configuration.pipeline context.routing).forward .established
    ((ConntrackLifecycle.destinationStage entry direction).apply (entry.flow.input direction)) = .permit
  late : StatefulACL.Policy.evaluate (before.configuration.pipeline context.routing).lateDefault
    (before.configuration.pipeline context.routing).late .established
    ((ConntrackLifecycle.sourceStage entry direction).apply
      ((ConntrackLifecycle.destinationStage entry direction).apply (entry.flow.input direction))) = .permit

structure Profile (context : CampusTCPService.Context) (before : Before) (zone : Nat) (header : Header) where
  zoneBound : zone < 65536
  compatible : (selectedEntry before zone header).Compatible
  original : (selectedEntry before zone header).flow.original = header
  originalZone : (selectedEntry before zone header).flow.originalZone = zone
  replyZone : (selectedEntry before zone header).flow.replyZone = zone
  trackerValid : before.tracker.Valid
  freshKeys : ConntrackLifecycle.FreshKeys before.tracker (selectedEntry before zone header)
  empty : before.admission.phase = .empty
  paths : ∀ direction, Path context before (selectedEntry before zone header) direction
  newForward : StatefulACL.Policy.evaluate (before.configuration.pipeline context.routing).forwardDefault
    (before.configuration.pipeline context.routing).forward .new
    ((ConntrackLifecycle.destinationStage (selectedEntry before zone header) .original).apply
      (selectedEntry before zone header).flow.original) = .permit
  newLate : StatefulACL.Policy.evaluate (before.configuration.pipeline context.routing).lateDefault
    (before.configuration.pipeline context.routing).late .new
    ((ConntrackLifecycle.sourceStage (selectedEntry before zone header) .original).apply
      ((ConntrackLifecycle.destinationStage (selectedEntry before zone header) .original).apply
        (selectedEntry before zone header).flow.original)) = .permit

variable {context : CampusTCPService.Context} {initial current : Before} {zone : Nat} {header : Header}

abbrev Profile.entry (_profile : Profile context initial zone header) := selectedEntry initial zone header

theorem Profile.zone_eq (profile : Profile context initial zone header) (direction : Direction) :
    profile.entry.flow.zone direction = zone := by
  cases direction
  · exact profile.originalZone
  · exact profile.replyZone

theorem Profile.fresh_forward (profile : Profile context initial zone header) :
    ConntrackLifecycle.FreshForwardConditions (initial.configuration.pipeline context.routing)
      profile.entry.flow.original profile.entry (profile.paths .original).hop :=
  ⟨(profile.paths .original).route, profile.newForward, profile.newLate⟩

theorem Profile.forward_conditions (profile : Profile context initial zone header) (record : ConntrackLifecycle.Record)
    (entry : record.entry = profile.entry) (direction : Direction) :
    ConntrackLifecycle.ForwardConditions (initial.configuration.pipeline context.routing)
      (profile.entry.flow.input direction) (ConntrackLifecycle.selectedAttachment record direction)
      (profile.paths direction).hop := by
  cases record with
  | mk actual seen =>
    dsimp only at entry
    subst actual
    cases direction with
    | original =>
      cases seen
      · exact ⟨rfl, (profile.paths .original).route, profile.newForward, profile.newLate⟩
      · exact ⟨rfl, (profile.paths .original).route, (profile.paths .original).forward, (profile.paths .original).late⟩
    | reply => exact ⟨rfl, (profile.paths .reply).route, (profile.paths .reply).forward, (profile.paths .reply).late⟩

theorem Profile.binding (profile : Profile context initial zone header) (valid : current.tracker.Valid)
    (selected : ConntrackLifecycle.Record) (member : selected ∈ current.tracker.records)
    (entry : selected.entry = profile.entry) (record : ConntrackLifecycle.Record)
    (present : record ∈ current.tracker.records) (same : record.entry.flow = profile.entry.flow) :
    record.entry = profile.entry := by
  have equal := CampusTCPGapProgressGateway.tracker_record_unique current.tracker valid present member
    (same.trans (congrArg NetfilterNAT.Entry.flow entry).symm)
  exact (congrArg ConntrackLifecycle.Record.entry equal).trans entry

theorem Profile.existing_tracker_ready (profile : Profile context initial zone header)
    (environment : initial.environment = current.environment) (source : W.Source) (direction : Direction)
    (inputHeader : source.packet.header = profile.entry.flow.input direction)
    (valid : current.tracker.Valid) (selected : ConntrackLifecycle.Record)
    (member : selected ∈ current.tracker.records) (entry : selected.entry = profile.entry) :
    ConntrackLifecycle.ExistingReady (current.configuration.pipeline context.routing) current.tracker
      (packetInput current source zone).lifecycle ⟨profile.entry.flow, direction⟩ (profile.paths direction).hop := by
  have configuration := congrArg Before.Environment.configuration environment
  change initial.configuration = current.configuration at configuration
  have flowMember : profile.entry.flow ∈ current.tracker.model.entries :=
    List.mem_map.mpr ⟨selected, member, congrArg NetfilterNAT.Entry.flow entry⟩
  have found : current.tracker.model.lookup zone source.packet.header = some ⟨profile.entry.flow, direction⟩ := by
    have lookup := FlowNAT.Snapshot.lookup_complete _ valid.1 ⟨profile.entry.flow, direction⟩ flowMember
    simpa only [FlowNAT.Hit.key, FlowNAT.Entry.key, profile.zone_eq direction, inputHeader] using lookup
  refine ⟨valid, profile.zoneBound, ?_, ?_, found, ?_⟩
  · have tcp : source.packet.header.protocol = Packet.Protocol.tcp := by simp only [TCP.DecodedIPv4.header]
    simp only [packetInput, TCP.WireForwarding.Input.lifecycle, Conntrack.transport, tcp, true_or, decide_true]
  · change (if (current.tracker.model.lookup zone source.packet.header).isNone then _ else none) = none
    rw [found]
    rfl
  · intro record present same
    have actual := profile.binding valid selected member entry record present same
    change ConntrackLifecycle.ForwardConditions (current.configuration.pipeline context.routing)
      source.packet.header (ConntrackLifecycle.selectedAttachment record direction) (profile.paths direction).hop
    rw [← configuration, inputHeader]
    exact profile.forward_conditions record actual direction

def Profile.existing_admission_ready (profile : Profile context initial zone header)
    (environment : initial.environment = current.environment) (source : W.Source) (direction : Direction)
    (inputHeader : source.packet.header = profile.entry.flow.input direction)
    (valid : current.tracker.Valid) (selected : ConntrackLifecycle.Record)
    (member : selected ∈ current.tracker.records) (entry : selected.entry = profile.entry)
    (admission : ∀ record ∈ current.tracker.records, record.entry.flow = profile.entry.flow →
      X.Allowed mode current.admission.phase (ConntrackLifecycle.selectedAttachment record direction)
        source.packet.segment current.admission.observations)
    (ttl : 1 < source.packet.ip.packet.ttl.toNat) :
    ExistingAdmissionReady context current source zone (profile.paths direction).ingress
      ⟨profile.entry.flow, direction⟩ (profile.paths direction).hop mode := by
  let path := profile.paths direction
  have guard := congrArg Before.Environment.guard environment
  change initial.guard = current.guard at guard
  refine ⟨path.checks.reframe current environment, ?_, ?_,
    profile.existing_tracker_ready environment source direction inputHeader valid selected member entry,
    admission, ttl, ?_, ?_, ?_⟩
  · exact (Checks.reframe_budget _ _ environment).trans path.budget
  · rw [← guard, inputHeader]
    exact path.ingressPermit
  · exact (Checks.reframe_forward_passed _ _ environment).trans path.forwardComparison
  · exact (Checks.reframe_guard_passed _ _ environment).trans path.guardComparison
  · simpa only [coverage, inputHeader] using path.covered

def Profile.fresh_ready (profile : Profile context initial zone header)
    (environment : initial.environment = current.environment) (source : W.Source)
    (inputHeader : source.packet.header = header) (valid : current.tracker.Valid)
    (keys : ConntrackLifecycle.FreshKeys current.tracker profile.entry) (empty : current.admission.phase = .empty)
    (syn : TCP.Admission.Startup source.packet.segment 2) (ttl : 1 < source.packet.ip.packet.ttl.toNat) :
    FreshSynReady context current source zone (profile.paths .original).ingress
      profile.entry (profile.paths .original).hop := by
  let path := profile.paths .original
  have configuration := congrArg Before.Environment.configuration environment
  change initial.configuration = current.configuration at configuration
  have guard := congrArg Before.Environment.guard environment
  change initial.guard = current.guard at guard
  have sourceHeader : source.packet.header = profile.entry.flow.original := inputHeader.trans profile.original.symm
  have absent : current.tracker.model.lookup zone source.packet.header = none := by
    rw [inputHeader, ← profile.original, ← profile.originalZone]
    exact ConntrackLifecycle.fresh_lookup_none keys
  refine ⟨path.checks.reframe current environment, ?_, ?_, valid, profile.zoneBound, ?_, profile.compatible,
    ⟨profile.original.trans inputHeader.symm, profile.originalZone⟩, keys, empty, syn, ?_, ttl, ?_, ?_, ?_⟩
  · exact (Checks.reframe_budget _ _ environment).trans path.budget
  · rw [← guard, sourceHeader]
    exact path.ingressPermit
  · change (if (current.tracker.model.lookup zone source.packet.header).isNone then _ else none) = some profile.entry
    rw [absent]
    simp only [Option.isNone_none, ite_true]
    rw [← configuration, inputHeader]
    rfl
  · rw [← configuration, sourceHeader]
    exact profile.fresh_forward
  · exact (Checks.reframe_forward_passed _ _ environment).trans path.forwardComparison
  · exact (Checks.reframe_guard_passed _ _ environment).trans path.guardComparison
  · change context.application.any (fun traffic => traffic.accepts source.packet.header) = true
    rw [sourceHeader]
    exact path.covered

def Profile.fresh_at_initial (profile : Profile context initial zone header) (source : W.Source)
    (inputHeader : source.packet.header = header) (syn : TCP.Admission.Startup source.packet.segment 2)
    (ttl : 1 < source.packet.ip.packet.ttl.toNat) :
    FreshSynReady context initial source zone (profile.paths .original).ingress
      profile.entry (profile.paths .original).hop :=
  profile.fresh_ready rfl source inputHeader profile.trackerValid profile.freshKeys profile.empty syn ttl

end Netlib.Check.CampusTCPStartupNative
