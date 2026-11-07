import Netlib.Check.CampusTCPGapProgressStart
import Netlib.Protocol.TCP.AdmissionRepeatEnabled
import Netlib.Protocol.TCP.CheckpointCoverageFacts
import Netlib.Protocol.TCP.AdmissionExecutionDataFacts

/-!
# Current two-lane coverage through held-gap retries

Coverage sources come from the selected gateway's actual stored history.
Repeats and empty ACKs retain both complete original ledgers.
-/

namespace Netlib.Check.CampusTCPGapProgressGateway

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPGapProgressStart

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {anchor cut : Cut input complete} {basis : StartupBasis anchor}

structure Current (start : GatewayStart anchor basis) (cut : Cut input complete) where
  session : Admission.Session
  phase : (beforeService input cut.report.final .standby).admission.phase = .data session
  shape : Shape start.seed session
  observations : (beforeService input anchor.report.final .standby).admission.observations <+:
    (beforeService input cut.report.final .standby).admission.observations
  trackerValid : (beforeService input cut.report.final .standby).tracker.Valid
  record : ConntrackLifecycle.Record
  member : record ∈ (beforeService input cut.report.final .standby).tracker.records
  entry : record.entry = session.entry
  confirmed : record.seenReply = true

def Current.ofStart (start : GatewayStart anchor basis) : Current start anchor :=
  ⟨start.seed, start.phase, Shape.refl _, List.prefix_refl _, start.trackerValid,
    start.record, start.member, start.entry, start.confirmed⟩

theorem Current.coverage_sources (_current : Current start cut) :
    (beforeService input cut.report.final .standby).admission.CoverageSources :=
  cut.report.final.standby.history.coverage_sources

def Current.source (current : Current start cut) (direction : Admission.Direction)
    (run : Admission.Coverage.Run Nat) (member : run ∈ (current.session.lane direction).coverage.runs) :
    Admission.CoverageSource (beforeService input cut.report.final .standby).admission.observations
      current.session.entry direction (current.session.lane direction) run :=
  (current.session.lane direction).coverageSource _ _ _
    (Admission.State.coverage_sources_lane _ current.coverage_sources current.session current.phase direction) run member

def Current.origin (current : Current start cut) (direction : Admission.Direction)
    (run : Admission.Coverage.Run Nat) (member : run ∈ (current.session.lane direction).coverage.runs) :
    Checkpoint.CoverageOrigin cut.report.final.standby.history current.session direction run :=
  cut.report.final.standby.history.coverageOrigin current.session current.phase direction run member

theorem Current.lower_member (current : Current start cut) (range : LowerRange start sender lower) :
    range.run ∈ (current.session.lane sender.direction).coverage.runs := by
  rw [current.shape.coverage]
  exact range.member

private theorem slice_compatible (runs : List (Theory.SparseCoverage.Run Meta))
    (ordered : runs.Pairwise Theory.SparseCoverage.Run.Before)
    (member : source ∈ runs) (slice : Theory.SparseCoverage.Slice source position payload offset) :
    Theory.SparseCoverage.Compatible
      (Theory.SparseCoverage.current state position payload metadata) runs := by
  induction runs with
  | nil => cases member
  | cons head tail ih =>
    obtain ⟨first, rest⟩ := List.pairwise_cons.mp ordered
    rcases List.mem_cons.mp member with same | inside
    · subst source
      intro run member
      rcases List.mem_cons.mp member with same | inside
      · subst run
        right; right
        simp only [Theory.SparseCoverage.current, Theory.SparseCoverage.Run.limit]
        have coordinates := slice.1
        have bounded := slice.2.1
        have bytes := slice.2.2
        refine ⟨by omega, by omega, ?_⟩
        have shifted : position - head.position = offset := by omega
        rw [shifted]
        exact bytes
      · left
        have order := first run inside
        unfold Theory.SparseCoverage.Run.Before Theory.SparseCoverage.Run.limit at order ⊢
        simp only [Theory.SparseCoverage.current]
        have coordinates := slice.1
        have bounded := slice.2.1
        omega
    · intro run member
      rcases List.mem_cons.mp member with same | later
      · subst run
        right; left
        have order := first source inside
        unfold Theory.SparseCoverage.Run.Before Theory.SparseCoverage.Run.limit at order ⊢
        simp only [Theory.SparseCoverage.current]
        have coordinates := slice.1
        omega
      · exact ih rest inside run later

theorem accept_slice_exists (state : Theory.SparseCoverage.State Meta) (source : Theory.SparseCoverage.Run Meta)
    (position : Nat) (payload : List UInt8) (metadata : Meta) (bound offset : Nat)
    (valid : state.Valid bound) (member : source ∈ state.runs) (nonempty : payload ≠ [])
    (slice : Theory.SparseCoverage.Slice source position payload offset) :
    ∃ placed, Theory.SparseCoverage.accept state position payload metadata bound = .ok placed ∧
      placed.state = state ∧ placed.source = source ∧ placed.offset = offset ∧ placed.novel = 0 := by
  have inside : position + payload.length ≤ bound := by
    have sourceBound := (valid.2.1 source member).2.1
    have coordinates := slice.1
    have bounded := slice.2.1
    unfold Theory.SparseCoverage.Run.limit at sourceBound
    omega
  obtain ⟨placed, accepted⟩ := Theory.SparseCoverage.accept_exists state position payload metadata bound valid nonempty inside
    (slice_compatible state.runs valid.1 member slice)
  exact ⟨placed, accepted, Theory.SparseCoverage.accept_first_source state position payload metadata bound placed
    accepted source member offset slice⟩

private theorem allowed_nonempty_profile
    (allowed : Admission.Allowed phase attachment segment observations) (nonempty : segment.payload ≠ []) :
    Admission.DataProfile segment := by
  cases phase with
  | empty =>
    have empty := allowed.2.2.2.2
    exact False.elim (nonempty empty)
  | syn entry iss window mss =>
    have empty := allowed.2.2.2.1.2.2
    exact False.elim (nonempty empty)
  | synAck entry clientISS clientWindow serverISS serverWindow clientMSS serverMSS =>
    have empty := allowed.2.2.2.1.2.2
    exact False.elim (nonempty empty)
  | data session =>
    have admitted := allowed.2.2
    cases selected : attachment.direction <;> simp only [selected] at admitted
    all_goals rcases admitted with fresh | repeated; exact fresh.1; exact repeated.1

theorem history_nonempty_profile (history : Checkpoint.History gateway) (index : Nat) (seen : Admission.Seen)
    (selected : gateway.admission.observations[index]? = some seen) (nonempty : seen.segment.payload ≠ []) :
    Admission.DataProfile seen.segment := by
  let origin := history.observationOrigin index seen selected
  rw [origin.segment] at nonempty ⊢
  exact allowed_nonempty_profile (AdmissionExecution.Result.nonempty_legacy origin.transition.admitted nonempty) nonempty

theorem Current.known_of_slice (current : Current start cut) (direction : Admission.Direction)
    (segment : Segment) (run : Admission.Coverage.Run Nat)
    (member : run ∈ (current.session.lane direction).coverage.runs)
    (nonempty : segment.payload ≠ []) (offset : Nat)
    (slice : Theory.SparseCoverage.Slice run (Seq.distance (current.session.lane direction).base segment.sequence)
      segment.payload offset) :
    Admission.KnownRange (current.session.lane direction) current.session.entry direction segment
      (beforeService input cut.report.final .standby).admission.observations := by
  have valid : (current.session.lane direction).Valid := by
    cases direction
    · exact current.session.originalValid
    · exact current.session.replyValid
  obtain ⟨placed, accepted, unchanged, sourceEq, offsetEq, novel⟩ := accept_slice_exists
    (current.session.lane direction).coverage run _ segment.payload
    (beforeService input cut.report.final .standby).admission.observations.length Admission.coverageBound offset
    valid.2.2.2 member nonempty slice
  let source := current.source direction run member
  have seenNonempty : source.seen.segment.payload ≠ [] := by
    rw [← source.evidence.bytes]
    exact (valid.2.2.2.2.1 run member).1
  have profile := history_nonempty_profile cut.report.final.standby.history run.metadata source.seen
    source.evidence.selected seenNonempty
  have highEnd := (current.session.lane direction).coverage.limit_le_highEnd run member
  have coordinates := slice.1
  have bounded := slice.2.1
  have bytes := slice.2.2
  have difference : Seq.distance (current.session.lane direction).base segment.sequence - run.position = offset := by omega
  unfold Admission.KnownRange Admission.placement
  rw [accepted]
  dsimp only
  rw [sourceEq, source.evidence.selected]
  refine ⟨novel, source.evidence.entry, source.evidence.direction, profile, seenNonempty, ?_, ?_, ?_, ?_⟩
  · rw [← source.evidence.position]
    omega
  · rw [← source.evidence.position, ← source.evidence.bytes]
    omega
  · rw [← source.evidence.position, ← source.evidence.bytes]
    exact highEnd
  · rw [← source.evidence.position, ← source.evidence.bytes, difference]
    exact bytes.symm

private def recordKeys (record : ConntrackLifecycle.Record) : List (Nat × Header) :=
  [record.entry.flow.key .original, record.entry.flow.key .reply]

private theorem records_unique (records : List ConntrackLifecycle.Record)
    (unique : (records.flatMap recordKeys).Nodup)
    (leftMember : left ∈ records) (rightMember : right ∈ records)
    (sameFlow : left.entry.flow = right.entry.flow) : left = right := by
  induction records with
  | nil => cases leftMember
  | cons head tail ih =>
    have keys : (head.entry.flow.key .original :: head.entry.flow.key .reply :: tail.flatMap recordKeys).Nodup := unique
    have first := List.nodup_cons.mp keys
    have rest := (List.nodup_cons.mp first.2).2
    rcases List.mem_cons.mp leftMember with rfl | leftTail
    · rcases List.mem_cons.mp rightMember with rfl | rightTail
      · rfl
      · have member : left.entry.flow.key .original ∈ tail.flatMap recordKeys := by
          apply List.mem_flatMap.mpr
          refine ⟨right, rightTail, ?_⟩
          simp only [recordKeys, List.mem_cons]
          exact Or.inl (congrArg (fun flow => flow.key .original) sameFlow)
        exact False.elim (first.1 (List.mem_cons_of_mem _ member))
    · rcases List.mem_cons.mp rightMember with rfl | rightTail
      · have member : right.entry.flow.key .original ∈ tail.flatMap recordKeys := by
          apply List.mem_flatMap.mpr
          refine ⟨left, leftTail, ?_⟩
          simp only [recordKeys, List.mem_cons]
          exact Or.inl (congrArg (fun flow => flow.key .original) sameFlow.symm)
        exact False.elim (first.1 (List.mem_cons_of_mem _ member))
      · exact ih rest leftTail rightTail

theorem tracker_record_unique (tracker : ConntrackLifecycle.State) (valid : tracker.Valid)
    (leftMember : left ∈ tracker.records) (rightMember : right ∈ tracker.records)
    (sameFlow : left.entry.flow = right.entry.flow) : left = right := by
  apply records_unique tracker.records _ leftMember rightMember sameFlow
  change (tracker.records.flatMap (fun record =>
    [record.entry.flow.key .original, record.entry.flow.key .reply])).Nodup
  simpa only [ConntrackLifecycle.State.model, FlowNAT.Snapshot.keys, FlowNAT.Snapshot.slots,
    List.flatMap_map, List.map_flatMap, List.map_cons, List.map_nil, FlowNAT.Hit.key, recordKeys, Function.comp_def] using valid.1.2

private theorem record_eq (record : ConntrackLifecycle.Record) (entry : NetfilterNAT.Entry)
    (same : record.entry = entry) (confirmed : record.seenReply = true) : record = ⟨entry, true⟩ := by
  cases record
  cases same
  cases confirmed
  rfl

theorem Current.binding (current : Current start cut) (record : ConntrackLifecycle.Record)
    (member : record ∈ (beforeService input cut.report.final .standby).tracker.records)
    (same : record.entry.flow = current.session.entry.flow) : record.entry = current.session.entry := by
  have equal := tracker_record_unique _ current.trackerValid member current.member
    (same.trans (congrArg NetfilterNAT.Entry.flow current.entry).symm)
  exact (congrArg ConntrackLifecycle.Record.entry equal).trans current.entry

theorem Current.confirmed_binding (current : Current start cut) (record : ConntrackLifecycle.Record)
    (member : record ∈ (beforeService input cut.report.final .standby).tracker.records)
    (same : record.entry.flow = current.session.entry.flow) : record = ⟨current.session.entry, true⟩ := by
  have equal := tracker_record_unique _ current.trackerValid member current.member
    (same.trans (congrArg NetfilterNAT.Entry.flow current.entry).symm)
  exact equal.trans (record_eq current.record current.session.entry current.entry current.confirmed)

theorem Current.lookup (current : Current start cut) (direction : Admission.Direction) :
    (beforeService input cut.report.final .standby).tracker.model.lookup
      (current.session.entry.flow.zone direction) (current.session.entry.flow.input direction) =
      some ⟨current.session.entry.flow, direction⟩ := by
  have member : current.session.entry.flow ∈ (beforeService input cut.report.final .standby).tracker.model.entries :=
    List.mem_map.mpr ⟨current.record, current.member, congrArg NetfilterNAT.Entry.flow current.entry⟩
  simpa only [FlowNAT.Hit.key, FlowNAT.Entry.key] using FlowNAT.Snapshot.lookup_complete _
    current.trackerValid.1 ⟨current.session.entry.flow, direction⟩ member

theorem Current.tracker_ready (current : Current start cut)
    (native : CampusTCPRoundGateway.Native context initial ingress start.seed.entry direction hop)
    (same : initial.environment = (beforeService input cut.report.final .standby).environment)
    (source : WireForwarding.Source) (zone : Nat)
    (header : source.packet.header = current.session.entry.flow.input direction)
    (zoneEq : current.session.entry.flow.zone direction = zone) :
    ConntrackLifecycle.ExistingReady
      ((beforeService input cut.report.final .standby).configuration.pipeline context.routing)
      (beforeService input cut.report.final .standby).tracker
      (CampusTCPService.packetInput (beforeService input cut.report.final .standby) source zone).lifecycle
      ⟨current.session.entry.flow, direction⟩ hop := by
  have configuration := congrArg CampusTCPService.Before.Environment.configuration same
  change initial.configuration = (beforeService input cut.report.final .standby).configuration at configuration
  have found : (beforeService input cut.report.final .standby).tracker.model.lookup zone source.packet.header =
      some ⟨current.session.entry.flow, direction⟩ := by
    rw [header, ← zoneEq]
    exact current.lookup direction
  refine ⟨current.trackerValid, ?_, ?_, ?_, found, ?_⟩
  · have compatible := current.trackerValid.2 current.record current.member
    rw [current.entry] at compatible
    simp only [CampusTCPService.packetInput, TCP.WireForwarding.Input.lifecycle]
    rw [← zoneEq]
    cases direction
    · exact compatible.1.2.2.1
    · exact compatible.1.2.2.2.1
  · have tcp : source.packet.header.protocol = Packet.Protocol.tcp := by simp only [DecodedIPv4.header]
    simp only [CampusTCPService.packetInput, TCP.WireForwarding.Input.lifecycle, Conntrack.transport, tcp, true_or, decide_true]
  · change (if ((beforeService input cut.report.final .standby).tracker.model.lookup zone source.packet.header).isNone then _ else none) = none
    rw [found]
    rfl
  · intro record member bound
    have equal := current.confirmed_binding record member bound
    rw [equal]
    change ConntrackLifecycle.ForwardConditions
      ((beforeService input cut.report.final .standby).configuration.pipeline context.routing)
      source.packet.header (ConntrackLifecycle.selectedAttachment ⟨current.session.entry, true⟩ direction) hop
    rw [← configuration, header, current.shape.entry]
    exact native.forwarding

def Current.existing_ready (current : Current start cut)
    (native : CampusTCPRoundGateway.Native context initial ingress start.seed.entry direction hop)
    (same : initial.environment = (beforeService input cut.report.final .standby).environment)
    (source : WireForwarding.Source) (zone : Nat)
    (header : source.packet.header = current.session.entry.flow.input direction)
    (zoneEq : current.session.entry.flow.zone direction = zone)
    (data : Admission.DataReady current.session direction source.packet.segment)
    (ttl : 1 < source.packet.ip.packet.ttl.toNat) :
    CampusTCPService.ExistingDataReady context (beforeService input cut.report.final .standby) source zone ingress
      ⟨current.session.entry.flow, direction⟩ current.session hop := by
  let checks := native.checks.reframe _ same
  have guard := congrArg CampusTCPService.Before.Environment.guard same
  change initial.guard = (beforeService input cut.report.final .standby).guard at guard
  refine ⟨checks, (CampusTCPService.Checks.reframe_budget _ _ same).trans native.budget,
    ?_, current.tracker_ready native same source zone header zoneEq, current.phase,
    current.binding, data, ttl,
    (CampusTCPService.Checks.reframe_forward_passed _ _ same).trans native.forwardComparison,
    (CampusTCPService.Checks.reframe_guard_passed _ _ same).trans native.guardComparison, ?_⟩
  · rw [← guard, header, current.shape.entry]
    exact native.ingressPermit
  · simp only [CampusTCPService.coverage, header, current.shape.entry]
    exact native.covered

def Current.repeated_ready (current : Current start cut)
    (native : CampusTCPRoundGateway.Native context initial ingress start.seed.entry direction hop)
    (same : initial.environment = (beforeService input cut.report.final .standby).environment)
    (source : WireForwarding.Source) (zone : Nat)
    (header : source.packet.header = current.session.entry.flow.input direction)
    (zoneEq : current.session.entry.flow.zone direction = zone)
    (data : Admission.RepeatedReady current.session direction source.packet.segment
      (beforeService input cut.report.final .standby).admission.observations)
    (ttl : 1 < source.packet.ip.packet.ttl.toNat) :
    CampusTCPService.ExistingRepeatedReady context (beforeService input cut.report.final .standby) source zone ingress
      ⟨current.session.entry.flow, direction⟩ current.session hop := by
  let checks := native.checks.reframe _ same
  have guard := congrArg CampusTCPService.Before.Environment.guard same
  change initial.guard = (beforeService input cut.report.final .standby).guard at guard
  refine ⟨checks, (CampusTCPService.Checks.reframe_budget _ _ same).trans native.budget,
    ?_, current.tracker_ready native same source zone header zoneEq, current.phase,
    current.binding, data, ttl,
    (CampusTCPService.Checks.reframe_forward_passed _ _ same).trans native.forwardComparison,
    (CampusTCPService.Checks.reframe_guard_passed _ _ same).trans native.guardComparison, ?_⟩
  · rw [← guard, header, current.shape.entry]
    exact native.ingressPermit
  · simp only [CampusTCPService.coverage, header, current.shape.entry]
    exact native.covered

private theorem observed_lt_modulus (lane : Admission.Lane) (valid : lane.Valid) : lane.observed < Seq.modulus := by
  have order := lane.coverage.frontier_le_highEnd
  change lane.observed ≤ lane.highEnd at order
  have epoch := valid.2.1
  unfold Seq.halfSpace Seq.modulus at *
  omega

private theorem highEnd_lt_modulus (lane : Admission.Lane) (valid : lane.Valid) : lane.highEnd < Seq.modulus := by
  have epoch := valid.2.1
  unfold Seq.halfSpace Seq.modulus at *
  omega

private theorem peer_ack_offset (session : Admission.Session) (direction : Admission.Direction) (segment : Segment)
    (ack : segment.acknowledgment = (session.peer direction).base.add (session.peer direction).observed) :
    Admission.ackOffset (session.peer direction) segment = (session.peer direction).observed := by
  rw [Admission.ackOffset, ack, Seq.distance_add, Nat.mod_eq_of_lt (observed_lt_modulus _ (session.peer_valid direction))]

theorem Current.lower_known (current : Current start cut) (range : LowerRange start sender lower)
    (segment : Segment) (nonempty : lower ≠ [])
    (sequence : segment.sequence = (current.session.lane sender.direction).base)
    (payload : segment.payload = lower) :
    Admission.KnownRange (current.session.lane sender.direction) current.session.entry sender.direction segment
      (beforeService input cut.report.final .standby).admission.observations := by
  apply current.known_of_slice sender.direction segment range.run (current.lower_member range)
    (by simpa only [payload] using nonempty) 0
  simp only [Theory.SparseCoverage.Slice, range.position, range.bytes, sequence, Seq.distance_self,
    payload, Nat.add_zero, Nat.zero_add, Nat.le_refl, List.drop_zero, List.take_length, and_self]

theorem Current.lower_admission_ready (current : Current start cut) (range : LowerRange start sender lower)
    (segment : Segment) (nonempty : lower ≠ []) (profile : Admission.DataProfile segment)
    (sequence : segment.sequence = (current.session.lane sender.direction).base)
    (payload : segment.payload = lower)
    (ack : segment.acknowledgment = (current.session.peer sender.direction).base.add
      (current.session.peer sender.direction).observed)
    (mss : lower.length ≤ (current.session.peerMSS sender.direction).limit) :
    Admission.RepeatedReady current.session sender.direction segment
      (beforeService input cut.report.final .standby).admission.observations := by
  have lane : current.session.sender sender.direction = current.session.lane sender.direction := by
    cases sender <;> rfl
  have offset := peer_ack_offset current.session sender.direction segment ack
  refine ⟨profile, ?_, ?_, ?_, ?_⟩
  · rw [lane]
    exact current.lower_known range segment nonempty sequence payload
  · simpa only [payload] using mss
  · rw [offset]
    exact Nat.le_refl _
  · rw [offset]
    have bound := (current.session.peer_valid sender.direction).1
    omega

theorem Current.covering_ack_ready (current : Current start cut) (direction : Admission.Direction)
    (segment : Segment) (profile : Admission.DataProfile segment) (empty : segment.payload = [])
    (sequence : segment.sequence = (current.session.sender direction).base.add
      (current.session.sender direction).highEnd)
    (ack : segment.acknowledgment = (current.session.peer direction).base.add
      (current.session.peer direction).observed) : Admission.AckReady current.session direction segment := by
  have offset := peer_ack_offset current.session direction segment ack
  refine ⟨profile, empty, ?_, ?_, ?_⟩
  · rw [sequence, Seq.distance_add, Nat.mod_eq_of_lt (highEnd_lt_modulus _ (current.session.sender_valid direction))]
    exact Nat.le_refl _
  · rw [offset]
    exact Nat.le_refl _
  · rw [offset]
    have bound := (current.session.peer_valid direction).1
    omega

private theorem data_mss (result : Admission.Result before packet lifecycle prepared)
    (phase : before.phase = .data session) (afterPhase : result.state.phase = .data after) :
    after.clientMSS = session.clientMSS ∧ after.serverMSS = session.serverMSS := by
  have allowed : Admission.Allowed (.data session) prepared.attachment packet.packet.segment before.observations :=
    phase ▸ result.admitted
  have same : Admission.Phase.data after = Admission.nextPhase (.data session) prepared.attachment packet.packet.segment allowed :=
    afterPhase.symm.trans (by simpa only [phase] using result.phase)
  simp only [Admission.nextPhase] at same
  repeat' split at same
  all_goals
    have equal := Admission.Phase.data.inj same
    rw [equal]
    exact ⟨rfl, rfl⟩

theorem result_identity (result : Admission.Result before packet lifecycle prepared)
    (phase : before.phase = .data session) :
    ∃ after, result.state.phase = .data after ∧ Identity session after := by
  obtain ⟨after, afterPhase, entry, originalBase, replyBase⟩ := result.data_fields phase
  have mss := data_mss result phase afterPhase
  refine ⟨after, afterPhase, entry, ?_, mss.1, mss.2⟩
  intro direction
  cases direction
  · exact originalBase
  · exact replyBase

theorem result_repeat_shape (result : Admission.Result before packet lifecycle prepared)
    (phase : before.phase = .data session)
    (known : Admission.KnownRange (session.lane prepared.attachment.direction) session.entry
      prepared.attachment.direction packet.packet.segment before.observations) :
    ∃ after, result.state.phase = .data after ∧ Shape session after ∧
      result.state.observations = before.observations ++ [Admission.observe packet lifecycle prepared] := by
  obtain ⟨after, afterPhase, identity⟩ := result_identity result phase
  obtain ⟨other, otherPhase, original, reply, ledger⟩ := result.repeated_frontier phase known
  have same : other = after := Admission.Phase.data.inj (otherPhase.symm.trans afterPhase)
  subst other
  exact ⟨after, afterPhase, ⟨identity, by intro direction; cases direction; exact original; exact reply⟩, ledger⟩

private theorem change_empty (lane : Admission.Lane) (segment : Segment) (source : Nat)
    (empty : segment.payload = []) (change : Admission.CoverageChange lane after segment source) :
    after.coverage = lane.coverage := by
  rcases change with same | ⟨placed, accepted, _⟩
  · exact same
  · have nonempty := (Theory.SparseCoverage.accept_stages lane.coverage
      (Seq.distance lane.base segment.sequence) segment.payload source Admission.coverageBound placed accepted).2.1
    exact False.elim (nonempty empty)

theorem result_empty_shape (result : Admission.Result before packet lifecycle prepared)
    (phase : before.phase = .data session) (empty : packet.packet.segment.payload = []) :
    ∃ after, result.state.phase = .data after ∧ Shape session after ∧
      result.state.observations = before.observations ++ [Admission.observe packet lifecycle prepared] := by
  obtain ⟨after, afterPhase, identity⟩ := result_identity result phase
  obtain ⟨other, otherPhase, change⟩ := result.coverage_transition phase
  have same : other = after := Admission.Phase.data.inj (otherPhase.symm.trans afterPhase)
  subst other
  rcases change with ⟨_, peer, changed⟩ | ⟨_, peer, changed⟩
  · have own := change_empty _ _ _ empty changed
    exact ⟨after, afterPhase, ⟨identity, by intro direction; cases direction; exact own; exact peer⟩, result.ledger⟩
  · have own := change_empty _ _ _ empty changed
    exact ⟨after, afterPhase, ⟨identity, by intro direction; cases direction; exact peer; exact own⟩, result.ledger⟩

theorem shape_peer_observed (shape : Shape session after) (direction : Admission.Direction) :
    (after.peer direction).observed = (session.peer direction).observed := by
  cases direction
  · exact congrArg Theory.SparseCoverage.State.frontier (shape.coverage .reply)
  · exact congrArg Theory.SparseCoverage.State.frontier (shape.coverage .original)

private theorem peer_acknowledged (result : Admission.Result before packet lifecycle prepared)
    (phase : before.phase = .data session) (afterPhase : result.state.phase = .data after) :
    (after.peer prepared.attachment.direction).acknowledged =
      max (session.peer prepared.attachment.direction).acknowledged
        (Admission.ackOffset (session.peer prepared.attachment.direction) packet.packet.segment) := by
  have allowed : Admission.Allowed (.data session) prepared.attachment packet.packet.segment before.observations :=
    phase ▸ result.admitted
  have same : Admission.Phase.data after = Admission.nextPhase (.data session) prepared.attachment packet.packet.segment allowed :=
    afterPhase.symm.trans (by simpa only [phase] using result.phase)
  cases direction : prepared.attachment.direction
  all_goals
    simp only [Admission.nextPhase] at same
    repeat' split at same
    all_goals try simp_all only [reduceCtorEq]
    all_goals
      have equal := Admission.Phase.data.inj same
      rw [equal]
      simp only [Admission.Session.peer]
      unfold Admission.acknowledgedLane
      split <;> rfl

theorem result_covering_ack (result : Admission.Result before packet lifecycle prepared)
    (phase : before.phase = .data session) (empty : packet.packet.segment.payload = [])
    (ack : packet.packet.segment.acknowledgment = (session.peer prepared.attachment.direction).base.add
      (session.peer prepared.attachment.direction).observed) :
    ∃ after, result.state.phase = .data after ∧ Shape session after ∧
      (after.peer prepared.attachment.direction).acknowledged = (after.peer prepared.attachment.direction).observed ∧
      result.state.observations = before.observations ++ [Admission.observe packet lifecycle prepared] := by
  obtain ⟨after, afterPhase, shape, ledger⟩ := result_empty_shape result phase empty
  have acknowledged := peer_acknowledged result phase afterPhase
  rw [peer_ack_offset session prepared.attachment.direction packet.packet.segment ack,
    Nat.max_eq_right (session.peer_valid prepared.attachment.direction).1] at acknowledged
  exact ⟨after, afterPhase, shape, acknowledged.trans (shape_peer_observed shape _).symm, ledger⟩

variable {source : TCP.WireForwarding.Source}

theorem Current.after_lower (current : Current start cut) (range : LowerRange start sender lower)
    (processing : CampusTCPService.Processing context (beforeService input cut.report.final .standby) source zone)
    (direction : processing.prepared.attachment.direction = sender.direction)
    (nonempty : lower ≠ []) (sequence : source.packet.segment.sequence = (current.session.lane sender.direction).base)
    (payload : source.packet.segment.payload = lower) :
    ∃ after, processing.nextAdmission.phase = .data after ∧ Shape start.seed after ∧
      processing.nextAdmission.observations =
        (beforeService input cut.report.final .standby).admission.observations ++
          [Admission.observe source.asInput
            (CampusTCPService.packetInput (beforeService input cut.report.final .standby) source zone).lifecycle
            processing.prepared] := by
  have known := current.lower_known range source.packet.segment nonempty sequence payload
  have selected : Admission.KnownRange (current.session.lane processing.prepared.attachment.direction)
      current.session.entry processing.prepared.attachment.direction source.asInput.packet.segment
      (beforeService input cut.report.final .standby).admission.observations := by
    simpa only [direction, WireForwarding.Source.asInput] using known
  obtain ⟨after, phase, shape, ledger⟩ := result_repeat_shape processing.admitted current.phase selected
  rw [CampusTCPRoundAdmission.Processing.committed_data processing current.session current.phase]
  exact ⟨after, phase, current.shape.trans shape, ledger⟩

theorem Current.after_ack (current : Current start cut)
    (processing : CampusTCPService.Processing context (beforeService input cut.report.final .standby) source zone)
    (empty : source.packet.segment.payload = [])
    (ack : source.packet.segment.acknowledgment = (current.session.peer processing.prepared.attachment.direction).base.add
      (current.session.peer processing.prepared.attachment.direction).observed) :
    ∃ after, processing.nextAdmission.phase = .data after ∧ Shape start.seed after ∧
      (after.peer processing.prepared.attachment.direction).acknowledged =
        (after.peer processing.prepared.attachment.direction).observed ∧
      processing.nextAdmission.observations =
        (beforeService input cut.report.final .standby).admission.observations ++
          [Admission.observe source.asInput
            (CampusTCPService.packetInput (beforeService input cut.report.final .standby) source zone).lifecycle
            processing.prepared] := by
  obtain ⟨after, phase, shape, acknowledged, ledger⟩ := result_covering_ack processing.admitted current.phase empty ack
  rw [CampusTCPRoundAdmission.Processing.committed_data processing current.session current.phase]
  exact ⟨after, phase, current.shape.trans shape, acknowledged, ledger⟩

end Netlib.Check.CampusTCPGapProgressGateway
