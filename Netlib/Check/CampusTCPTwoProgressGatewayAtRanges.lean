import Netlib.Check.CampusTCPTwoProgressGatewayAtReady

/-!
# Retained ranges at the current gateway location

Actual admission keeps the original range coordinates and source IDs.
New range metadata names the same current observation ledger.
-/

namespace Netlib.Check.CampusTCPTwoProgressGatewayAt

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressCoverage
open CampusTCPTwoProgressGatewayState (reindex sender_lane peer_coverage)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current next : Cut input complete} {sender : Actor} {gateway location : Gateway}
variable {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}

theorem ViewAt.highEnd (view : ViewAt initial current location) :
    (view.gateway.session.lane sender.direction).highEnd =
      if view.ranges.upperRun.isSome then initial.geometry.«prefix» + lower.length + upper.length
      else if view.ranges.lowerRun.isSome then initial.geometry.«prefix» + lower.length else initial.geometry.«prefix» :=
  view.ranges.highEnd initial.geometry.highEnd

theorem ViewAt.observed (view : ViewAt initial current location) :
    (view.gateway.session.lane sender.direction).observed =
      if view.ranges.lowerRun.isSome then initial.geometry.«prefix» + lower.length +
        (if view.ranges.upperRun.isSome then upper.length else 0) else initial.geometry.«prefix» := by
  apply view.ranges.frontier Admission.coverageBound
  · cases sender
    · exact initial.gatewayState.session.originalValid.2.2.2
    · exact initial.gatewayState.session.replyValid.2.2.2
  · exact initial.geometry.observed
  · exact initial.geometry.highEnd
  · exact initial.lowerNonempty

variable {source : WireForwarding.Source}

theorem ViewAt.after_coverage (view : ViewAt initial current location)
    (retained : cut.report.steps <+: current.report.steps)
    (processing : CampusTCPService.Processing context (beforeService input current.report.final location) source zone)
    (direction : processing.prepared.attachment.direction = sender.direction)
    (after : Admission.Session) (phase : processing.admitted.state.phase = .data after)
    (ranges : TwoRanges (initial.gatewayState.session.lane sender.direction).coverage
      (after.lane sender.direction).coverage initial.geometry.«prefix» lower upper)
    (admission : (beforeService input next.report.final location).admission = processing.nextAdmission)
    (tracker : (beforeService input next.report.final location).tracker = processing.outcome.state) :
    ∃ result : ViewAt initial next location, result.gateway.session = after ∧
      result.ranges.lowerRun = ranges.lowerRun ∧ result.ranges.upperRun = ranges.upperRun := by
  obtain ⟨gatewayState⟩ := view.gateway.after_processing retained processing admission tracker
  have selected : gatewayState.session = after := by
    apply Admission.Phase.data.inj
    exact gatewayState.phase.symm.trans (by
      rw [admission, CampusTCPRoundAdmission.Processing.committed_data processing view.gateway.session view.gateway.phase]
      exact phase)
  have peer := peer_coverage processing.admitted view.gateway.phase phase
  rw [direction] at peer
  let newRanges := reindex ranges (congrArg (fun session => (session.lane sender.direction).coverage) selected.symm)
  let result : ViewAt initial next location := {
    gateway := gatewayState
    ranges := newRanges
    peerCoverage := by rw [selected, peer]; exact view.peerCoverage
  }
  refine ⟨result, selected, ?_, ?_⟩
  all_goals rfl

theorem ViewAt.lower_service (view : ViewAt initial current location)
    (retained : cut.report.steps <+: current.report.steps)
    (processing : CampusTCPService.Processing context (beforeService input current.report.final location) source zone)
    (direction : processing.prepared.attachment.direction = sender.direction)
    (ready : Admission.FreshReady view.gateway.session processing.prepared.attachment.direction source.packet.segment)
    (missing : view.ranges.lowerRun = none)
    (position : Seq.distance (view.gateway.session.lane sender.direction).base source.packet.segment.sequence = initial.geometry.«prefix»)
    (payload : source.packet.segment.payload = lower)
    (admission : (beforeService input next.report.final location).admission = processing.nextAdmission)
    (tracker : (beforeService input next.report.final location).tracker = processing.outcome.state) :
    ∃ result : ViewAt initial next location, result.ranges.upperRun = view.ranges.upperRun ∧
      ∃ run, result.ranges.lowerRun = some run ∧
        run.sourceID = (view.gateway.session.lane sender.direction).coverage.nextID ∧
        run.metadata = (beforeService input current.report.final location).admission.observations.length ∧
        run.position = initial.geometry.«prefix» ∧ run.bytes = lower := by
  let ranges := reindex view.ranges (show (view.gateway.session.lane sender.direction).coverage =
      (view.gateway.session.sender processing.prepared.attachment.direction).coverage by rw [direction, sender_lane])
  have inside : initial.geometry.«prefix» + lower.length ≤ Admission.coverageBound := by
    have epoch := initial.geometry.epoch
    unfold Admission.coverageBound Seq.halfSpace at *
    omega
  have positionAt : Seq.distance (view.gateway.session.sender processing.prepared.attachment.direction).base
      source.packet.segment.sequence = initial.geometry.«prefix» := by simpa only [direction, sender_lane] using position
  obtain ⟨after, phase, newRanges, upperRun, run, lowerRun, id, metadata, positionField, bytes⟩ :=
    CampusTCPTwoProgressGatewayCoverage.lower_admission processing.admitted view.gateway.session view.gateway.phase ready
      _ _ lower upper ranges initial.geometry.highEnd missing initial.lowerNonempty inside positionAt payload
  let selectedRanges := reindex newRanges (show (after.sender processing.prepared.attachment.direction).coverage =
      (after.lane sender.direction).coverage by rw [direction, sender_lane])
  obtain ⟨result, _, first, second⟩ := view.after_coverage retained processing direction after phase selectedRanges admission tracker
  refine ⟨result, second.trans upperRun, run, first.trans lowerRun, ?_, metadata, positionField, bytes⟩
  simpa only [direction, sender_lane] using id

theorem ViewAt.upper_service (view : ViewAt initial current location)
    (retained : cut.report.steps <+: current.report.steps)
    (processing : CampusTCPService.Processing context (beforeService input current.report.final location) source zone)
    (direction : processing.prepared.attachment.direction = sender.direction)
    (ready : Admission.FreshReady view.gateway.session processing.prepared.attachment.direction source.packet.segment)
    (missing : view.ranges.upperRun = none)
    (position : Seq.distance (view.gateway.session.lane sender.direction).base source.packet.segment.sequence =
      initial.geometry.«prefix» + lower.length)
    (payload : source.packet.segment.payload = upper)
    (admission : (beforeService input next.report.final location).admission = processing.nextAdmission)
    (tracker : (beforeService input next.report.final location).tracker = processing.outcome.state) :
    ∃ result : ViewAt initial next location, result.ranges.lowerRun = view.ranges.lowerRun ∧
      ∃ run, result.ranges.upperRun = some run ∧
        run.sourceID = (view.gateway.session.lane sender.direction).coverage.nextID ∧
        run.metadata = (beforeService input current.report.final location).admission.observations.length ∧
        run.position = initial.geometry.«prefix» + lower.length ∧ run.bytes = upper := by
  let ranges := reindex view.ranges (show (view.gateway.session.lane sender.direction).coverage =
      (view.gateway.session.sender processing.prepared.attachment.direction).coverage by rw [direction, sender_lane])
  have inside : initial.geometry.«prefix» + lower.length + upper.length ≤ Admission.coverageBound := by
    have epoch := initial.geometry.epoch
    unfold Admission.coverageBound Seq.halfSpace at *
    omega
  have positionAt : Seq.distance (view.gateway.session.sender processing.prepared.attachment.direction).base
      source.packet.segment.sequence = initial.geometry.«prefix» + lower.length := by simpa only [direction, sender_lane] using position
  obtain ⟨after, phase, newRanges, lowerRun, run, upperRun, id, metadata, positionField, bytes⟩ :=
    CampusTCPTwoProgressGatewayCoverage.upper_admission processing.admitted view.gateway.session view.gateway.phase ready
      _ _ lower upper ranges initial.geometry.highEnd missing initial.upperNonempty inside positionAt payload
  let selectedRanges := reindex newRanges (show (after.sender processing.prepared.attachment.direction).coverage =
      (after.lane sender.direction).coverage by rw [direction, sender_lane])
  obtain ⟨result, _, first, second⟩ := view.after_coverage retained processing direction after phase selectedRanges admission tracker
  refine ⟨result, first.trans lowerRun, run, second.trans upperRun, ?_, metadata, positionField, bytes⟩
  simpa only [direction, sender_lane] using id

theorem ViewAt.after_shape (view : ViewAt initial current location)
    (retained : cut.report.steps <+: current.report.steps)
    (processing : CampusTCPService.Processing context (beforeService input current.report.final location) source zone)
    (after : Admission.Session) (phase : processing.admitted.state.phase = .data after)
    (shape : CampusTCPGapProgressStart.Shape view.gateway.session after)
    (admission : (beforeService input next.report.final location).admission = processing.nextAdmission)
    (tracker : (beforeService input next.report.final location).tracker = processing.outcome.state) :
    ∃ result : ViewAt initial next location, result.ranges.lowerRun = view.ranges.lowerRun ∧
      result.ranges.upperRun = view.ranges.upperRun := by
  obtain ⟨gatewayState⟩ := view.gateway.after_processing retained processing admission tracker
  have selected : gatewayState.session = after := by
    apply Admission.Phase.data.inj
    exact gatewayState.phase.symm.trans (by
      rw [admission, CampusTCPRoundAdmission.Processing.committed_data processing view.gateway.session view.gateway.phase]
      exact phase)
  have same : (view.gateway.session.lane sender.direction).coverage =
      (gatewayState.session.lane sender.direction).coverage := by rw [selected, shape.coverage]
  let result : ViewAt initial next location := {
    gateway := gatewayState
    ranges := reindex view.ranges same
    peerCoverage := by
      rw [selected]
      cases sender
      · exact (shape.coverage .reply).trans view.peerCoverage
      · exact (shape.coverage .original).trans view.peerCoverage
  }
  exact ⟨result, rfl, rfl⟩

theorem ViewAt.empty_service (view : ViewAt initial current location)
    (retained : cut.report.steps <+: current.report.steps)
    (processing : CampusTCPService.Processing context (beforeService input current.report.final location) source zone)
    (empty : source.packet.segment.payload = [])
    (admission : (beforeService input next.report.final location).admission = processing.nextAdmission)
    (tracker : (beforeService input next.report.final location).tracker = processing.outcome.state) :
    ∃ result : ViewAt initial next location, result.ranges.lowerRun = view.ranges.lowerRun ∧
      result.ranges.upperRun = view.ranges.upperRun := by
  obtain ⟨after, phase, shape, _⟩ := CampusTCPGapProgressGateway.result_empty_shape processing.admitted view.gateway.phase empty
  exact view.after_shape retained processing after phase shape admission tracker

theorem ViewAt.repeat_service (view : ViewAt initial current location)
    (retained : cut.report.steps <+: current.report.steps)
    (processing : CampusTCPService.Processing context (beforeService input current.report.final location) source zone)
    (known : Admission.KnownRange (view.gateway.session.lane processing.prepared.attachment.direction)
      view.gateway.session.entry processing.prepared.attachment.direction source.packet.segment
      (beforeService input current.report.final location).admission.observations)
    (admission : (beforeService input next.report.final location).admission = processing.nextAdmission)
    (tracker : (beforeService input next.report.final location).tracker = processing.outcome.state) :
    ∃ result : ViewAt initial next location, result.ranges.lowerRun = view.ranges.lowerRun ∧
      result.ranges.upperRun = view.ranges.upperRun := by
  obtain ⟨after, phase, shape, _⟩ := CampusTCPGapProgressGateway.result_repeat_shape processing.admitted view.gateway.phase known
  exact view.after_shape retained processing after phase shape admission tracker

theorem ViewAt.lower_known (view : ViewAt initial current location)
    (retained : cut.report.steps <+: current.report.steps) (run : Admission.Coverage.Run Nat)
    (available : view.ranges.lowerRun = some run) (segment : Segment)
    (position : Seq.distance (view.gateway.session.lane sender.direction).base segment.sequence = initial.geometry.«prefix»)
    (payload : segment.payload = lower) :
    Admission.KnownRange (view.gateway.session.lane sender.direction) view.gateway.session.entry sender.direction segment
      (beforeService input current.report.final location).admission.observations := by
  have fields := view.ranges.lowerFields run (by simp [available])
  apply view.gateway.known_of_slice retained sender.direction segment run
    (by rw [view.ranges.runs, available]; simp) (by simpa only [payload] using initial.lowerNonempty) 0
  simp only [Theory.SparseCoverage.Slice, fields.1, fields.2, position, payload, Nat.add_zero,
    Nat.zero_add, Nat.le_refl, List.drop_zero, List.take_length, and_self]

theorem ViewAt.upper_known (view : ViewAt initial current location)
    (retained : cut.report.steps <+: current.report.steps) (run : Admission.Coverage.Run Nat)
    (available : view.ranges.upperRun = some run) (segment : Segment)
    (position : Seq.distance (view.gateway.session.lane sender.direction).base segment.sequence =
      initial.geometry.«prefix» + lower.length)
    (payload : segment.payload = upper) :
    Admission.KnownRange (view.gateway.session.lane sender.direction) view.gateway.session.entry sender.direction segment
      (beforeService input current.report.final location).admission.observations := by
  have fields := view.ranges.upperFields run (by simp [available])
  apply view.gateway.known_of_slice retained sender.direction segment run
    (by rw [view.ranges.runs, available]; simp) (by simpa only [payload] using initial.upperNonempty) 0
  simp only [Theory.SparseCoverage.Slice, fields.1, fields.2, position, payload, Nat.add_zero,
    Nat.zero_add, Nat.le_refl, List.drop_zero, List.take_length, and_self]

end Netlib.Check.CampusTCPTwoProgressGatewayAt
