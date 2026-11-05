import Netlib.Check.BufferedReplay

/-!
# Buffered cutover certificates

Boundaries are schedule positions. The flushing batch precedes the clean-service suffix.
Readiness uses actual prefix state and computed FIFO admissions, independently of observations.
Observed service exclusion additionally requires complete replay agreement.
-/

namespace Netlib.Check.BufferedReplay

open Packet

def Event.Blocks (event : Event) (forbidden : Match) : Prop :=
  match event with
  | .operation source => source.event.Blocks forbidden
  | .serve .. => True

def Event.blocks (event : Event) (forbidden : Match) : Bool :=
  match event with
  | .operation source => source.event.blocks forbidden
  | .serve .. => true

theorem Event.blocks_correct (event : Event) (forbidden : Match) :
    event.blocks forbidden = true ↔ event.Blocks forbidden := by
  cases event <;> simp [blocks, Blocks, ConntrackLifecycle.Event.blocks_correct]

theorem Event.toModel_blocks (event : Event) (routing : Import.LinuxRoute.Snapshot) (before : BufferedState)
    (forbidden : Match) (barrier : event.Blocks forbidden) : (event.toModel routing before).Blocks forbidden := by
  cases event with
  | operation source => exact source.event.toModel_blocks forbidden routing before.tracker barrier
  | serve => trivial

@[simp] theorem Event.toModel_capacity (event : Event) (routing : Import.LinuxRoute.Snapshot) (before : BufferedState) :
    (event.toModel routing before).capacity = event.capacity := by cases event <;> rfl

def Event.observedServed : Event → List Header
  | .operation _ => []
  | .serve _ observed => observed

def stateAt (findings : List Finding) (final : BufferedState) (position : Nat) : BufferedState :=
  (((findings.drop position).head?).map Finding.before).getD final

theorem stateAt_drop (findings : List Finding) (final : BufferedState) (start count : Nat) :
    stateAt (findings.drop start) final count = stateAt findings final (start + count) := by
  simp only [stateAt, List.drop_drop]

theorem ReplayTrace.toModel {routing : Import.LinuxRoute.Snapshot} {initial final : BufferedState} {findings : List Finding}
    (trace : ReplayTrace routing initial findings final) :
    Protocol.BufferedLifecycle.Trace initial (findings.map Finding.modelEvent) (findings.map Finding.result) final := by
  induction trace with
  | nil => exact .nil _
  | cons _ accepted _ ih => exact .cons accepted ih

theorem ReplayTrace.split {routing : Import.LinuxRoute.Snapshot} {initial final : BufferedState} {findings : List Finding}
    (trace : ReplayTrace routing initial findings final) (position : Nat) :
    ReplayTrace routing initial (findings.take position) (stateAt findings final position) ∧
      ReplayTrace routing (stateAt findings final position) (findings.drop position) final := by
  induction trace generalizing position with
  | nil => simp only [stateAt, List.drop_nil, List.take_nil]; exact ⟨.nil _, .nil _⟩
  | cons linked accepted rest ih =>
    cases position with
    | zero => exact ⟨.nil _, .cons linked accepted rest⟩
    | succ position =>
      obtain ⟨head, tail⟩ := ih position
      exact ⟨.cons linked accepted head, tail⟩

theorem ReplayTrace.linked {routing : Import.LinuxRoute.Snapshot} {initial final : BufferedState} {findings : List Finding}
    (trace : ReplayTrace routing initial findings final) :
    ∀ finding ∈ findings, finding.modelEvent = finding.observation.event.toModel routing finding.before := by
  induction trace with
  | nil => simp
  | cons linked _ _ ih =>
    intro finding member
    rcases List.mem_cons.mp member with rfl | member
    · exact linked
    · exact ih finding member

theorem ReplayTrace.barriers {routing : Import.LinuxRoute.Snapshot} {initial final : BufferedState} {findings : List Finding}
    (trace : ReplayTrace routing initial findings final) (forbidden : Match)
    (barriers : ∀ finding ∈ findings, finding.observation.event.Blocks forbidden) :
    ∀ event ∈ findings.map Finding.modelEvent, event.Blocks forbidden := by
  intro event member
  obtain ⟨finding, belongs, rfl⟩ := List.mem_map.mp member
  rw [trace.linked finding belongs]
  exact finding.observation.event.toModel_blocks routing finding.before forbidden (barriers finding belongs)

theorem ReplayTrace.capacities {routing : Import.LinuxRoute.Snapshot} {initial final : BufferedState} {findings : List Finding}
    (trace : ReplayTrace routing initial findings final) :
    findings.map (fun finding => finding.modelEvent.capacity) =
      findings.map (fun finding => finding.observation.event.capacity) := by
  induction trace with
  | nil => rfl
  | cons linked _ _ ih => simp [List.map_cons, linked, ih]

theorem ReplayTrace.matches {routing : Import.LinuxRoute.Snapshot} {initial final : BufferedState} {findings : List Finding}
    (trace : ReplayTrace routing initial findings final)
    (agreement : Agreement routing initial (findings.map Finding.observation)) :
    ∀ finding ∈ findings, Matches finding.observation finding.result := by
  induction trace with
  | nil => simp
  | @cons final head tail linked accepted rest ih =>
    obtain ⟨actual, actualStep, matched, remaining⟩ := agreement
    have same : actual = head.result := by
      rw [← linked, accepted] at actualStep
      exact (Except.ok.inj actualStep).symm
    subst actual
    intro finding member
    rcases List.mem_cons.mp member with rfl | member
    · exact matched
    · exact ih remaining finding member

theorem Matches.served_eq (observation : Observation) (result : BufferedResult) (matched : Matches observation result) :
    result.served = observation.event.observedServed := by
  cases event : observation.event with
  | operation source =>
    simp only [Matches, Event.Matches, event] at matched
    obtain ⟨_, _, _, served⟩ := matched.1
    simpa only [event, Event.observedServed] using served
  | serve capacity observed =>
    simp only [Matches, Event.Matches, event] at matched
    exact matched.1.2

namespace Report

def stateAt (report : Report routing initial observations) (position : Nat) : BufferedState :=
  BufferedReplay.stateAt report.findings report.final position

def capacityBetween (_report : Report routing initial observations) (start drainedAt : Nat) : Nat :=
  (((observations.drop start).take (drainedAt - start)).map (·.event.capacity)).sum

theorem drop_covered (report : Report routing initial observations) (position : Nat) :
    (report.findings.drop position).map Finding.observation = observations.drop position := by
  rw [List.map_drop, report.covered]

theorem capacityBetween_correct (report : Report routing initial observations) (start drainedAt : Nat) :
    Protocol.BufferedLifecycle.serviceCapacity
      (((report.findings.drop start).take (drainedAt - start)).map Finding.modelEvent) =
      report.capacityBetween start drainedAt := by
  have interval := ((report.trace.split start).2.split (drainedAt - start)).1
  unfold Protocol.BufferedLifecycle.serviceCapacity capacityBetween
  simp only [List.map_map, Function.comp_def]
  rw [interval.capacities]
  have sourceCapacity : report.findings.map (fun finding => finding.observation.event.capacity) =
      observations.map (fun observation => observation.event.capacity) := by
    simpa only [List.map_map, Function.comp_def] using
      congrArg (List.map (fun observation => observation.event.capacity)) report.covered
  simpa only [List.map_take, List.map_drop] using
    congrArg (fun capacities => ((capacities.drop start).take (drainedAt - start)).sum) sourceCapacity

theorem stateAt_valid (report : Report routing initial observations) (position : Nat) (valid : initial.Valid) :
    (report.stateAt position).Valid := (report.trace.split position).1.toModel.valid valid |>.1

end Report
end Netlib.Check.BufferedReplay

namespace Netlib.Check.BufferedDrain

open Packet BufferedReplay

def blocksFrom (observations : List Observation) (start : Nat) (forbidden : Match) : Bool :=
  (observations.drop start).all (fun observation => observation.event.blocks forbidden)

theorem blocksFrom_correct (observations : List Observation) (start : Nat) (forbidden : Match) :
    blocksFrom observations start forbidden = true ↔
      ∀ observation ∈ observations.drop start, observation.event.Blocks forbidden := by
  simp only [blocksFrom, List.all_eq_true, Event.blocks_correct]

end Netlib.Check.BufferedDrain

namespace Netlib.Check.BufferedReplay.Report

open Packet

def Ready (report : Report routing initial observations) (start drainedAt : Nat) (forbidden : Match) : Prop :=
  start ≤ drainedAt ∧ drainedAt ≤ observations.length ∧
    (report.stateAt start).queue.pending.length ≤ report.capacityBetween start drainedAt ∧
    ∀ observation ∈ observations.drop start, observation.event.Blocks forbidden

def ready (report : Report routing initial observations) (start drainedAt : Nat) (forbidden : Match) : Bool :=
  decide (start ≤ drainedAt) && decide (drainedAt ≤ observations.length) &&
    decide ((report.stateAt start).queue.pending.length ≤ report.capacityBetween start drainedAt) &&
    BufferedDrain.blocksFrom observations start forbidden

theorem ready_correct (report : Report routing initial observations) (start drainedAt : Nat) (forbidden : Match) :
    report.ready start drainedAt forbidden = true ↔ report.Ready start drainedAt forbidden := by
  simp only [ready, Bool.and_eq_true, decide_eq_true_eq, BufferedDrain.blocksFrom_correct, Ready, and_assoc]

theorem interval_trace (report : Report routing initial observations) (start drainedAt : Nat)
    (ordered : start ≤ drainedAt) :
    ReplayTrace routing (report.stateAt start) ((report.findings.drop start).take (drainedAt - start))
      (report.stateAt drainedAt) := by
  have interval := ((report.trace.split start).2.split (drainedAt - start)).1
  rw [BufferedReplay.stateAt_drop, Nat.add_sub_of_le ordered] at interval
  exact interval

theorem barriers_from (report : Report routing initial observations) (start : Nat) (forbidden : Match)
    (barriers : ∀ observation ∈ observations.drop start, observation.event.Blocks forbidden) :
    ∀ finding ∈ report.findings.drop start, finding.observation.event.Blocks forbidden := by
  intro finding member
  apply barriers finding.observation
  rw [← report.drop_covered start]
  exact List.mem_map.mpr ⟨finding, member, rfl⟩

theorem pending_clean_of_ready (report : Report routing initial observations) (start drainedAt : Nat) (forbidden : Match)
    (accepted : report.ready start drainedAt forbidden = true) :
    Theory.QueueDrain.CleanPending (fun header => ¬forbidden.Holds header) (report.stateAt drainedAt).queue := by
  obtain ⟨ordered, _, enough, barriers⟩ := (report.ready_correct start drainedAt forbidden).mp accepted
  have interval := report.interval_trace start drainedAt ordered
  apply interval.toModel.pending_clean_after_budget forbidden
  · apply interval.barriers forbidden
    intro finding member
    exact report.barriers_from start forbidden barriers finding (List.mem_of_mem_take member)
  · rw [report.capacityBetween_correct]
    exact enough

theorem model_served_excluded (report : Report routing initial observations) (start drainedAt : Nat) (forbidden : Match)
    (accepted : report.ready start drainedAt forbidden = true) :
    ∀ finding ∈ report.findings.drop drainedAt, ∀ header ∈ finding.result.served, ¬forbidden.Holds header := by
  obtain ⟨ordered, _, _, barriers⟩ := (report.ready_correct start drainedAt forbidden).mp accepted
  have suffix := (report.trace.split drainedAt).2
  have excluded := suffix.toModel.served_excluded forbidden (report.pending_clean_of_ready start drainedAt forbidden accepted)
    (suffix.barriers forbidden (fun finding member => report.barriers_from start forbidden barriers finding
      (by
        have split : report.findings.drop drainedAt =
            (report.findings.drop start).drop (drainedAt - start) := by
          rw [List.drop_drop, Nat.add_sub_of_le ordered]
        rw [split] at member
        exact List.mem_of_mem_drop member)))
  intro finding member header served
  exact excluded finding.result (List.mem_map.mpr ⟨finding, member, rfl⟩) header served

theorem observed_served_excluded (report : Report routing initial observations) (start drainedAt : Nat) (forbidden : Match)
    (accepted : report.ready start drainedAt forbidden = true) (compliant : report.compliant = true) :
    ∀ observation ∈ observations.drop drainedAt, ∀ header ∈ observation.event.observedServed, ¬forbidden.Holds header := by
  have agreement := report.compliant_iff.mp compliant
  rw [← report.covered] at agreement
  have matchedFindings := report.trace.matches agreement
  intro observation member header served
  rw [← report.drop_covered drainedAt] at member
  obtain ⟨finding, belongs, rfl⟩ := List.mem_map.mp member
  have matched := matchedFindings finding (List.mem_of_mem_drop belongs)
  rw [← matched.served_eq] at served
  exact report.model_served_excluded start drainedAt forbidden accepted finding belongs header served

theorem continuation_served_excluded (report : Report routing initial observations) (start drainedAt : Nat) (forbidden : Match)
    (accepted : report.ready start drainedAt forbidden = true)
    {events : List Protocol.BufferedLifecycle.Event} {results : List BufferedResult} {finalState : BufferedState}
    (future : Protocol.BufferedLifecycle.Trace (report.stateAt drainedAt) events results finalState)
    (barriers : ∀ event ∈ events, event.Blocks forbidden) :
    ∀ result ∈ results, ∀ header ∈ result.served, ¬forbidden.Holds header :=
  future.served_excluded forbidden (report.pending_clean_of_ready start drainedAt forbidden accepted) barriers

end Netlib.Check.BufferedReplay.Report
