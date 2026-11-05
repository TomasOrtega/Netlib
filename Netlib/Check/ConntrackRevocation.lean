import Netlib.Check.ConntrackLifecycle
import Netlib.Check.StatefulExclusion
import Netlib.Protocol.Revocation

/-!
# Replay suffix exclusion

Suffixes use list positions and retain the table produced by the preceding operations.
Model exclusion uses certified late filters. Observed exclusion also requires replay agreement.
The forbidden class describes output-stage headers, not an untranslated flow identity.
-/

namespace Netlib.Check.ConntrackLifecycle.Event

open Packet Protocol Protocol.ConntrackLifecycle

def Blocks (event : Event) (forbidden : Match) : Prop :=
  match event with
  | .packet config .. => StatefulExclusion.Blocks config.late forbidden
  | .erase .. => True

def blocks (event : Event) (forbidden : Match) : Bool :=
  match event with
  | .packet config .. => StatefulExclusion.check config.late forbidden
  | .erase .. => true

theorem blocks_correct (event : Event) (forbidden : Match) : event.blocks forbidden = true ↔ event.Blocks forbidden := by
  cases event <;> simp [blocks, Blocks, StatefulExclusion.check_correct]

theorem toModel_blocks (event : Event) (forbidden : Match) (routing : Import.LinuxRoute.Snapshot) (before : State)
    (barrier : event.Blocks forbidden) : (event.toModel routing before).Blocks forbidden := by
  cases event with
  | erase => trivial
  | packet config zone header observed state =>
    intro classification output selected
    change StatefulACL.Policy.evaluate config.late.policy config.late.compile classification output = .deny
    rw [Import.NftablesStateful.Snapshot.compile_evaluate]
    exact barrier classification output selected

def observedOutput (event : Event) : Option Header := event.packetObservation.bind (·.output)

end Netlib.Check.ConntrackLifecycle.Event

namespace Netlib.Check.ConntrackRevocation

open Packet ConntrackLifecycle

def blocksFrom (observations : List Observation) (start : Nat) (forbidden : Match) : Bool :=
  (observations.drop start).all (fun observation => observation.event.blocks forbidden)

theorem blocksFrom_correct (observations : List Observation) (start : Nat) (forbidden : Match) :
    blocksFrom observations start forbidden = true ↔
      ∀ observation ∈ observations.drop start, observation.event.Blocks forbidden := by
  simp only [blocksFrom, List.all_eq_true, Event.blocks_correct]

end Netlib.Check.ConntrackRevocation

namespace Netlib.Check.ConntrackLifecycle

open Packet Protocol Protocol.ConntrackLifecycle

theorem ReplayTrace.drop {routing : Import.LinuxRoute.Snapshot} {initial final : State} {findings : List Finding}
    (trace : ReplayTrace routing initial findings final) (start : Nat) :
    ∃ middle, ReplayTrace routing middle (findings.drop start) final := by
  induction trace generalizing start with
  | nil => simp only [List.drop_nil]; exact ⟨_, .nil _⟩
  | cons accepted rest ih =>
    cases start with
    | zero => exact ⟨_, .cons accepted rest⟩
    | succ start => exact ih start

theorem ReplayTrace.excludes {routing : Import.LinuxRoute.Snapshot} {initial final : State} {findings : List Finding}
    (trace : ReplayTrace routing initial findings final) (forbidden : Match)
    (barriers : ∀ finding ∈ findings, finding.observation.event.Blocks forbidden) :
    ∀ finding ∈ findings, finding.result.Excludes forbidden := by
  induction trace with
  | nil => simp
  | @cons before final head tail accepted rest ih =>
    intro actual member
    rcases List.mem_cons.mp member with rfl | member
    · exact Operations.step_excludes before _ actual.result forbidden
        (actual.observation.event.toModel_blocks forbidden routing before (barriers _ (by simp))) accepted
    · exact ih (fun next belongs => barriers next (List.mem_cons_of_mem _ belongs)) actual member

theorem ReplayTrace.suffix_excludes {routing : Import.LinuxRoute.Snapshot} {initial final : State} {findings : List Finding}
    (trace : ReplayTrace routing initial findings final) (start : Nat) (forbidden : Match)
    (barriers : ∀ finding ∈ findings.drop start, finding.observation.event.Blocks forbidden) :
    ∀ finding ∈ findings.drop start, finding.result.Excludes forbidden := by
  obtain ⟨_, suffix⟩ := trace.drop start
  exact suffix.excludes forbidden barriers

theorem ReplayTrace.matches {routing : Import.LinuxRoute.Snapshot} {initial final : State} {findings : List Finding}
    (trace : ReplayTrace routing initial findings final)
    (agreement : Agreement routing initial (findings.map Finding.observation)) :
    ∀ finding ∈ findings, Matches finding.observation finding.result := by
  induction trace with
  | nil => simp
  | @cons before final head tail accepted rest ih =>
    obtain ⟨actual, actualStep, matched, remaining⟩ := agreement
    have same : actual = head.result := by
      rw [accepted] at actualStep
      exact (Except.ok.inj actualStep).symm
    subst actual
    intro finding member
    rcases List.mem_cons.mp member with rfl | member
    · exact matched
    · exact ih remaining finding member

theorem Matches.output_excluded (observation : Observation) (result : Operations.Result) (forbidden : Match)
    (matched : Matches observation result) (excluded : result.Excludes forbidden) :
    OutputExcluded forbidden observation.event.observedOutput := by
  unfold Event.observedOutput
  rw [matched.1]
  cases packet : result.packet with
  | none => simp [OutputExcluded]
  | some outcome => simpa [PacketObservation.expected] using excluded outcome packet

namespace Report

theorem drop_covered (report : Report routing initial observations) (start : Nat) :
    (report.findings.drop start).map Finding.observation = observations.drop start := by
  rw [List.map_drop, report.covered]

theorem model_outputs_excluded (report : Report routing initial observations) (start : Nat) (forbidden : Match)
    (barriers : ConntrackRevocation.blocksFrom observations start forbidden = true) :
    ∀ finding ∈ report.findings.drop start, finding.result.Excludes forbidden := by
  apply report.trace.suffix_excludes start forbidden
  intro finding member
  have observed : finding.observation ∈ observations.drop start := by
    rw [← report.drop_covered start]
    exact List.mem_map.mpr ⟨finding, member, rfl⟩
  exact (ConntrackRevocation.blocksFrom_correct observations start forbidden).mp barriers _ observed

theorem observed_outputs_excluded (report : Report routing initial observations) (start : Nat) (forbidden : Match)
    (barriers : ConntrackRevocation.blocksFrom observations start forbidden = true)
    (compliant : report.compliant = true) :
    ∀ observation ∈ observations.drop start, OutputExcluded forbidden observation.event.observedOutput := by
  have agreement := report.compliant_iff.mp compliant
  rw [← report.covered] at agreement
  have matchedFindings := report.trace.matches agreement
  intro observation member
  rw [← report.drop_covered start] at member
  obtain ⟨finding, belongs, rfl⟩ := List.mem_map.mp member
  apply Matches.output_excluded finding.observation finding.result forbidden
  · exact matchedFindings finding (List.mem_of_mem_drop belongs)
  · exact report.model_outputs_excluded start forbidden barriers finding belongs

end Report
end Netlib.Check.ConntrackLifecycle
