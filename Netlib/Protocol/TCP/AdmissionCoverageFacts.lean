import Netlib.Protocol.TCP.AdmissionRecoveryFacts
import Netlib.Protocol.TCP.AdmissionMSSFacts

/-!
# Original coverage sources in the admission ledger

Each run names one actual observation in the same state.
The entry, direction, position, and payload remain exact.
-/

namespace Netlib.Protocol.TCP.Admission

structure RunSource (observations : List Seen) (entry : Entry) (direction : Direction)
    (lane : Lane) (run : Coverage.Run Nat) (seen : Seen) : Prop where
  selected : observations[run.metadata]? = some seen
  entry : seen.attachment.entry = entry
  direction : seen.attachment.direction = direction
  position : run.position = Seq.distance lane.base seen.segment.sequence
  bytes : run.bytes = seen.segment.payload

def Lane.Sources (lane : Lane) (observations : List Seen) (entry : Entry) (direction : Direction) : Prop :=
  ∀ run ∈ lane.coverage.runs, ∃ seen, RunSource observations entry direction lane run seen

def State.CoverageSources (state : State) : Prop :=
  match state.phase with
  | .data session => session.original.Sources state.observations session.entry .original ∧
      session.reply.Sources state.observations session.entry .reply
  | _ => True

structure CoverageSource (observations : List Seen) (entry : Entry) (direction : Direction)
    (lane : Lane) (run : Coverage.Run Nat) where
  seen : Seen
  evidence : RunSource observations entry direction lane run seen

def Lane.coverageSource (lane : Lane) (observations : List Seen) (entry : Entry) (direction : Direction)
    (sources : lane.Sources observations entry direction) (run : Coverage.Run Nat)
    (member : run ∈ lane.coverage.runs) : CoverageSource observations entry direction lane run :=
  match selected : observations[run.metadata]? with
  | none => False.elim (by
    obtain ⟨seen, source⟩ := sources run member
    have actual := source.selected
    rw [selected] at actual
    cases actual)
  | some seen => ⟨seen, by
      obtain ⟨original, source⟩ := sources run member
      have same : original = seen := Option.some.inj (source.selected.symm.trans selected)
      subst original
      exact source⟩

theorem Lane.initial_sources (observations : List Seen) (entry : Entry) (direction : Direction)
    (base : Seq) (window : InternetChecksum.Word) (sequence acknowledgment : Seq) :
    (Lane.initial base window sequence acknowledgment).Sources observations entry direction := by
  intro run member
  cases member

theorem State.initial_coverageSources : State.initial.CoverageSources := trivial

theorem RunSource.append {observations : List Seen} {selectedEntry : Entry} {selectedDirection : Direction}
    {before : Lane} {run : Coverage.Run Nat} {seen : Seen}
    (source : RunSource observations selectedEntry selectedDirection before run seen)
    (after : Lane) (base : after.base = before.base) (next : Seen) :
    RunSource (observations ++ [next]) selectedEntry selectedDirection after run seen := by
  refine ⟨?_, source.entry, source.direction, ?_, source.bytes⟩
  · have bound := (List.getElem?_eq_some_iff.mp source.selected).1
    rw [List.getElem?_append_left bound]
    exact source.selected
  · rw [base]
    exact source.position

theorem Lane.sources_stutter (before after : Lane) (observations : List Seen) (entry : Entry)
    (direction : Direction) (seen : Seen) (sources : before.Sources observations entry direction)
    (base : after.base = before.base) (same : after.coverage = before.coverage) :
    after.Sources (observations ++ [seen]) entry direction := by
  intro run member
  have old : run ∈ before.coverage.runs := by rw [← same]; exact member
  obtain ⟨original, source⟩ := sources run old
  exact ⟨original, source.append after base seen⟩

theorem Lane.sources_change (before after : Lane) (observations : List Seen) (entry : Entry)
    (direction : Direction) (seen : Seen) (sources : before.Sources observations entry direction)
    (base : after.base = before.base) (attached : seen.attachment.entry = entry)
    (directed : seen.attachment.direction = direction)
    (change : CoverageChange before after seen.segment observations.length) :
    after.Sources (observations ++ [seen]) entry direction := by
  rcases change with same | ⟨placed, accepted, same⟩
  · exact before.sources_stutter after observations entry direction seen sources base same
  · intro run member
    have present : run ∈ placed.state.runs := by rw [← same]; exact member
    rcases Theory.SparseCoverage.accept_members _ _ _ _ _ _ accepted run present with old | rfl
    · obtain ⟨original, source⟩ := sources run old
      exact ⟨original, source.append after base seen⟩
    · refine ⟨seen, ⟨?_, attached, directed, ?_, rfl⟩⟩
      · simp only [Theory.SparseCoverage.current, List.getElem?_append_right (Nat.le_refl observations.length),
          Nat.sub_self, List.getElem?_cons_zero]
      · change Seq.distance before.base seen.segment.sequence = Seq.distance after.base seen.segment.sequence
        rw [base]

theorem Result.coverageSources (result : Result before input lifecycle prepared)
    (sources : before.CoverageSources) : result.state.CoverageSources := by
  cases phase : before.phase with
  | empty =>
    have computed : result.state.phase = nextPhase .empty prepared.attachment input.packet.segment
        (phase ▸ result.admitted) := by simpa only [phase] using result.phase
    simp only [State.CoverageSources, computed, nextPhase.eq_1]
  | syn entry iss window offer =>
    have computed : result.state.phase = nextPhase (.syn entry iss window offer) prepared.attachment input.packet.segment
        (phase ▸ result.admitted) := by simpa only [phase] using result.phase
    simp only [State.CoverageSources, computed, nextPhase.eq_2]
  | synAck entry clientISS clientWindow serverISS serverWindow clientMSS serverMSS =>
    have computed : result.state.phase = nextPhase (.synAck entry clientISS clientWindow serverISS serverWindow clientMSS serverMSS)
        prepared.attachment input.packet.segment (phase ▸ result.admitted) := by simpa only [phase] using result.phase
    simp only [State.CoverageSources, computed, nextPhase.eq_3]
    exact ⟨Lane.initial_sources _ _ _ _ _ _ _, Lane.initial_sources _ _ _ _ _ _ _⟩
  | data session =>
    obtain ⟨after, afterPhase, entry, originalBase, replyBase⟩ := result.data_fields phase
    obtain ⟨changed, changedPhase, changes⟩ := result.coverage_transition phase
    have same : changed = after := Phase.data.inj (changedPhase.symm.trans afterPhase)
    subst changed
    have old : session.original.Sources before.observations session.entry .original ∧
        session.reply.Sources before.observations session.entry .reply := by
      simpa only [State.CoverageSources, phase] using sources
    have allowed : Allowed (.data session) prepared.attachment input.packet.segment before.observations := phase ▸ result.admitted
    have attached : prepared.attachment.entry = session.entry := allowed.1
    simp only [State.CoverageSources, afterPhase, result.ledger, entry]
    rcases changes with ⟨direction, peer, change⟩ | ⟨direction, peer, change⟩
    · exact ⟨session.original.sources_change after.original before.observations session.entry .original
        (observe input lifecycle prepared) old.1 originalBase attached direction change,
        session.reply.sources_stutter after.reply before.observations session.entry .reply
          (observe input lifecycle prepared) old.2 replyBase peer⟩
    · exact ⟨session.original.sources_stutter after.original before.observations session.entry .original
        (observe input lifecycle prepared) old.1 originalBase peer,
        session.reply.sources_change after.reply before.observations session.entry .reply
          (observe input lifecycle prepared) old.2 replyBase attached direction change⟩

theorem Result.commit_coverageSources (result : Result before input lifecycle prepared)
    (sources : before.CoverageSources) (tracker : ConntrackLifecycle.State) (after : State)
    (committed : commit result tracker = .ok after) : after.CoverageSources := by
  rcases commit_cases result tracker after committed with kept | reset
  · rw [kept.1]
    exact result.coverageSources sources
  · rw [reset.1]
    exact State.initial_coverageSources

theorem State.coverage_sources_lane (state : State) (sources : state.CoverageSources)
    (session : Session) (phase : state.phase = .data session) (direction : Direction) :
    (session.lane direction).Sources state.observations session.entry direction := by
  have both : session.original.Sources state.observations session.entry .original ∧
      session.reply.Sources state.observations session.entry .reply := by
    simpa only [State.CoverageSources, phase] using sources
  cases direction with
  | original => exact both.1
  | reply => exact both.2

end Netlib.Protocol.TCP.Admission
