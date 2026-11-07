import Netlib.Protocol.TCP.AdmissionStartupRecovery
import Netlib.Protocol.TCP.AdmissionCoverageFacts

/-!
# Coverage sources through startup recovery admission

A repeated control preserves coverage and appends its actual observation.
Existing runs retain their original observation indices and payloads.
-/

namespace Netlib.Protocol.TCP.AdmissionStartupRecovery

open Admission

theorem Result.stutter_coverageSources (result : Result before input lifecycle prepared)
    (stutter : StutterAllowed before.phase prepared.attachment input.packet.segment before.observations)
    (sources : before.CoverageSources) : result.state.CoverageSources := by
  have unchanged := result.stutter stutter
  cases phase : before.phase with
  | empty => simp only [State.CoverageSources, unchanged, phase]
  | syn entry iss window offer => simp only [State.CoverageSources, unchanged, phase]
  | synAck entry clientISS clientWindow serverISS serverWindow clientMSS serverMSS =>
    simp only [State.CoverageSources, unchanged, phase]
  | data session =>
    have old : session.original.Sources before.observations session.entry .original ∧
        session.reply.Sources before.observations session.entry .reply := by
      simpa only [State.CoverageSources, phase] using sources
    simp only [State.CoverageSources, unchanged, phase, result.ledger]
    exact ⟨session.original.sources_stutter session.original before.observations session.entry .original
        (observe input lifecycle prepared) old.1 rfl rfl,
      session.reply.sources_stutter session.reply before.observations session.entry .reply
        (observe input lifecycle prepared) old.2 rfl rfl⟩

theorem Result.coverageSources (result : Result before input lifecycle prepared)
    (sources : before.CoverageSources) : result.state.CoverageSources := by
  by_cases legacy : Admission.Allowed before.phase prepared.attachment input.packet.segment before.observations
  · exact (result.asLegacy legacy).coverageSources sources
  · exact result.stutter_coverageSources (result.admitted.resolve_left legacy) sources

theorem Result.commit_coverageSources (result : Result before input lifecycle prepared)
    (sources : before.CoverageSources) (tracker : ConntrackLifecycle.State) (after : State)
    (committed : commit result tracker = .ok after) : after.CoverageSources := by
  rcases commit_cases result tracker after committed with kept | reset
  · rw [kept.1]
    exact result.coverageSources sources
  · rw [reset.1]
    exact State.initial_coverageSources

end Netlib.Protocol.TCP.AdmissionStartupRecovery
