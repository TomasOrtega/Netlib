import Netlib.Protocol.TCP.AdmissionExecution
import Netlib.Protocol.TCP.AdmissionStartupRecoveryCoverage

/-!
# Coverage sources for both admission modes

Legacy transitions retain their existing source proof.
Recovery controls append their actual observation without replacing earlier sources.
-/

namespace Netlib.Protocol.TCP.AdmissionExecution

open Admission

theorem Result.coverageSources (value : Result mode before input lifecycle prepared)
    (sources : before.CoverageSources) : (Result.state value).CoverageSources := by
  cases mode with
  | ordinary => exact Admission.Result.coverageSources value sources
  | startupRecovery => exact AdmissionStartupRecovery.Result.coverageSources value sources

theorem Result.commit_coverageSources (value : Result mode before input lifecycle prepared)
    (sources : before.CoverageSources) (tracker : ConntrackLifecycle.State) (after : State)
    (committed : commit value tracker = .ok after) : after.CoverageSources := by
  rcases commit_cases value tracker after committed with kept | reset
  · rw [kept.1]
    exact Result.coverageSources value sources
  · rw [reset.1]
    exact State.initial_coverageSources

end Netlib.Protocol.TCP.AdmissionExecution
