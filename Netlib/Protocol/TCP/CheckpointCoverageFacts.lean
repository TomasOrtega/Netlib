import Netlib.Protocol.TCP.AdmissionCoverageFacts
import Netlib.Protocol.TCP.CheckpointObservationHistory

/-!
# Actual operations that supply sparse coverage

The source lookup uses the retained observation index.
Each byte keeps its original operation and earlier history cut.
-/

namespace Netlib.Protocol.TCP.Checkpoint

theorem History.coverage_sources (history : History gateway) : gateway.admission.CoverageSources := by
  induction history with
  | initial => exact Admission.State.initial_coverageSources
  | advance prior transition ih =>
    exact transition.admitted.commit_coverageSources ih transition.outcome.state transition.nextAdmission transition.committed

structure CoverageOrigin (history : History gateway) (session : Admission.Session)
    (direction : Admission.Direction) (run : Admission.Coverage.Run Nat) where
  phase : gateway.admission.phase = .data session
  member : run ∈ (session.lane direction).coverage.runs
  source : Admission.CoverageSource gateway.admission.observations session.entry direction (session.lane direction) run
  observation : ObservationOrigin history run.metadata source.seen

def History.coverageOrigin (history : History gateway) (session : Admission.Session)
    (phase : gateway.admission.phase = .data session) (direction : Admission.Direction)
    (run : Admission.Coverage.Run Nat) (member : run ∈ (session.lane direction).coverage.runs) :
    CoverageOrigin history session direction run :=
  let sources := gateway.admission.coverage_sources_lane history.coverage_sources session phase direction
  let source := (session.lane direction).coverageSource gateway.admission.observations session.entry direction sources run member
  ⟨phase, member, source, history.observationOrigin run.metadata source.seen source.evidence.selected⟩

theorem History.coverage_origin (history : History gateway) (session : Admission.Session)
    (phase : gateway.admission.phase = .data session) (direction : Admission.Direction)
    (run : Admission.Coverage.Run Nat) (member : run ∈ (session.lane direction).coverage.runs) :
    Nonempty (CoverageOrigin history session direction run) := ⟨history.coverageOrigin session phase direction run member⟩

variable {gateway : Gateway} {history : History gateway} {session : Admission.Session}
  {selectedDirection : Admission.Direction} {run : Admission.Coverage.Run Nat}

theorem CoverageOrigin.earlier (origin : CoverageOrigin history session selectedDirection run) :
    origin.observation.prior.length < history.length := origin.observation.earlier

theorem CoverageOrigin.index (origin : CoverageOrigin history session selectedDirection run) :
    run.metadata = origin.observation.before.admission.observations.length := origin.observation.position

theorem CoverageOrigin.payload (origin : CoverageOrigin history session selectedDirection run) :
    run.bytes = origin.observation.transition.request.source.packet.segment.payload :=
  origin.source.evidence.bytes.trans (congrArg Segment.payload origin.observation.segment)

theorem CoverageOrigin.position (origin : CoverageOrigin history session selectedDirection run) :
    run.position = Seq.distance (session.lane selectedDirection).base
      origin.observation.transition.request.source.packet.segment.sequence := by
  rw [origin.source.evidence.position, origin.observation.segment]

theorem CoverageOrigin.wire_bytes (origin : CoverageOrigin history session selectedDirection run) :
    origin.source.seen.bytes = origin.observation.transition.request.source.bytes := origin.observation.bytes

theorem CoverageOrigin.attachment (origin : CoverageOrigin history session selectedDirection run) :
    origin.source.seen.attachment = origin.observation.transition.prepared.attachment := origin.observation.attachment

theorem CoverageOrigin.entry (origin : CoverageOrigin history session selectedDirection run) :
    origin.observation.transition.prepared.attachment.entry = session.entry := by
  rw [← origin.attachment]
  exact origin.source.evidence.entry

theorem CoverageOrigin.direction (origin : CoverageOrigin history session selectedDirection run) :
    origin.observation.transition.prepared.attachment.direction = selectedDirection := by
  rw [← origin.attachment]
  exact origin.source.evidence.direction

theorem CoverageOrigin.byte (origin : CoverageOrigin history session selectedDirection run)
    (index : Nat) (byte : UInt8) (selected : run.bytes[index]? = some byte) :
    origin.observation.transition.request.source.packet.segment.payload[index]? = some byte := by
  rw [← origin.payload]
  exact selected

theorem CoverageOrigin.byte_position (origin : CoverageOrigin history session selectedDirection run) (index : Nat) :
    run.position + index = Seq.distance (session.lane selectedDirection).base
      origin.observation.transition.request.source.packet.segment.sequence + index := by
  rw [origin.position]

theorem Snapshot.coverage_sources (snapshot : Snapshot) : snapshot.source.admission.CoverageSources :=
  snapshot.history.coverage_sources

theorem Installation.coverage_sources (installation : Installation snapshot sourceHistory target) :
    installation.state.admission.CoverageSources := by
  rw [installation.copied]
  exact snapshot.coverage_sources

end Netlib.Protocol.TCP.Checkpoint
