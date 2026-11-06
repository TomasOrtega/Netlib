import Netlib.Check.CampusTCPFacts
import Netlib.Protocol.TCP.CheckpointCoverageFacts

/-!
# Sparse observation sources in the campus state

Both gateway histories come from the actual replay and exact checkpoint copy.
Holes do not weaken source evidence or establish later delivery.
-/

namespace Netlib.Check.CampusTCPSparseFacts

open Protocol
namespace M
export Check.CampusTCPModel (Report)
end M

structure Assurance (report : M.Report input events) where
  application : CampusTCPFacts.Assurance report
  primary : report.final.primary.transport.admission.CoverageSources
  standby : report.final.standby.transport.admission.CoverageSources

def assure (report : M.Report input events) : Except String (Assurance report) := do
  let application ← CampusTCPFacts.assure report
  return ⟨application, report.final.primary.history.coverage_sources, report.final.standby.history.coverage_sources⟩

def Assurance.primaryOrigin (_value : Assurance report) (session : TCP.Admission.Session)
    (phase : report.final.primary.transport.admission.phase = .data session)
    (direction : TCP.Admission.Direction) (run : TCP.Admission.Coverage.Run Nat)
    (member : run ∈ (session.lane direction).coverage.runs) :
    TCP.Checkpoint.CoverageOrigin report.final.primary.history session direction run :=
  report.final.primary.history.coverageOrigin session phase direction run member

def Assurance.standbyOrigin (_value : Assurance report) (session : TCP.Admission.Session)
    (phase : report.final.standby.transport.admission.phase = .data session)
    (direction : TCP.Admission.Direction) (run : TCP.Admission.Coverage.Run Nat)
    (member : run ∈ (session.lane direction).coverage.runs) :
    TCP.Checkpoint.CoverageOrigin report.final.standby.history session direction run :=
  report.final.standby.history.coverageOrigin session phase direction run member

theorem Assurance.application_prefix (value : Assurance report) :
    value.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes <+:
        value.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.written ∧
      value.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes <+:
        value.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.written :=
  value.application.application_prefix

end Netlib.Check.CampusTCPSparseFacts
