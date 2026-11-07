import Netlib.Check.CampusTCPStartupServiceEnabled

/-!
# Current data readiness for either admission mode

The data guards give a genuine legacy admission witness.
The selected execution mode retains that witness.
-/

namespace Netlib.Check.CampusTCPService

open Protocol

def ExistingDataReady.admissionReady
    (ready : ExistingDataReady context before source zone ingress hit session hop) (mode : X.Mode) :
    ExistingAdmissionReady context before source zone ingress hit hop mode := by
  refine ⟨ready.checks, ready.budget, ready.ingressPermit, ready.tracker, ?_, ready.ttl,
    ready.forwardComparison, ready.guardComparison, ready.covered⟩
  intro record member same
  have allowed : TCP.Admission.Allowed before.admission.phase
      (ConntrackLifecycle.selectedAttachment record hit.direction) source.packet.segment before.admission.observations := by
    rw [ready.phase]
    exact TCP.Admission.DataReady.allowed session _ source.packet.segment before.admission.observations
      (ready.binding record member same) rfl ready.data
  cases mode with
  | ordinary => exact allowed
  | startupRecovery => exact Or.inl allowed

def ExistingRepeatedReady.admissionReady
    (ready : ExistingRepeatedReady context before source zone ingress hit session hop) (mode : X.Mode) :
    ExistingAdmissionReady context before source zone ingress hit hop mode := by
  refine ⟨ready.checks, ready.budget, ready.ingressPermit, ready.tracker, ?_, ready.ttl,
    ready.forwardComparison, ready.guardComparison, ready.covered⟩
  intro record member same
  have allowed : TCP.Admission.Allowed before.admission.phase
      (ConntrackLifecycle.selectedAttachment record hit.direction) source.packet.segment before.admission.observations := by
    rw [ready.phase]
    exact TCP.Admission.RepeatedReady.allowed session _ source.packet.segment before.admission.observations
      (ready.binding record member same) rfl ready.repeated
  cases mode with
  | ordinary => exact allowed
  | startupRecovery => exact Or.inl allowed

end Netlib.Check.CampusTCPService
