import Netlib.Check.CampusTCPRoundService

/-!
# Service evidence at an application connection

The mode equality transports the same stored service evidence.
-/

namespace Netlib.Check.CampusTCPApplicationService

open Protocol Protocol.TCP CampusTCPModel

variable {input : Input}

def ordinaryEvidence (evidence : CampusTCPService.Evidence context before source zone ingress mode)
    (ordinary : mode = AdmissionExecution.Mode.ordinary) :
    CampusTCPService.Evidence context before source zone ingress .ordinary := ordinary ▸ evidence

theorem ordinaryEvidence_fields (evidence : CampusTCPService.Evidence context before source zone ingress mode)
    (ordinary : mode = AdmissionExecution.Mode.ordinary) :
    (ordinaryEvidence evidence ordinary).tracker = evidence.tracker ∧
      (ordinaryEvidence evidence ordinary).admission = evidence.admission := by
  cases ordinary
  exact ⟨rfl, rfl⟩

def ordinaryProcessing (processing : CampusTCPService.Processing context before source zone mode)
    (ordinary : mode = AdmissionExecution.Mode.ordinary) :
    CampusTCPService.Processing context before source zone := ordinary ▸ processing

theorem ordinaryProcessing_fields (processing : CampusTCPService.Processing context before source zone mode)
    (ordinary : mode = AdmissionExecution.Mode.ordinary) :
    (ordinaryProcessing processing ordinary).prepared = processing.prepared ∧
      (ordinaryProcessing processing ordinary).outcome = processing.outcome ∧
      (ordinaryProcessing processing ordinary).nextAdmission = processing.nextAdmission := by
  cases ordinary
  exact ⟨rfl, rfl, rfl⟩

theorem ordinaryEvidence_processing (evidence : CampusTCPService.Evidence context before source zone ingress mode)
    (processing : CampusTCPService.Processing context before source zone mode)
    (ordinary : mode = AdmissionExecution.Mode.ordinary) (present : evidence.processing = some processing) :
    (ordinaryEvidence evidence ordinary).processing = some (ordinaryProcessing processing ordinary) := by
  cases ordinary
  exact present

def restoreProcessing (processing : CampusTCPService.Processing context before source zone)
    (ordinary : mode = AdmissionExecution.Mode.ordinary) :
    CampusTCPService.Processing context before source zone mode := ordinary.symm ▸ processing

theorem restoreProcessing_fields (processing : CampusTCPService.Processing context before source zone)
    (ordinary : mode = AdmissionExecution.Mode.ordinary) :
    (restoreProcessing processing ordinary).outcome = processing.outcome ∧
      (restoreProcessing processing ordinary).nextAdmission = processing.nextAdmission := by
  cases ordinary
  exact ⟨rfl, rfl⟩

theorem restoreProcessing_present (evidence : CampusTCPService.Evidence context before source zone ingress mode)
    (processing : CampusTCPService.Processing context before source zone)
    (ordinary : mode = AdmissionExecution.Mode.ordinary)
    (present : (ordinaryEvidence evidence ordinary).processing = some processing) :
    evidence.processing = some (restoreProcessing processing ordinary) := by
  cases ordinary
  exact present

theorem ordinary_processing
    (facts : CampusTCPRoundService.ServiceFacts (input := input) before item hit session actual served emission emitted)
    (ordinary : served.mode = AdmissionExecution.Mode.ordinary) :
    ∃ processing : CampusTCPService.Processing (input.contextFor served.ticket.value.gateway)
        served.before served.ticket.value.source input.zone,
      (ordinaryEvidence served.evidence ordinary).processing = some processing ∧
        processing.outcome.nextHop = some item.value.produced.actor.nextHop ∧
        processing.prepared.attachment.entry = session.entry ∧
        processing.prepared.attachment.direction = hit.direction ∧ processing.prepared.attachment.fresh = false := by
  obtain ⟨processing, present, hop, entry, direction, fresh⟩ := facts.processing
  have fields := ordinaryProcessing_fields processing ordinary
  refine ⟨ordinaryProcessing processing ordinary,
    ordinaryEvidence_processing served.evidence processing ordinary present, ?_, ?_, ?_, ?_⟩
  · rw [fields.2.1]
    exact hop
  · rw [fields.1]
    exact entry
  · rw [fields.1]
    exact direction
  · rw [fields.1]
    exact fresh

end Netlib.Check.CampusTCPApplicationService
