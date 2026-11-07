import Netlib.Check.CampusTCPTwoTransferControlState

/-!
# Control state across ordinary endpoint and assignment steps

Actual nonservice moves retain both gateway residents and control fields.
A current empty control demand restricts the transfer to its end phases.
-/

namespace Netlib.Check.CampusTCPTwoTransferControlState

open CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {current : Cut input complete} {actual : Step input}
variable {monitor : CampusTCPTwoTransferMonitor.Monitor} {location : Gateway} {paused : Bool}

private theorem environment_after (move : Move current actual)
    (quiet : CampusTCPRoundEnvironment.Nonservice actual.event) :
    CampusTCPRoundEnvironment.environment move.after.report.final =
      CampusTCPRoundEnvironment.environment current.report.final := by
  have transport : CampusTCPRoundEnvironment.TransportOnly actual.event := by
    cases event : actual.event <;> simp_all [CampusTCPRoundEnvironment.Nonservice, CampusTCPRoundEnvironment.TransportOnly]
  rw [move.final, ← move.beforeEq]
  exact (CampusTCPRoundEnvironment.Step.environment actual transport).symm

private theorem resident_after (move : Move current actual)
    (quiet : CampusTCPRoundEnvironment.Nonservice actual.event) (location : Gateway) :
    move.after.report.final.resident location = current.report.final.resident location := by
  rw [move.final, ← move.beforeEq]
  exact CampusTCPRoundEnvironment.Step.resident_nonservice actual quiet location

theorem Source.nonservice (source : Source current.report.final paused)
    (move : Move current actual) (quiet : CampusTCPRoundEnvironment.Nonservice actual.event) :
    Source move.after.report.final paused := by
  have environment := environment_after move quiet
  have standby : move.after.report.final.standby = current.report.final.standby := resident_after move quiet .standby
  exact {
    paused := (congrArg CampusTCPRoundEnvironment.Environment.assignmentPaused environment).trans source.paused
    unsealed := (congrArg CampusTCPRoundEnvironment.Environment.primarySealed environment).trans source.unsealed
    unfenced := (congrArg CampusTCPRoundEnvironment.Environment.primaryFenced environment).trans source.unfenced
    client := by
      have owners := congrArg CampusTCPRoundEnvironment.Environment.owners environment
      change move.after.report.final.owners = current.report.final.owners at owners
      rw [owners]
      exact source.client
    server := by
      have owners := congrArg CampusTCPRoundEnvironment.Environment.owners environment
      change move.after.report.final.owners = current.report.final.owners at owners
      rw [owners]
      exact source.server
    empty := by rw [standby]; exact source.empty
    namespaceEq := by rw [standby]; exact source.namespaceEq }

theorem Finished.nonservice (source : Finished current.report.final)
    (move : Move current actual) (quiet : CampusTCPRoundEnvironment.Nonservice actual.event) :
    Finished move.after.report.final := by
  have environment := environment_after move quiet
  have owners := congrArg CampusTCPRoundEnvironment.Environment.owners environment
  change move.after.report.final.owners = current.report.final.owners at owners
  exact {
    unpaused := (congrArg CampusTCPRoundEnvironment.Environment.assignmentPaused environment).trans source.unpaused
    sealed := (congrArg CampusTCPRoundEnvironment.Environment.primarySealed environment).trans source.sealed
    fenced := (congrArg CampusTCPRoundEnvironment.Environment.primaryFenced environment).trans source.fenced
    client := by rw [owners]; exact source.client
    server := by rw [owners]; exact source.server
    installed := (congrArg CampusTCPRoundEnvironment.Environment.installed environment).trans source.installed }

theorem Phase.ordinary_modes (phase : Phase current.report.final monitor.mode location)
    (ordinary : CampusTCPTwoTransferMonitor.controlDemand monitor = none) : monitor.mode = .armed ∨ monitor.mode = .finished := by
  generalize modeEq : monitor.mode = mode at phase
  cases phase with
  | armed => exact Or.inl rfl
  | finished => exact Or.inr rfl
  | capture | install | clientRoute | serverRoute | fence | resume =>
    simp only [CampusTCPTwoTransferMonitor.controlDemand, modeEq] at ordinary
    cases ordinary

theorem Phase.nonservice (phase : Phase current.report.final monitor.mode location)
    (ordinary : CampusTCPTwoTransferMonitor.controlDemand monitor = none)
    (move : Move current actual) (quiet : CampusTCPRoundEnvironment.Nonservice actual.event) :
    Phase move.after.report.final monitor.mode location := by
  generalize modeEq : monitor.mode = mode at phase
  cases phase with
  | armed source => exact .armed (source.nonservice move quiet)
  | finished source => exact .finished (source.nonservice move quiet)
  | capture | install | clientRoute | serverRoute | fence | resume =>
    simp only [CampusTCPTwoTransferMonitor.controlDemand, modeEq] at ordinary
    cases ordinary

end Netlib.Check.CampusTCPTwoTransferControlState
