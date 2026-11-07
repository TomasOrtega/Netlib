import Netlib.Check.CampusTCPTwoTransferRecordedFacts

/-!
# Ordered controls in the actual transfer record

Each healthy phase has exactly its completed control prefix.
Finished records therefore retain all seven controls in order.
-/

namespace Netlib.Check.CampusTCPTwoTransferControlTrace

open Protocol.TCP CampusTCPModel
open CampusTCPTwoTransferMonitor
open CampusTCPTwoTransferRecorded (Recorded)

local notation "Config" => CampusTCPTwoTransferMonitor.Config

variable {input : Input} {monitor : Monitor} {control : Control}

def order : Mode → List Control
  | .armed | .invalid => []
  | .capture => [.pause]
  | .install => [.pause, .capture]
  | .clientRoute => [.pause, .capture, .install]
  | .serverRoute => [.pause, .capture, .install, .clientRoute]
  | .fence => [.pause, .capture, .install, .clientRoute, .serverRoute]
  | .resume => [.pause, .capture, .install, .clientRoute, .serverRoute, .fence]
  | .finished => [.pause, .capture, .install, .clientRoute, .serverRoute, .fence, .resume]

def Shape (monitor : Monitor) : Prop := monitor.controls.map (·.1) = order monitor.mode

private theorem selected_order (selected : controlDemand monitor = some control) :
    order control.after = order monitor.mode ++ [control] := by
  cases control <;> cases mode : monitor.mode <;> simp_all [controlDemand, order, Control.after]
  all_goals split at selected <;> simp_all

private theorem ordinary_frame (config : Config) (monitor : Monitor) (actual : Step input)
    (healthy : (ordinary config monitor actual).mode ≠ .invalid) :
    (ordinary config monitor actual).mode = monitor.mode ∧
      (ordinary config monitor actual).controls = monitor.controls := by
  dsimp only [ordinary] at healthy ⊢
  split at healthy
  · exact False.elim (healthy rfl)
  · rename_i valid
    rw [ite_eq_right valid]
    exact ⟨rfl, rfl⟩

private theorem drain_frame (config : Config) (monitor : Monitor) (actual : Step input) (ticket : Nat)
    (healthy : (observeDrain config monitor actual ticket).mode ≠ .invalid) :
    (observeDrain config monitor actual ticket).mode = monitor.mode ∧
      (observeDrain config monitor actual ticket).controls = monitor.controls := by
  cases present : actual.result.service <;> simp only [observeDrain, present] at healthy ⊢
  · exact False.elim (healthy rfl)
  · repeat' first
      | (solve | exact False.elim (healthy rfl))
      | (split at healthy)
    all_goals simp_all
    all_goals repeat' (split <;> simp_all)

theorem shape_step (config : Config) (monitor : Monitor) (actual : Step input) (shape : Shape monitor)
    (healthy : (observe config monitor actual).mode ≠ .invalid) : Shape (observe config monitor actual) := by
  obtain ⟨valid, supported, passed, allowed⟩ := CampusTCPTwoTransferAccounting.observe_checked config monitor actual healthy
  have checked : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoTransferMonitor.allowed config actual.before monitor actual.event) = true := by
    rw [supported, passed]
    exact allowed
  rw [CampusTCPTwoTransferMonitor.observe, ite_eq_left checked] at healthy ⊢
  cases drain : drainTicket actual.before monitor with
  | some ticket =>
    simp only [drain] at healthy ⊢
    cases event : actual.event <;> simp only [event] at healthy ⊢
    all_goals first
      | (solve |
        obtain ⟨mode, controls⟩ := ordinary_frame config monitor actual healthy
        simpa only [Shape, mode, controls] using shape)
      | (solve |
        obtain ⟨mode, controls⟩ := drain_frame config monitor actual ticket healthy
        simpa only [Shape, mode, controls] using shape)
  | none =>
    simp only [drain] at healthy ⊢
    cases selected : controlDemand monitor with
    | none =>
      simp only [selected] at healthy ⊢
      obtain ⟨mode, controls⟩ := ordinary_frame config monitor actual healthy
      simpa only [Shape, mode, controls] using shape
    | some control =>
      simp only [selected] at healthy ⊢
      cases event : actual.event <;> simp only [event] at healthy ⊢
      all_goals first
        | (solve |
          obtain ⟨mode, controls⟩ := ordinary_frame config monitor actual healthy
          simpa only [Shape, mode, controls] using shape)
        | (solve |
          simp only [Shape, List.map_append, List.map_cons, List.map_nil]
          rw [shape, ← selected_order selected])

theorem fold_shape (config : Config) (monitor : Monitor) (steps : List (Step input)) (shape : Shape monitor)
    (healthy : (steps.foldl (observe config) monitor).mode ≠ .invalid) :
    Shape (steps.foldl (observe config) monitor) := by
  induction steps generalizing monitor with
  | nil => exact shape
  | cons actual rest ih =>
    have nextHealthy := CampusTCPTwoTransferAccounting.fold_healthy config (observe config monitor actual) rest healthy
    exact ih (observe config monitor actual) (shape_step config monitor actual shape nextHealthy) healthy

theorem recorded_shape {complete : H.Completed input.active input.passive}
    {cut current : CampusTCPRound.Cut input complete} (recorded : Recorded cut config current monitor)
    (healthy : monitor.mode ≠ .invalid) : Shape monitor := by
  rw [← recorded.observed] at healthy ⊢
  exact fold_shape config .initial recorded.suffix rfl healthy

theorem finished_controls {complete : H.Completed input.active input.passive}
    {cut current : CampusTCPRound.Cut input complete} (recorded : Recorded cut config current monitor)
    (finished : monitor.mode = .finished) :
    monitor.controls.map (·.1) = [.pause, .capture, .install, .clientRoute, .serverRoute, .fence, .resume] := by
  have shape := recorded_shape recorded (by rw [finished]; decide)
  simpa only [Shape, finished, order] using shape

end Netlib.Check.CampusTCPTwoTransferControlTrace
