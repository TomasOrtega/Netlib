import Netlib.Check.CampusTCPTwoTransferControlTrace
import Netlib.Check.CampusTCPTwoTransferControlBound

/-!
# Stored events at the recorded control slots

Each control slot names its actual operation in the same suffix.
Control slots are strictly ordered and stay inside that suffix.
-/

namespace Netlib.Check.CampusTCPTwoTransferControlEvents

open Protocol.TCP CampusTCPModel
open CampusTCPTwoTransferMonitor
open CampusTCPTwoTransferRecorded (Recorded)

local notation "Config" => CampusTCPTwoTransferMonitor.Config

variable {input : Input} {config : Config} {monitor : Monitor} {actual : Step input}

private theorem ordinary_controls (config : Config) (monitor : Monitor) (actual : Step input)
    (healthy : (ordinary config monitor actual).mode ≠ .invalid) :
    (ordinary config monitor actual).controls = monitor.controls := by
  dsimp only [ordinary] at healthy ⊢
  split at healthy
  · exact False.elim (healthy rfl)
  · rename_i valid
    rw [ite_eq_right valid]

private theorem drain_controls (config : Config) (monitor : Monitor) (actual : Step input) (ticket : Nat)
    (healthy : (observeDrain config monitor actual ticket).mode ≠ .invalid) :
    (observeDrain config monitor actual ticket).controls = monitor.controls := by
  cases present : actual.result.service <;> simp only [observeDrain, present] at healthy ⊢
  · exact False.elim (healthy rfl)
  · repeat' first
      | (solve | exact False.elim (healthy rfl))
      | (split at healthy)
    all_goals simp_all
    all_goals repeat' (split <;> simp_all)

theorem observe_controls (healthy : (observe config monitor actual).mode ≠ .invalid) :
    (observe config monitor actual).controls = monitor.controls ∨
      ∃ control, actual.event = control.event config ∧
        (observe config monitor actual).controls = monitor.controls ++ [(control, monitor.exchange.slots)] := by
  obtain ⟨valid, supported, passed, allowed⟩ :=
    CampusTCPTwoTransferAccounting.observe_checked config monitor actual healthy
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
      | exact .inl (ordinary_controls config monitor actual healthy)
      | exact .inl (drain_controls config monitor actual ticket healthy)
  | none =>
    simp only [drain] at healthy ⊢
    cases selected : controlDemand monitor with
    | none =>
      simp only [selected] at healthy ⊢
      exact .inl (ordinary_controls config monitor actual healthy)
    | some control =>
      simp only [selected] at healthy ⊢
      cases event : actual.event <;> simp only [event] at healthy ⊢
      all_goals first
        | exact .inl (ordinary_controls config monitor actual healthy)
        | (have served : control.serves config actual.event = true := by
            simpa [Allowed, CampusTCPTwoTransferMonitor.allowed, valid, drain, selected, event] using allowed
           exact .inr ⟨control, by
             simpa only [event] using (CampusTCPTwoTransferControlBound.serves_control_event actual.event).mp served, rfl⟩)

structure Chronology (config : Config) (steps : List (Step input)) (controls : List (Control × Nat)) : Prop where
  event : ∀ control slot, (control, slot) ∈ controls →
    ∃ actual, steps[slot]? = some actual ∧ actual.event = control.event config
  bound : ∀ control slot, (control, slot) ∈ controls → slot < steps.length
  ordered : controls.Pairwise (fun first second => first.2 < second.2)

private theorem Chronology.extend (value : Chronology config prior controls) (actual : Step input) :
    Chronology config (prior ++ [actual]) controls where
  event := by
    intro control slot member
    obtain ⟨selected, found, event⟩ := value.event control slot member
    exact ⟨selected, (List.getElem?_append_left (value.bound control slot member)).trans found, event⟩
  bound := by
    intro control slot member
    have before := value.bound control slot member
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  ordered := value.ordered

private theorem Chronology.append_control (value : Chronology config prior controls)
    (actual : Step input) (control : Control) (event : actual.event = control.event config) :
    Chronology config (prior ++ [actual]) (controls ++ [(control, prior.length)]) where
  event := by
    intro selected slot member
    rcases List.mem_append.mp member with old | new
    · exact (value.extend actual).event selected slot old
    · have same : (selected, slot) = (control, prior.length) := List.mem_singleton.mp new
      cases same
      exact ⟨actual, List.getElem?_concat_length, event⟩
  bound := by
    intro selected slot member
    rcases List.mem_append.mp member with old | new
    · exact (value.extend actual).bound selected slot old
    · have same : (selected, slot) = (control, prior.length) := List.mem_singleton.mp new
      cases same
      simp
  ordered := by
    apply List.pairwise_append.mpr
    refine ⟨value.ordered, by simp, ?_⟩
    intro first member second selected
    have same : second = (control, prior.length) := List.mem_singleton.mp selected
    subst second
    exact value.bound first.1 first.2 member

theorem chronology_step (value : Chronology config prior monitor.controls)
    (slots : monitor.exchange.slots = prior.length)
    (healthy : (observe config monitor actual).mode ≠ .invalid) :
    Chronology config (prior ++ [actual]) (observe config monitor actual).controls := by
  rcases observe_controls healthy with same | ⟨control, event, appended⟩
  · rw [same]
    exact value.extend actual
  · rw [appended, slots]
    exact value.append_control actual control event

theorem fold_chronology (config : Config) (monitor : Monitor) (prior steps : List (Step input))
    (value : Chronology config prior monitor.controls) (slots : monitor.exchange.slots = prior.length)
    (healthy : (steps.foldl (observe config) monitor).mode ≠ .invalid) :
    Chronology config (prior ++ steps) (steps.foldl (observe config) monitor).controls := by
  induction steps generalizing prior monitor with
  | nil => simpa only [List.append_nil, List.foldl_nil] using value
  | cons actual rest ih =>
    have nextHealthy := CampusTCPTwoTransferAccounting.fold_healthy config (observe config monitor actual) rest healthy
    have nextValue := chronology_step value slots nextHealthy
    have nextSlots : (observe config monitor actual).exchange.slots = (prior ++ [actual]).length := by
      rw [(CampusTCPTwoTransferAccounting.observe_counters config monitor actual nextHealthy).2.2, slots]
      simp
    simpa only [List.foldl_cons, List.append_assoc, List.cons_append, List.nil_append] using
      ih (observe config monitor actual) (prior ++ [actual]) nextValue nextSlots healthy

theorem initial_chronology (config : Config) (steps : List (Step input))
    (healthy : (steps.foldl (observe config) .initial).mode ≠ .invalid) :
    Chronology config steps (steps.foldl (observe config) .initial).controls := by
  have empty : Chronology config ([] : List (Step input)) Monitor.initial.controls := {
    event := by intro control slot member; cases member
    bound := by intro control slot member; cases member
    ordered := by simp [Monitor.initial] }
  simpa only [List.nil_append] using fold_chronology config .initial [] steps empty rfl healthy

variable {complete : H.Completed input.active input.passive}
variable {cut current : CampusTCPRound.Cut input complete}
variable {control : Control} {slot : Nat}

theorem recorded_chronology (recorded : Recorded cut config current monitor) (healthy : monitor.mode ≠ .invalid) :
    Chronology config recorded.suffix monitor.controls := by
  have finalHealthy : (recorded.suffix.foldl (observe config) .initial).mode ≠ .invalid := by
    rw [recorded.observed]
    exact healthy
  have value := initial_chronology config recorded.suffix finalHealthy
  have same := congrArg Monitor.controls recorded.observed
  exact same ▸ value

theorem recorded_event (recorded : Recorded cut config current monitor) (healthy : monitor.mode ≠ .invalid)
    (member : (control, slot) ∈ monitor.controls) :
    ∃ actual, recorded.suffix[slot]? = some actual ∧ actual.event = control.event config :=
  (recorded_chronology recorded healthy).event control slot member

theorem recorded_bound (recorded : Recorded cut config current monitor) (healthy : monitor.mode ≠ .invalid)
    (member : (control, slot) ∈ monitor.controls) : slot < recorded.suffix.length :=
  (recorded_chronology recorded healthy).bound control slot member

theorem recorded_ordered (recorded : Recorded cut config current monitor) (healthy : monitor.mode ≠ .invalid) :
    (monitor.controls.map (·.2)).Pairwise (· < ·) :=
  List.pairwise_map.mpr (recorded_chronology recorded healthy).ordered

end Netlib.Check.CampusTCPTwoTransferControlEvents
