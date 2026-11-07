import Netlib.Check.CampusTCPTwoTransferAccounting
import Netlib.Check.CampusTCPTwoProgressMonitorFacts
import Netlib.Check.CampusTCPPrimaryDrain
import Netlib.Theory.BoundedServiceRestriction

/-!
# Bounded service for the seven transfer controls

Control windows refer to the same stored trace and service condition.
-/

namespace Netlib.Check.CampusTCPTwoTransferControlBound

open CampusTCPModel (Input Step Event Actor State Trace Served)
open CampusTCPTwoTransferMonitor

local notation "Config" => CampusTCPTwoTransferMonitor.Config

variable {input : Input} {config : Config} {monitor : Monitor} {control : Control}

private theorem exchange_mode_beq (left right : CampusTCPTwoExchangeMonitor.Mode) :
    (left == right) = decide (left = right) := by cases left <;> cases right <;> rfl

private theorem local_mode_beq (left right : CampusTCPTwoProgressMonitor.Mode) :
    (left == right) = decide (left = right) := by cases left <;> cases right <;> rfl

theorem serves_control_event (event : Event) : control.serves config event = true ↔ event = control.event config := by
  cases control <;> cases event <;> simp [Control.serves, Control.event, beq_iff_eq]
  all_goals rename_i actor gateway; cases actor <;> cases gateway <;> simp

private theorem exchange_clock_due (cfg : CampusTCPTwoExchangeMonitor.Config)
    (value : CampusTCPTwoExchangeMonitor.Monitor) (actual : Step input)
    (due : transferDue value = true) (clock : actual.event = .advanceClock actor millis)
    (healthy : (CampusTCPTwoExchangeMonitor.observe cfg value actual).mode ≠ .invalid) :
    transferDue (CampusTCPTwoExchangeMonitor.observe cfg value actual) = true := by
  have forward : value.mode = .forward := by cases mode : value.mode <;> simp_all [transferDue, exchange_mode_beq, local_mode_beq]
  have originals : value.forward.mode = .originals := by cases mode : value.forward.mode <;> simp_all [transferDue, exchange_mode_beq, local_mode_beq]
  by_cases checked : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoExchangeMonitor.allowed cfg actual.before value actual.event) = true
  · have fields := Bool.and_eq_true_iff.mp checked
    have localAllowed : CampusTCPTwoProgressMonitor.Allowed cfg.forward actual.before value.forward actual.event := by
      simpa only [CampusTCPTwoExchangeMonitor.allowed, forward, CampusTCPTwoProgressMonitor.Allowed] using fields.2
    have localStep := CampusTCPTwoProgressMonitorFacts.observe_clock cfg.forward value.forward actual
      (Bool.and_eq_true_iff.mp fields.1).1 (Bool.and_eq_true_iff.mp fields.1).2 localAllowed clock
    simp only [CampusTCPTwoExchangeMonitor.observe, checked, forward, localStep, originals,
      local_mode_beq, reduceCtorEq, decide_false, Bool.false_eq_true, ite_true, ite_false]
    change transferDue value = true
    exact due
  · simp only [CampusTCPTwoExchangeMonitor.observe, checked,
      CampusTCPTwoExchangeMonitor.Monitor.invalid] at healthy
    exact False.elim (healthy rfl)

private theorem ordinary_control_clock (selected : controlDemand monitor = some control) (actual : Step input)
    (clock : actual.event = .advanceClock actor millis)
    (healthy : (ordinary config monitor actual).mode ≠ .invalid) :
    controlDemand (ordinary config monitor actual) = some control := by
  have nextHealthy : (CampusTCPTwoExchangeMonitor.observe (config.at actual.before) monitor.exchange actual).mode ≠ .invalid := by
    intro invalid
    simp only [ordinary, invalid, decide_true, ite_true, Monitor.invalid] at healthy
    exact healthy rfl
  have expanded : ordinary config monitor actual =
      { monitor with exchange := CampusTCPTwoExchangeMonitor.observe (config.at actual.before) monitor.exchange actual } := by
    simp only [ordinary, nextHealthy, decide_false, Bool.false_eq_true, ite_false]
  cases mode : monitor.mode with
  | armed =>
    have due : transferDue monitor.exchange = true := by
      simp only [controlDemand, mode] at selected
      split at selected
      · assumption
      · cases selected
    have nextDue := exchange_clock_due (config.at actual.before) monitor.exchange actual due clock nextHealthy
    simpa only [expanded, controlDemand, mode, nextDue, ite_true] using
      (show some Control.pause = some control by simpa only [controlDemand, mode, due, ite_true] using selected)
  | capture | install | clientRoute | serverRoute | fence | resume | finished | invalid =>
    simpa only [expanded, controlDemand, mode] using selected

private theorem ordinary_mode (actual : Step input)
    (healthy : (ordinary config monitor actual).mode ≠ .invalid) :
    (ordinary config monitor actual).mode = monitor.mode := by
  dsimp only [ordinary] at healthy ⊢
  split at healthy
  · exact False.elim (healthy rfl)
  · rename_i valid
    rw [ite_eq_right valid]

theorem observe_clock_control (selected : controlDemand monitor = some control) (actual : Step input)
    (clock : actual.event = .advanceClock actor millis)
    (healthy : (observe config monitor actual).mode ≠ .invalid) :
    controlDemand (observe config monitor actual) = some control ∧
      (observe config monitor actual).mode = monitor.mode := by
  obtain ⟨_, supported, passed, allowed⟩ := CampusTCPTwoTransferAccounting.observe_checked config monitor actual healthy
  change CampusTCPTwoTransferMonitor.allowed config actual.before monitor actual.event = true at allowed
  have checked : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoTransferMonitor.allowed config actual.before monitor actual.event) = true := by
    simp only [supported, passed, allowed, Bool.and_self]
  rw [observe, ite_eq_left checked] at healthy ⊢
  cases drained : drainTicket actual.before monitor with
  | none =>
    simp only [drained, selected, clock] at healthy ⊢
    exact ⟨ordinary_control_clock selected actual clock healthy, ordinary_mode actual healthy⟩
  | some ticket =>
    simp only [drained, clock] at healthy ⊢
    exact ⟨ordinary_control_clock selected actual clock healthy, ordinary_mode actual healthy⟩

theorem drain_serves_event {ticket : Nat} {event : Event} :
    drainServes ticket event = true ↔ event = .serve ticket none := by
  cases event <;> simp [drainServes]
  rename_i selected observed
  cases observed <;> simp

private theorem checked_mode (condition : Bool) (updated : CampusTCPTwoExchangeMonitor.Monitor)
    (healthy : (if condition then monitor.invalid else { monitor with exchange := updated }).mode ≠ .invalid) :
    (if condition then monitor.invalid else { monitor with exchange := updated }).mode = monitor.mode := by
  cases condition <;> simp_all [Monitor.invalid]

private theorem drain_result (actual : Step input) (healthy : (observeDrain config monitor actual ticket).mode ≠ .invalid) :
    ∃ served, actual.result.service = some served ∧ served.ticket.id = ticket ∧
      served.ticket.value.gateway = .primary ∧ (observeDrain config monitor actual ticket).mode = monitor.mode := by
  unfold observeDrain at healthy ⊢
  cases present : actual.result.service with
  | none => simp only [present, Monitor.invalid] at healthy; exact False.elim (healthy rfl)
  | some served =>
    simp only [present] at healthy ⊢
    by_cases checked : served.ticket.id = ticket ∧ served.ticket.value.gateway = .primary
    · simp only [checked] at healthy ⊢
      exact ⟨served, rfl, checked.1, checked.2, checked_mode _ _ healthy⟩
    · simp only [checked, decide_false, Bool.false_eq_true, ite_false, Monitor.invalid] at healthy
      exact False.elim (healthy rfl)

inductive Advance (config : Config) (monitor : Monitor) (control : Control) (actual : Step input) : Prop where
  | clock (actor : Actor) (millis : Nat) (event : actual.event = .advanceClock actor millis)
      (demand : controlDemand (observe config monitor actual) = some control)
      (mode : (observe config monitor actual).mode = monitor.mode)
  | drain (ticket : Nat) (served : Served input)
      (selected : drainTicket actual.before monitor = some ticket)
      (event : actual.event = .serve ticket none) (present : actual.result.service = some served)
      (primary : served.ticket.value.gateway = .primary)
      (mode : (observe config monitor actual).mode = monitor.mode)
  | control (event : actual.event = control.event config)
      (mode : (observe config monitor actual).mode = control.after)

theorem classify (selected : controlDemand monitor = some control) (actual : Step input)
    (healthy : (observe config monitor actual).mode ≠ .invalid) : Advance config monitor control actual := by
  obtain ⟨valid, supported, passed, checked⟩ := CampusTCPTwoTransferAccounting.observe_checked config monitor actual healthy
  change allowed config actual.before monitor actual.event = true at checked
  have guard : (actual.result.supported && actual.result.passed && allowed config actual.before monitor actual.event) = true := by
    simp only [supported, passed, checked, Bool.and_self]
  cases drain : drainTicket actual.before monitor with
  | some ticket =>
    cases event : actual.event
    all_goals first
      | exact .clock _ _ event (observe_clock_control selected actual event healthy).1
          (observe_clock_control selected actual event healthy).2
      | (
        have served : drainServes ticket actual.event = true := by simpa [allowed, valid, drain, event] using checked
        have same : observe config monitor actual = observeDrain config monitor actual ticket := by
          rw [observe, ite_eq_left guard, drain, event]
        have nextHealthy : (observeDrain config monitor actual ticket).mode ≠ .invalid := by rw [← same]; exact healthy
        obtain ⟨output, present, _, primary, mode⟩ := drain_result actual nextHealthy
        exact .drain ticket output drain (drain_serves_event.mp served) present primary (by rw [same]; exact mode))
  | none =>
    cases event : actual.event
    all_goals first
      | exact .clock _ _ event (observe_clock_control selected actual event healthy).1
          (observe_clock_control selected actual event healthy).2
      | (
        have served : control.serves config actual.event = true := by
          simpa [allowed, valid, drain, selected, event] using checked
        have same : (observe config monitor actual).mode = control.after := by
          rw [observe, ite_eq_left guard, drain, selected, event]
        exact .control ((serves_control_event actual.event).mp served) same)

def remainingControls (monitor : Monitor) : Nat :=
  match monitor.mode with
  | .armed => if transferDue monitor.exchange then 7 else 0
  | .capture => 6 | .install => 5 | .clientRoute => 4 | .serverRoute => 3 | .fence => 2 | .resume => 1
  | .finished | .invalid => 0

def potential (state : State input) (monitor : Monitor) : Nat :=
  if monitor.mode = .finished ∨ monitor.mode = .invalid then 0
  else remainingControls monitor + state.outstanding .primary

def ControlPhase (monitor : Monitor) : Prop :=
  (∃ control, controlDemand monitor = some control) ∨ monitor.mode = .finished ∨ monitor.mode = .invalid

def rank : Control → Nat
  | .pause => 7 | .capture => 6 | .install => 5 | .clientRoute => 4
  | .serverRoute => 3 | .fence => 2 | .resume => 1

private theorem rank_positive (control : Control) : 0 < rank control := by cases control <;> decide

private theorem transfer_mode_beq (left right : Mode) : (left == right) = decide (left = right) := by
  cases left <;> cases right <;> rfl

theorem drain_mode (selected : drainTicket state monitor = some ticket) : monitor.mode = .capture := by
  cases mode : monitor.mode <;> simp_all [drainTicket, transfer_mode_beq]

theorem control_valid (selected : controlDemand monitor = some control) :
    monitor.mode ≠ .finished ∧ monitor.mode ≠ .invalid := by
  constructor
  all_goals intro mode; simp only [controlDemand, mode] at selected; cases selected

theorem remaining_selected (selected : controlDemand monitor = some control) : remainingControls monitor = rank control := by
  cases mode : monitor.mode with
  | armed =>
    simp only [controlDemand, mode] at selected
    split at selected
    · rename_i due
      cases selected
      simp only [remainingControls, mode, due, ite_true, rank]
    · cases selected
  | capture | install | clientRoute | serverRoute | fence | resume | finished | invalid =>
    simp only [controlDemand, mode] at selected
    cases selected <;> simp only [remainingControls, mode, rank]

theorem potential_active (state : State input) (selected : controlDemand monitor = some control) :
    potential state monitor = rank control + state.outstanding .primary := by
  have valid := control_valid selected
  simp only [potential, valid.1, valid.2, or_self, ite_false, remaining_selected selected]

theorem potential_zero (phase : ControlPhase monitor) (zero : potential state monitor = 0) :
    monitor.mode = .finished ∨ monitor.mode = .invalid := by
  rcases phase with ⟨control, selected⟩ | finished | invalid
  · rw [potential_active state selected] at zero
    have positive := rank_positive control
    omega
  · exact .inl finished
  · exact .inr invalid

theorem observe_finished (mode : monitor.mode = .finished) (actual : Step input)
    (healthy : (observe config monitor actual).mode ≠ .invalid) :
    (observe config monitor actual).mode = .finished := by
  obtain ⟨_, supported, passed, checked⟩ := CampusTCPTwoTransferAccounting.observe_checked config monitor actual healthy
  change allowed config actual.before monitor actual.event = true at checked
  have guard : (actual.result.supported && actual.result.passed && allowed config actual.before monitor actual.event) = true := by
    simp only [supported, passed, checked, Bool.and_self]
  have drained : drainTicket actual.before monitor = none := by simp [drainTicket, mode, transfer_mode_beq]
  have selected : controlDemand monitor = none := by simp only [controlDemand, mode]
  rw [observe, ite_eq_left guard, drained, selected] at healthy ⊢
  exact (ordinary_mode actual healthy).trans mode

theorem phase_step (phase : ControlPhase monitor) (actual : Step input) :
    ControlPhase (observe config monitor actual) := by
  by_cases healthy : (observe config monitor actual).mode ≠ .invalid
  · rcases phase with ⟨control, selected⟩ | finished | invalid
    · cases classify selected actual healthy with
      | clock _ _ _ demand _ => exact .inl ⟨control, demand⟩
      | drain ticket _ drained _ _ _ mode =>
        have source := drain_mode drained
        exact .inl ⟨.capture, by simp only [controlDemand, mode, source]⟩
      | control _ mode =>
        cases control
        all_goals first
          | exact .inr (.inl (mode.trans rfl))
          | exact .inl ⟨_, by simp only [controlDemand, mode, Control.after]; rfl⟩
    · exact .inr (.inl (observe_finished finished actual healthy))
    · rw [CampusTCPTwoTransferAccounting.observe_invalid config monitor actual invalid] at healthy
      exact False.elim (healthy invalid)
  · exact .inr (.inr (Classical.byContradiction healthy))

theorem pending_active (state : State input) (selected : controlDemand monitor = some control) :
    ∃ demand, nextDemand config state monitor = some demand := by
  have valid := (control_valid selected).2
  simp only [nextDemand, valid, decide_false, Bool.false_eq_true, ite_false]
  cases drained : drainTicket state monitor with
  | some ticket => exact ⟨.drain ticket, rfl⟩
  | none => exact ⟨.transfer control, by rw [selected]⟩

private theorem active_clock_false (state : State input) (selected : controlDemand monitor = some control)
    (pending : nextDemand config state monitor = some demand) : serves config demand (.advanceClock actor millis) = false := by
  have valid := (control_valid selected).2
  simp only [nextDemand, valid, decide_false, Bool.false_eq_true, ite_false] at pending
  cases drained : drainTicket state monitor with
  | some ticket => rw [drained] at pending; cases pending; rfl
  | none => rw [drained, selected] at pending; cases pending; cases control <;> rfl

private theorem pending_same (selected : controlDemand monitor = some control)
    (updated : controlDemand next = some control) (mode : next.mode = monitor.mode)
    (work : after.work = before.work) : nextDemand config after next = nextDemand config before monitor := by
  have valid := (control_valid selected).2
  have nextValid := (control_valid updated).2
  have drained : drainTicket after next = drainTicket before monitor := by simp only [drainTicket, mode, work]
  simp only [nextDemand, valid, nextValid, decide_false, Bool.false_eq_true, ite_false, drained]
  cases drainTicket before monitor <;> simp only [selected, updated]

private theorem control_strict (selected : controlDemand monitor = some control)
    (mode : next.mode = control.after) (work : after.work = before.work) :
    potential after next < potential before monitor := by
  have count : after.outstanding .primary = before.outstanding .primary := by simp only [State.outstanding, work]
  rw [potential_active before selected]
  cases control <;> simp only [potential, mode, Control.after, remainingControls, rank, reduceCtorEq,
    or_self, ite_false, ite_true, or_false, count] <;> omega

theorem step_laws (phase : ControlPhase monitor) (actual : Step input) :
    potential actual.result.state (observe config monitor actual) ≤ potential actual.before monitor ∧
      (0 < potential actual.before monitor →
        potential actual.result.state (observe config monitor actual) = potential actual.before monitor →
          nextDemand config actual.result.state (observe config monitor actual) = nextDemand config actual.before monitor) ∧
      (0 < potential actual.before monitor → ∀ demand, nextDemand config actual.before monitor = some demand →
        serves config demand actual.event = true →
          potential actual.result.state (observe config monitor actual) < potential actual.before monitor) := by
  by_cases healthy : (observe config monitor actual).mode ≠ .invalid
  · rcases phase with ⟨control, selected⟩ | finished | invalid
    · cases classify selected actual healthy with
      | clock actor millis event demand mode =>
        have work := CampusTCPPrimaryDrain.clock_work actual actor millis event
        have count : actual.result.state.outstanding .primary = actual.before.outstanding .primary := by
          simp only [State.outstanding, work]
        have same : potential actual.result.state (observe config monitor actual) = potential actual.before monitor := by
          rw [potential_active _ demand, potential_active _ selected, count]
        refine ⟨Nat.le_of_eq same, fun _ _ => pending_same selected demand mode work, ?_⟩
        intro _ chosen pending served
        rw [event, active_clock_false actual.before selected pending] at served
        cases served
      | drain ticket output drained event present primary mode =>
        have sourceMode := drain_mode drained
        have nextSelected : controlDemand (observe config monitor actual) = some .capture := by
          simp only [controlDemand, mode, sourceMode]
        have oldSelected : controlDemand monitor = some .capture := by simp only [controlDemand, sourceMode]
        have count := CampusTCPPrimaryDrain.serve_primary_count actual ticket event output present primary
        have strict : potential actual.result.state (observe config monitor actual) < potential actual.before monitor := by
          rw [potential_active _ nextSelected, potential_active _ oldSelected]
          omega
        exact ⟨Nat.le_of_lt strict, by intro _ same; omega, fun _ _ _ _ => strict⟩
      | control event mode =>
        have work := CampusTCPPrimaryDrain.control_work actual (by rw [event]; cases control <;> trivial)
        have strict := control_strict selected mode work
        exact ⟨Nat.le_of_lt strict, by intro _ same; omega, fun _ _ _ _ => strict⟩
    · have nextFinished := observe_finished finished actual healthy
      simp only [potential, finished, nextFinished, true_or, ite_true, Nat.le_refl, Nat.lt_irrefl, false_implies, and_self]
    · rw [CampusTCPTwoTransferAccounting.observe_invalid config monitor actual invalid] at healthy
      exact False.elim (healthy invalid)
  · have invalid : (observe config monitor actual).mode = .invalid := Classical.byContradiction healthy
    simp only [potential, invalid, or_true, ite_true]
    exact ⟨Nat.zero_le _, by intro positive same; omega, fun positive _ _ _ => positive⟩

theorem potential_pending (phase : ControlPhase monitor) (state : State input) (positive : 0 < potential state monitor) :
    ∃ demand, nextDemand config state monitor = some demand := by
  rcases phase with ⟨control, selected⟩ | finished | invalid
  · exact pending_active state selected
  · simp only [potential, finished, true_or, ite_true, Nat.lt_irrefl] at positive
  · simp only [potential, invalid, or_true, ite_true, Nat.lt_irrefl] at positive

theorem monitorAt_next (steps : List (Step input)) (found : steps[index]? = some actual) :
    monitorAt config monitor steps (index + 1) = observe config (monitorAt config monitor steps index) actual := by
  induction steps generalizing index monitor with
  | nil => simp at found
  | cons head rest ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst actual
      simp only [monitorAt, monitorAt_zero]
    | succ index => exact ih found

variable {initial final : State input} {events remaining : List Event} {steps : List (Step input)} {bound start : Nat}

theorem phase_at (trace : Trace input initial events steps final remaining)
    (selected : controlDemand (monitorAt config monitor steps start) = some control)
    (order : start ≤ slot) (within : slot ≤ steps.length) : ControlPhase (monitorAt config monitor steps slot) := by
  obtain ⟨count, rfl⟩ := Nat.exists_eq_add_of_le order
  induction count with
  | zero => exact .inl ⟨control, by simpa only [Nat.add_zero] using selected⟩
  | succ count ih =>
    obtain ⟨actual, found, _, _, _⟩ := CampusTCPSchedule.Trace.at trace (start + count) (by omega)
    rw [← Nat.add_assoc, monitorAt_next steps found]
    exact phase_step (ih (by omega) (by omega)) actual

def potentialAt (config : Config) (initial : State input) (monitor : Monitor) (steps : List (Step input)) (slot : Nat) : Nat :=
  potential (CampusTCPSchedule.stateAt initial steps slot) (monitorAt config monitor steps slot)

private theorem laws_at (trace : Trace input initial events steps final remaining)
    (phase : ControlPhase (monitorAt config monitor steps slot)) (inside : slot < steps.length) :
    potentialAt config initial monitor steps (slot + 1) ≤ potentialAt config initial monitor steps slot ∧
      (0 < potentialAt config initial monitor steps slot →
        potentialAt config initial monitor steps (slot + 1) = potentialAt config initial monitor steps slot →
          ∀ demand, pendingAt config initial monitor steps slot = some demand →
            pendingAt config initial monitor steps (slot + 1) = some demand) ∧
      (0 < potentialAt config initial monitor steps slot → ∀ demand,
        pendingAt config initial monitor steps slot = some demand →
          serves config demand (CampusTCPSchedule.eventAt steps slot) = true →
            potentialAt config initial monitor steps (slot + 1) < potentialAt config initial monitor steps slot) := by
  obtain ⟨actual, found, before, event, after⟩ := CampusTCPSchedule.Trace.at trace slot inside
  have laws := step_laws (config := config) phase actual
  rw [before, after, ← monitorAt_next steps found, event] at laws
  exact ⟨laws.1, fun positive same demand pending => (laws.2.1 positive same).trans pending, laws.2.2⟩

namespace FiniteRank

open Netlib.Theory

universe u v
variable {Demand : Type u} {Action : Type v}
variable {length bound : Nat} {pending : Nat → Option Demand} {action : Nat → Action}
variable {serves : Demand → Action → Bool} {rank : Nat → Nat}

private theorem rank_mono
    (nonincrease : ∀ slot, slot < length → rank (slot + 1) ≤ rank slot)
    {first last : Nat} (order : first ≤ last) (within : last ≤ length) : rank last ≤ rank first := by
  obtain ⟨count, rfl⟩ := Nat.exists_eq_add_of_le order
  induction count with
  | zero => simp
  | succ count ih =>
    have step := nonincrease (first + count) (by omega)
    exact Nat.le_trans step (ih (by omega) (by omega))

private theorem block_decreases
    (service : BoundedServiceCheck.Serviced length pending action serves bound)
    (nonincrease : ∀ slot, slot < length → rank (slot + 1) ≤ rank slot)
    (demand : ∀ slot, slot ≤ length → 0 < rank slot → ∃ value, pending slot = some value)
    (persistent : ∀ slot, slot < length → 0 < rank slot → ∀ value, rank (slot + 1) = rank slot →
      pending slot = some value → pending (slot + 1) = some value)
    (strict : ∀ slot, slot < length → 0 < rank slot → ∀ value, pending slot = some value →
      serves value (action slot) = true → rank (slot + 1) < rank slot)
    (start : Nat) (within : start + bound ≤ length) (positive : 0 < rank start) :
    rank (start + bound) < rank start := by
  by_cases decreased : rank (start + bound) < rank start
  · exact decreased
  · have whole := rank_mono nonincrease (show start ≤ start + bound by omega) within
    have same : rank (start + bound) = rank start := by omega
    have equal : ∀ offset, offset ≤ bound → rank (start + offset) = rank start := by
      intro offset selected
      have lower := rank_mono nonincrease (show start + offset ≤ start + bound by omega) within
      have upper := rank_mono nonincrease (show start ≤ start + offset by omega) (by omega)
      omega
    obtain ⟨value, selected⟩ := demand start (by omega) positive
    have retained : ∀ offset, offset ≤ bound → pending (start + offset) = some value := by
      intro offset
      induction offset with
      | zero => simpa using selected
      | succ offset ih =>
        intro inside
        have previous := ih (by omega)
        have beforeEq := equal offset (by omega)
        have afterEq := equal (offset + 1) inside
        have next := persistent (start + offset) (by omega) (by omega) value
          (by simpa only [Nat.add_assoc] using afterEq.trans beforeEq.symm) previous
        simpa only [Nat.add_assoc] using next
    obtain ⟨offset, inside, served⟩ := service start within value selected
      (fun offset inside => retained offset (by omega))
    have beforeEq := equal offset (by omega)
    have decrease := strict (start + offset) (by omega) (by omega) value (retained offset (by omega)) served
    have afterEq := equal (offset + 1) (by omega)
    simp only [Nat.add_assoc] at decrease
    omega

private theorem rank_after_blocks
    (service : BoundedServiceCheck.Serviced length pending action serves bound)
    (nonincrease : ∀ slot, slot < length → rank (slot + 1) ≤ rank slot)
    (demand : ∀ slot, slot ≤ length → 0 < rank slot → ∃ value, pending slot = some value)
    (persistent : ∀ slot, slot < length → 0 < rank slot → ∀ value, rank (slot + 1) = rank slot →
      pending slot = some value → pending (slot + 1) = some value)
    (strict : ∀ slot, slot < length → 0 < rank slot → ∀ value, pending slot = some value →
      serves value (action slot) = true → rank (slot + 1) < rank slot)
    (start blocks : Nat) (within : start + blocks * bound ≤ length) :
    rank (start + blocks * bound) ≤ rank start - blocks := by
  induction blocks with
  | zero => simp
  | succ blocks ih =>
    have index : start + (blocks + 1) * bound = start + blocks * bound + bound := by
      simp only [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
    rw [index] at within ⊢
    have previous := ih (by omega)
    have next := rank_mono nonincrease
      (show start + blocks * bound ≤ start + blocks * bound + bound by omega) within
    by_cases empty : rank (start + blocks * bound) = 0
    · omega
    · have positive : 0 < rank (start + blocks * bound) := by omega
      have decrease := block_decreases service nonincrease demand persistent strict
        (start + blocks * bound) within positive
      omega

private theorem zero_by_at
    (service : BoundedServiceCheck.Serviced length pending action serves bound)
    (nonincrease : ∀ slot, slot < length → rank (slot + 1) ≤ rank slot)
    (demand : ∀ slot, slot ≤ length → 0 < rank slot → ∃ value, pending slot = some value)
    (persistent : ∀ slot, slot < length → 0 < rank slot → ∀ value, rank (slot + 1) = rank slot →
      pending slot = some value → pending (slot + 1) = some value)
    (strict : ∀ slot, slot < length → 0 < rank slot → ∀ value, pending slot = some value →
      serves value (action slot) = true → rank (slot + 1) < rank slot)
    (start : Nat) (within : start + rank start * bound ≤ length) :
    rank (start + rank start * bound) = 0 := by
  have reduced := rank_after_blocks service nonincrease demand persistent strict start (rank start) within
  omega


end FiniteRank

theorem controls_exit_by (trace : Trace input initial events steps final remaining)
    (service : Serviced config initial monitor steps bound)
    (selected : controlDemand (monitorAt config monitor steps start) = some control)
    (enough : start + potentialAt config initial monitor steps start * bound ≤ steps.length) :
    (monitorAt config monitor steps (start + potentialAt config initial monitor steps start * bound)).mode = .finished ∨
      (monitorAt config monitor steps (start + potentialAt config initial monitor steps start * bound)).mode = .invalid := by
  let score := fun offset => potentialAt config initial monitor steps (start + offset)
  have startWithin : start ≤ steps.length := by omega
  have relative : Theory.BoundedServiceCheck.Serviced (steps.length - start)
      (fun offset => pendingAt config initial monitor steps (start + offset))
      (fun offset => CampusTCPSchedule.eventAt steps (start + offset)) (serves config) bound :=
    Theory.BoundedServiceRestriction.suffix_service service startWithin
  have nonincrease : ∀ slot, slot < steps.length - start → score (slot + 1) ≤ score slot := by
    intro slot inside
    have phase := phase_at trace selected (slot := start + slot) (by omega) (by omega)
    have laws := laws_at trace phase (by omega)
    simpa only [score, Nat.add_assoc] using laws.1
  have demand : ∀ slot, slot ≤ steps.length - start → 0 < score slot →
      ∃ value, pendingAt config initial monitor steps (start + slot) = some value := by
    intro slot inside positive
    have phase := phase_at trace selected (slot := start + slot) (by omega) (by omega)
    exact potential_pending phase _ positive
  have persistent : ∀ slot, slot < steps.length - start → 0 < score slot → ∀ value,
      score (slot + 1) = score slot → pendingAt config initial monitor steps (start + slot) = some value →
        pendingAt config initial monitor steps (start + (slot + 1)) = some value := by
    intro slot inside positive value equal pending
    have phase := phase_at trace selected (slot := start + slot) (by omega) (by omega)
    have laws := laws_at trace phase (by omega)
    have same : potentialAt config initial monitor steps (start + slot + 1) =
        potentialAt config initial monitor steps (start + slot) := by simpa only [score, Nat.add_assoc] using equal
    simpa only [Nat.add_assoc] using laws.2.1 positive same value pending
  have strict : ∀ slot, slot < steps.length - start → 0 < score slot → ∀ value,
      pendingAt config initial monitor steps (start + slot) = some value →
        serves config value (CampusTCPSchedule.eventAt steps (start + slot)) = true → score (slot + 1) < score slot := by
    intro slot inside positive value pending served
    have phase := phase_at trace selected (slot := start + slot) (by omega) (by omega)
    have laws := laws_at trace phase (by omega)
    simpa only [score, Nat.add_assoc] using laws.2.2 positive value pending served
  have relativeEnough : 0 + score 0 * bound ≤ steps.length - start := by
    change 0 + potentialAt config initial monitor steps (start + 0) * bound ≤ steps.length - start
    simp only [Nat.add_zero, Nat.zero_add]
    omega
  have zero := FiniteRank.zero_by_at relative nonincrease demand persistent strict 0 relativeEnough
  have actualZero : potentialAt config initial monitor steps
      (start + potentialAt config initial monitor steps start * bound) = 0 := by
    simpa only [score, Nat.zero_add, Nat.add_zero] using zero
  exact potential_zero (phase_at trace selected (by omega) enough) actualZero

theorem armed_exits_by (trace : Trace input initial events steps final remaining)
    (service : Serviced config initial monitor steps bound)
    (armed : (monitorAt config monitor steps start).mode = .armed)
    (due : transferDue (monitorAt config monitor steps start).exchange = true)
    (enough : start + (7 + (CampusTCPSchedule.stateAt initial steps start).outstanding .primary) * bound ≤ steps.length) :
    (monitorAt config monitor steps
      (start + (7 + (CampusTCPSchedule.stateAt initial steps start).outstanding .primary) * bound)).mode = .finished ∨
    (monitorAt config monitor steps
      (start + (7 + (CampusTCPSchedule.stateAt initial steps start).outstanding .primary) * bound)).mode = .invalid := by
  have selected : controlDemand (monitorAt config monitor steps start) = some .pause := by
    simp only [controlDemand, armed, due, ite_true]
  have score : potentialAt config initial monitor steps start =
      7 + (CampusTCPSchedule.stateAt initial steps start).outstanding .primary :=
    potential_active _ selected
  have done := controls_exit_by trace service selected (by rw [score]; exact enough)
  simpa only [score] using done

private theorem fold_suffix (steps : List (Step input)) (slot : Nat) :
    (steps.drop slot).foldl (observe config) (monitorAt config monitor steps slot) =
      steps.foldl (observe config) monitor := by
  induction steps generalizing monitor slot with
  | nil => simp only [List.drop_nil, monitorAt, List.foldl_nil]
  | cons actual rest ih =>
    cases slot with
    | zero => rfl
    | succ slot => exact ih slot

theorem monitorAt_healthy (healthy : (steps.foldl (observe config) monitor).mode ≠ .invalid) (slot : Nat) :
    (monitorAt config monitor steps slot).mode ≠ .invalid := by
  apply CampusTCPTwoTransferAccounting.fold_healthy config (monitorAt config monitor steps slot) (steps.drop slot)
  rw [fold_suffix steps slot]
  exact healthy

theorem finishes_by (trace : Trace input initial events steps final remaining)
    (service : Serviced config initial monitor steps bound)
    (armed : (monitorAt config monitor steps start).mode = .armed)
    (due : transferDue (monitorAt config monitor steps start).exchange = true)
    (enough : start + (7 + (CampusTCPSchedule.stateAt initial steps start).outstanding .primary) * bound ≤ steps.length)
    (healthy : (steps.foldl (observe config) monitor).mode ≠ .invalid) :
    (monitorAt config monitor steps
      (start + (7 + (CampusTCPSchedule.stateAt initial steps start).outstanding .primary) * bound)).mode = .finished := by
  rcases armed_exits_by trace service armed due enough with finished | invalid
  · exact finished
  · exact False.elim (monitorAt_healthy healthy _ invalid)

end Netlib.Check.CampusTCPTwoTransferControlBound
