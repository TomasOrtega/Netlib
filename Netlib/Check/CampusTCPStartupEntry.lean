import Netlib.Check.CampusTCPStartupProfileFacts

/-!
# An actual startup-to-data entry

The two observed modes identify the real transition, not a later data cut.
Setup predecessors retain their actual stored steps and event indices.
-/

namespace Netlib.Check.CampusTCPStartupEntry

open CampusTCPModel

namespace E
export CampusTCPStartupTransferExecution (Monitor initial observe monitorAt)
end E
namespace P
export CampusTCPStartupMonitor (Monitor Mode Setup initial observe allowed nextDemand)
end P
namespace M
export CampusTCPStartupTransferMonitor (Config)
end M
namespace T
export CampusTCPStartupTransferConfig (Handoff)
end T
namespace W
export CampusTCPTwoTransferMonitor (Monitor)
end W
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

inductive Point where
  | clientRecovery | serverRecovery | clientAck | serverAck | write | data
  deriving DecidableEq

def Point.mode : Point → P.Mode
  | .clientRecovery => .setup .clientRecovery
  | .serverRecovery => .setup .serverRecovery
  | .clientAck => .setup .clientAck
  | .serverAck => .setup .serverAck
  | .write => .setup .write
  | .data => .data

def Point.previous : Point → P.Mode
  | .clientRecovery => .drive
  | .serverRecovery => .setup .clientRecovery
  | .clientAck => .setup .serverRecovery
  | .serverAck => .setup .clientAck
  | .write => .setup .serverAck
  | .data => .setup .write

def Point.event (config : M.Config) : Point → Event
  | .clientRecovery => .finishStartup
  | .serverRecovery => .enableStartupRecovery .client
  | .clientAck => .enableStartupRecovery .server
  | .serverAck => .enableAck .client
  | .write => .enableAck .server
  | .data => .write .client (config.transfer.lower ++ config.transfer.upper)

variable {input : Input} {config : M.Config}

theorem observe_point (point : Point) (prior : P.Monitor) (actual : Step input)
    (mode : (P.observe config prior actual).mode = point.mode) :
    prior.mode = point.previous ∧ actual.event = point.event config ∧
      actual.result.supported = true ∧ actual.result.passed = true := by
  by_cases permitted : (actual.result.supported && actual.result.passed && CampusTCPStartupMonitor.allowed config actual.before prior actual.event) = true
  · have flags : (actual.result.supported = true ∧ actual.result.passed = true) ∧
        CampusTCPStartupMonitor.allowed config actual.before prior actual.event = true := by
      simpa only [Bool.and_eq_true] using permitted
    have support := flags.1.1
    have passed := flags.1.2
    cases before : prior.mode with
    | preparation index =>
      simp only [P.observe, permitted, ↓reduceIte, before] at mode
      split at mode <;> cases point <;> cases mode
    | opening =>
      simp only [P.observe, permitted, ↓reduceIte, before] at mode
      cases point <;> cases mode
    | drive =>
      by_cases finish : actual.event = .finishStartup
      · have accepted : (actual.result.supported && actual.result.passed &&
            CampusTCPStartupMonitor.allowed config actual.before prior .finishStartup) = true := by
          simpa only [finish] using permitted
        simp only [P.observe, finish, accepted, ↓reduceIte, before] at mode
        cases point <;> cases mode
        exact ⟨rfl, finish, support, passed⟩
      · simp only [P.observe, permitted, ↓reduceIte, before, finish] at mode
        cases point <;> cases mode
    | setup stage =>
      have selected : actual.event = CampusTCPStartupMonitor.Setup.event config stage := by
        have allowed := flags.2
        simp only [CampusTCPStartupMonitor.allowed, before, CampusTCPStartupMonitor.nextDemand] at allowed
        exact (Option.some.inj (of_decide_eq_true allowed)).symm
      simp only [P.observe, permitted, ↓reduceIte, before] at mode
      cases stage <;> cases point <;> cases mode
      all_goals exact ⟨rfl, selected, support, passed⟩
    | data | invalid =>
      simp only [P.observe, permitted, ↓reduceIte, before] at mode
      cases point <;> cases mode
  · simp only [P.observe, permitted] at mode
    cases point <;> cases mode

structure Entry (config : M.Config) (whole : Report input events) (slot : Nat) where
  within : slot < whole.steps.length
  startup : P.Monitor
  before : E.monitorAt config (E.initial config) whole.steps slot = .startup startup
  handoff : T.Handoff input.active input.passive
  dataMonitor : W.Monitor
  after : E.monitorAt config (E.initial config) whole.steps (slot + 1) = .data handoff dataMonitor

variable {events : List Event} {whole : Report input events} {slot : Nat}

def Entry.actual (entry : Entry config whole slot) : Step input := whole.steps[slot]'entry.within

theorem Entry.selected (entry : Entry config whole slot) : whole.steps[slot]? = some entry.actual :=
  List.getElem?_eq_some_iff.mpr ⟨entry.within, rfl⟩

theorem Entry.at (entry : Entry config whole slot) :
    entry.actual.before = S.stateAt input.initial whole.steps slot ∧
      entry.actual.event = S.eventAt whole.steps slot ∧
      entry.actual.result.state = S.stateAt input.initial whole.steps (slot + 1) := by
  obtain ⟨actual, found, before, event, after⟩ := CampusTCPSchedule.Trace.at whole.trace slot entry.within
  have same : actual = entry.actual := Option.some.inj (found.symm.trans entry.selected)
  subst actual
  exact ⟨before, event, after⟩

theorem monitorAt_next (config : M.Config) (monitor : E.Monitor input) (steps : List (Step input))
    (found : steps[index]? = some actual) :
    E.monitorAt config monitor steps (index + 1) = E.observe config (E.monitorAt config monitor steps index) actual := by
  induction steps generalizing monitor index with
  | nil => simp only [List.getElem?_nil, reduceCtorEq] at found
  | cons head rest ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst actual
      simp only [E.monitorAt, CampusTCPStartupTransferSuffix.monitorAt_zero]
    | succ index => exact ih _ found

theorem Entry.observed (entry : Entry config whole slot) :
    E.observe config (.startup entry.startup) entry.actual = .data entry.handoff entry.dataMonitor := by
  rw [← entry.before, ← monitorAt_next config (E.initial config) whole.steps entry.selected]
  exact entry.after

theorem Entry.fields (entry : Entry config whole slot) :
    entry.startup.mode = .setup .write ∧
      entry.actual.event = .write .client (config.transfer.lower ++ config.transfer.upper) ∧
      entry.actual.result.supported = true ∧ entry.actual.result.passed = true := by
  have entered := CampusTCPStartupTransferSuffix.observe_startup_data entry.actual entry.startup entry.observed
  exact observe_point .data entry.startup entry.actual entered.1

theorem Entry.initial_monitor (entry : Entry config whole slot) : entry.dataMonitor = .initial :=
  (CampusTCPStartupTransferSuffix.observe_startup_data entry.actual entry.startup entry.observed).2.2


theorem observe_startup_eq (prior : P.Monitor) (actual : Step input) (after : P.Monitor)
    (observed : E.observe config (.startup prior) actual = .startup after) : P.observe config prior actual = after := by
  simp only [E.observe] at observed
  split at observed
  · cases selected : CampusTCPStartupTransferConfig.snapshot actual.result.state <;>
      simp only [selected, reduceCtorEq] at observed
  · cases observed
    rfl

theorem initial_not_point (config : M.Config) (point : Point) : (P.initial config).mode ≠ point.mode := by
  intro same
  simp only [P.initial] at same
  split at same <;> cases point <;> cases same

structure Predecessor (config : M.Config) (whole : Report input events) (count : Nat) (point : Point) where
  index : Nat
  successor : count = index + 1
  within : index < whole.steps.length
  actual : Step input
  selected : whole.steps[index]? = some actual
  startup : P.Monitor
  before : E.monitorAt config (E.initial config) whole.steps index = .startup startup
  mode : startup.mode = point.previous
  event : actual.event = point.event config
  supported : actual.result.supported = true
  passed : actual.result.passed = true
  beforeState : actual.before = S.stateAt input.initial whole.steps index
  afterState : actual.result.state = S.stateAt input.initial whole.steps count

theorem predecessor (point : Point) {count : Nat} {current : P.Monitor}
    (within : count ≤ whole.steps.length)
    (atPoint : E.monitorAt config (E.initial config) whole.steps count = .startup current)
    (mode : current.mode = point.mode) : Nonempty (Predecessor config whole count point) := by
  cases count with
  | zero =>
    rw [CampusTCPStartupTransferSuffix.monitorAt_zero] at atPoint
    change CampusTCPStartupTransferExecution.Monitor.startup (P.initial config) = .startup current at atPoint
    cases atPoint
    exact False.elim (initial_not_point config point mode)
  | succ index =>
    obtain ⟨prior, before⟩ := CampusTCPStartupProfileFacts.monitorAt_startup_past atPoint (Nat.le_succ index)
    obtain ⟨actual, found, beforeState, event, afterState⟩ := CampusTCPSchedule.Trace.at whole.trace index (by omega)
    have update := monitorAt_next config (E.initial config) whole.steps found
    rw [before] at update
    have observed := update.symm.trans atPoint
    have same := observe_startup_eq prior actual current observed
    have fields := observe_point point prior actual ((congrArg (fun value : P.Monitor => value.mode) same).trans mode)
    exact ⟨⟨index, rfl, by omega, actual, found, prior, before,
      fields.1, fields.2.1, fields.2.2.1, fields.2.2.2, beforeState, afterState⟩⟩

end Netlib.Check.CampusTCPStartupEntry
