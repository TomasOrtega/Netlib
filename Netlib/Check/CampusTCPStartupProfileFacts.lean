import Netlib.Check.CampusTCPStartupProfile
import Netlib.Check.CampusTCPStartupTransferSuffix

/-!
# Startup profiles from one actual Actions certificate

An observed startup cut excludes earlier data and invalid modes.
Its cold sources and clock guards follow from the recorded whole prefix.
-/

namespace Netlib.Check.CampusTCPStartupProfileFacts

open CampusTCPModel CampusTCPStartupProfile

namespace E
export CampusTCPStartupTransferExecution (Monitor initial observe monitorAt allowed actions actions_correct)
end E
namespace P
export CampusTCPStartupMonitor (Monitor Mode observe)
end P
namespace M
export CampusTCPStartupTransferMonitor (Config)
end M
namespace B
export CampusTCPStartupClockBounds (Actions)
end B
namespace C
export CampusTCPRecoveryStartupCold (ColdEvent ColdProfile)
end C
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

variable {input : Input} {config : M.Config} {initial final : State input}
variable {events remaining : List Event} {steps : List (Step input)} {count slot : Nat}
variable {monitor : E.Monitor input} {current : P.Monitor}

theorem observe_startup_before {actual : Step input}
    (observed : E.observe config monitor actual = .startup current) : ∃ prior, monitor = .startup prior := by
  cases monitor with
  | startup prior => exact ⟨prior, rfl⟩
  | data handoff dataMonitor | invalid => simp only [E.observe, reduceCtorEq] at observed

theorem startup_observe_cold_before (prior : P.Monitor) (actual : Step input)
    (cold : ColdMode (P.observe config prior actual).mode) : ColdMode prior.mode := by
  cases mode : prior.mode with
  | preparation index | opening | drive => simp only [ColdMode]
  | setup stage =>
    change False
    simp only [P.observe, mode] at cold
    split at cold
    · cases stage <;> exact cold
    · exact cold
  | data | invalid =>
    change False
    simp only [P.observe, mode] at cold
    first
      | exact cold
      | split at cold <;> exact cold

theorem observe_cold_before {actual : Step input}
    (observed : E.observe config monitor actual = .startup current) (cold : ColdMode current.mode) :
    ∃ prior, monitor = .startup prior ∧ ColdMode prior.mode := by
  cases monitor with
  | startup prior =>
    refine ⟨prior, rfl, ?_⟩
    by_cases ready : (P.observe config prior actual).mode = .data
    · cases selected : CampusTCPStartupTransferConfig.snapshot actual.result.state <;>
        simp only [E.observe, ready, ↓reduceIte, selected, reduceCtorEq] at observed
    · simp only [E.observe, ready, ↓reduceIte] at observed
      cases observed
      exact startup_observe_cold_before prior actual cold
  | data handoff dataMonitor | invalid => simp only [E.observe, reduceCtorEq] at observed

theorem monitorAt_startup_before (ending : E.monitorAt config monitor steps count = .startup current) :
    ∃ prior, monitor = .startup prior := by
  induction steps generalizing monitor count with
  | nil => exact ⟨current, ending⟩
  | cons actual rest ih =>
    cases count with
    | zero => exact ⟨current, ending⟩
    | succ count =>
      obtain ⟨prior, observed⟩ := ih ending
      exact observe_startup_before observed

theorem monitorAt_cold_before (ending : E.monitorAt config monitor steps count = .startup current)
    (cold : ColdMode current.mode) : ∃ prior, monitor = .startup prior ∧ ColdMode prior.mode := by
  induction steps generalizing monitor count with
  | nil => exact ⟨current, ending, cold⟩
  | cons actual rest ih =>
    cases count with
    | zero => exact ⟨current, ending, cold⟩
    | succ count =>
      obtain ⟨prior, observed, before⟩ := ih ending
      exact observe_cold_before observed before

theorem monitorAt_startup_past (ending : E.monitorAt config monitor steps count = .startup current) (before : slot ≤ count) :
    ∃ prior, E.monitorAt config monitor steps slot = .startup prior := by
  apply monitorAt_startup_before (steps := steps.drop slot) (count := count - slot)
  rw [CampusTCPStartupTransferSuffix.monitorAt_drop, Nat.add_sub_of_le before]
  exact ending

theorem monitorAt_cold_past (ending : E.monitorAt config monitor steps count = .startup current)
    (cold : ColdMode current.mode) (before : slot ≤ count) :
    ∃ prior, E.monitorAt config monitor steps slot = .startup prior ∧ ColdMode prior.mode := by
  have tail : E.monitorAt config (E.monitorAt config monitor steps slot) (steps.drop slot) (count - slot) = .startup current := by
    rw [CampusTCPStartupTransferSuffix.monitorAt_drop, Nat.add_sub_of_le before]
    exact ending
  exact monitorAt_cold_before tail cold

private theorem take_step_fields (trace : Trace input initial events steps final remaining)
    (within : count ≤ steps.length) (actual : Step input) (member : actual ∈ steps.take count) :
    ∃ slot, slot < count ∧ actual.before = S.stateAt initial steps slot ∧ actual.event = S.eventAt steps slot := by
  obtain ⟨slot, selected⟩ := List.mem_iff_getElem?.mp member
  have inside := (List.getElem?_eq_some_iff.mp selected).1
  rw [List.length_take, Nat.min_eq_left within] at inside
  rw [List.getElem?_take_of_lt inside] at selected
  obtain ⟨same, found, before, event, _⟩ := CampusTCPSchedule.Trace.at trace slot (Nat.lt_of_lt_of_le inside within)
  have equal : same = actual := Option.some.inj (found.symm.trans selected)
  subst same
  exact ⟨slot, inside, before, event⟩

theorem Trace.clock_prefix (trace : Trace input initial events steps final remaining)
    (prep : Prep config.startup) (actions : E.actions config initial monitor steps = true)
    (within : count ≤ steps.length) (ending : E.monitorAt config monitor steps count = .startup current) :
    B.Actions config.transfer.quantum (steps.take count) := by
  intro actual member
  obtain ⟨slot, inside, before, event⟩ := take_step_fields trace within actual member
  obtain ⟨prior, mode⟩ := monitorAt_startup_past ending (Nat.le_of_lt inside)
  have permitted := (E.actions_correct _ _ _ _).mp actions slot (Nat.lt_of_lt_of_le inside within)
  rw [mode] at permitted
  have guard := allowed_clock prep permitted
  simpa only [← before, ← event] using guard

theorem Trace.no_copy_prefix (trace : Trace input initial events steps final remaining)
    (prep : Prep config.startup) (actions : E.actions config initial monitor steps = true)
    (within : count ≤ steps.length) (ending : E.monitorAt config monitor steps count = .startup current) :
    ∀ actual ∈ steps.take count, ∀ id, actual.event ≠ .copyPacket id := by
  intro actual member id
  obtain ⟨slot, inside, before, event⟩ := take_step_fields trace within actual member
  obtain ⟨prior, mode⟩ := monitorAt_startup_past ending (Nat.le_of_lt inside)
  have permitted := (E.actions_correct _ _ _ _).mp actions slot (Nat.lt_of_lt_of_le inside within)
  rw [mode] at permitted
  have excluded := allowed_no_copy prep permitted id
  simpa only [← event] using excluded

theorem Trace.cold_prefix (trace : Trace input initial events steps final remaining)
    (prep : Prep config.startup) (actions : E.actions config initial monitor steps = true)
    (within : count ≤ steps.length) (ending : E.monitorAt config monitor steps count = .startup current)
    (cold : ColdMode current.mode) : ∀ actual ∈ steps.take count, C.ColdEvent actual.event := by
  intro actual member
  obtain ⟨slot, inside, before, event⟩ := take_step_fields trace within actual member
  obtain ⟨prior, mode, priorCold⟩ := monitorAt_cold_past ending cold (Nat.le_of_lt inside)
  have permitted := (E.actions_correct _ _ _ _).mp actions slot (Nat.lt_of_lt_of_le inside within)
  rw [mode] at permitted
  have profile := allowed_cold prep priorCold permitted
  simpa only [← event] using profile

theorem Report.cut_clock_actions (report : Report input events) (prep : Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) report.steps = true)
    (within : count ≤ report.steps.length)
    (ending : E.monitorAt config (E.initial config) report.steps count = .startup current) :
    B.Actions config.transfer.quantum (CampusTCPSchedule.Report.cut report count within).steps :=
  Trace.clock_prefix report.trace prep actions within ending

theorem Report.cut_no_copy (report : Report input events) (prep : Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) report.steps = true)
    (within : count ≤ report.steps.length)
    (ending : E.monitorAt config (E.initial config) report.steps count = .startup current) :
    ∀ actual ∈ (CampusTCPSchedule.Report.cut report count within).steps, ∀ id, actual.event ≠ .copyPacket id :=
  Trace.no_copy_prefix report.trace prep actions within ending

theorem Report.cut_cold_profile (report : Report input events) (prep : Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) report.steps = true)
    (within : count ≤ report.steps.length)
    (ending : E.monitorAt config (E.initial config) report.steps count = .startup current)
    (cold : ColdMode current.mode) : C.ColdProfile (CampusTCPSchedule.Report.cut report count within) :=
  Trace.cold_prefix report.trace prep actions within ending cold

end Netlib.Check.CampusTCPStartupProfileFacts
