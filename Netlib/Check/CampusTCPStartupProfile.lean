import Netlib.Check.CampusTCPStartupMonitor
import Netlib.Check.CampusTCPRecoveryStartupCold

/-!
# Raw preparation and allowed startup events

Preparation contains only installed authentication and deployment operations.
The selected startup guard derives clock bounds and excludes packet copying.
-/

namespace Netlib.Check.CampusTCPStartupProfile

open CampusTCPModel

namespace M
export CampusTCPStartupTransferMonitor (Config StartupPlan)
end M
namespace P
export CampusTCPStartupMonitor (Monitor Mode Setup nextDemand allowed observe)
end P
namespace C
export CampusTCPRecoveryStartupCold (ColdEvent)
end C
namespace B
export CampusTCPStartupClockBounds (ClockGuard)
end B

def PreparationEvent : Event → Prop
  | .authentication _ | .install _ | .stage _ | .installGuard _
  | .installAt _ _ | .stageAt _ _ | .installGuardAt _ _ => True
  | _ => False

def Prep (plan : M.StartupPlan) : Prop := ∀ event ∈ plan.preparation, PreparationEvent event

def ColdMode : P.Mode → Prop
  | .preparation _ | .opening | .drive => True
  | _ => False

variable {input : Input} {config : M.Config} {state : State input}
variable {monitor : P.Monitor} {event : Event}

theorem PreparationEvent.cold (preparation : PreparationEvent event) : C.ColdEvent event := by
  cases event <;> simp only [PreparationEvent] at preparation
  all_goals trivial

theorem PreparationEvent.clock (preparation : PreparationEvent event) (state : State input) :
    B.ClockGuard quantum state event := by
  cases event <;> simp only [PreparationEvent] at preparation
  all_goals cases connected : state.connection <;> simp only [B.ClockGuard, connected]

theorem PreparationEvent.no_copy (preparation : PreparationEvent event) (id : Nat) : event ≠ .copyPacket id := by
  intro same
  subst event
  exact preparation

theorem preparation_allowed (prep : Prep config.startup) (mode : monitor.mode = .preparation index)
    (permitted : P.allowed config state monitor event = true) : PreparationEvent event := by
  simp only [P.allowed, mode, P.nextDemand] at permitted
  exact prep event (List.mem_of_getElem? (of_decide_eq_true permitted))

theorem Job.event_cold (job : CampusTCPStartupJobs.Job input) :
    C.ColdEvent (CampusTCPStartupSelection.Job.event config job) := by
  cases job <;> trivial

theorem Job.event_no_copy (job : CampusTCPStartupJobs.Job input) (id : Nat) :
    CampusTCPStartupSelection.Job.event config job ≠ .copyPacket id := by
  cases job <;> intro same <;> cases same

theorem job_allowed_cold (permitted : CampusTCPStartupSelection.jobAllowed config state event = true) : C.ColdEvent event := by
  obtain ⟨job, _, selected⟩ := List.any_eq_true.mp permitted
  have same := of_decide_eq_true selected
  rw [← same]
  exact Job.event_cold job

theorem job_allowed_no_copy (permitted : CampusTCPStartupSelection.jobAllowed config state event = true) (id : Nat) :
    event ≠ .copyPacket id := by
  obtain ⟨job, _, selected⟩ := List.any_eq_true.mp permitted
  have same := of_decide_eq_true selected
  rw [← same]
  exact Job.event_no_copy job id

theorem selection_clock (permitted : CampusTCPStartupSelection.allowed config state held event = true) :
    B.ClockGuard config.transfer.quantum state event := by
  cases event <;> first
    | exact CampusTCPStartupSelection.clock_guard permitted
    | cases connected : state.connection <;> simp only [B.ClockGuard, connected]

theorem selection_cold (permitted : CampusTCPStartupSelection.allowed config state held event = true) : C.ColdEvent event := by
  cases event <;> first
    | trivial
    | exact job_allowed_cold permitted

theorem selection_no_copy (permitted : CampusTCPStartupSelection.allowed config state held event = true) (id : Nat) :
    event ≠ .copyPacket id := by
  intro same
  subst event
  exact job_allowed_no_copy permitted id rfl

theorem Setup.event_clock (stage : P.Setup) (config : M.Config) (state : State input) :
    B.ClockGuard quantum state (CampusTCPStartupMonitor.Setup.event config stage) := by
  cases stage <;> cases connected : state.connection <;> simp only [B.ClockGuard, CampusTCPStartupMonitor.Setup.event, connected]

theorem Setup.event_no_copy (stage : P.Setup) (config : M.Config) (id : Nat) :
    CampusTCPStartupMonitor.Setup.event config stage ≠ .copyPacket id := by
  cases stage <;> intro same <;> cases same

theorem allowed_clock (prep : Prep config.startup) (permitted : P.allowed config state monitor event = true) :
    B.ClockGuard config.transfer.quantum state event := by
  cases mode : monitor.mode with
  | preparation index => exact (preparation_allowed prep mode permitted).clock state
  | opening =>
    simp only [P.allowed, mode, P.nextDemand] at permitted
    have same := Option.some.inj (of_decide_eq_true permitted)
    rw [← same]
    cases connected : state.connection <;> simp only [B.ClockGuard, connected]
  | drive => exact selection_clock (by simpa only [P.allowed, mode] using permitted)
  | setup stage =>
    simp only [P.allowed, mode, P.nextDemand] at permitted
    have same := Option.some.inj (of_decide_eq_true permitted)
    rw [← same]
    exact Setup.event_clock stage config state
  | data | invalid => simp only [P.allowed, mode, Bool.false_eq_true] at permitted

theorem allowed_no_copy (prep : Prep config.startup) (permitted : P.allowed config state monitor event = true) (id : Nat) :
    event ≠ .copyPacket id := by
  cases mode : monitor.mode with
  | preparation index => exact (preparation_allowed prep mode permitted).no_copy id
  | opening =>
    simp only [P.allowed, mode, P.nextDemand] at permitted
    have same := Option.some.inj (of_decide_eq_true permitted)
    rw [← same]
    intro impossible
    cases impossible
  | drive => exact selection_no_copy (by simpa only [P.allowed, mode] using permitted) id
  | setup stage =>
    simp only [P.allowed, mode, P.nextDemand] at permitted
    have same := Option.some.inj (of_decide_eq_true permitted)
    rw [← same]
    exact Setup.event_no_copy stage config id
  | data | invalid => simp only [P.allowed, mode, Bool.false_eq_true] at permitted

theorem allowed_cold (prep : Prep config.startup) (cold : ColdMode monitor.mode)
    (permitted : P.allowed config state monitor event = true) : C.ColdEvent event := by
  cases mode : monitor.mode with
  | preparation index => exact (preparation_allowed prep mode permitted).cold
  | opening =>
    simp only [P.allowed, mode, P.nextDemand] at permitted
    have same := Option.some.inj (of_decide_eq_true permitted)
    rw [← same]
    trivial
  | drive => exact selection_cold (by simpa only [P.allowed, mode] using permitted)
  | setup stage | data | invalid => simp only [ColdMode, mode] at cold

end Netlib.Check.CampusTCPStartupProfile
