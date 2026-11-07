import Netlib.Check.CampusTCPStartupProfileFacts
import Netlib.Check.CampusTCPRecoveryStartupTransport
import Netlib.Check.CampusTCPRoundEnvironment

/-!
# Primary startup services from the actual prefix

Cold operations retain the initial route owners.
Each service selects a real pending ticket from its earlier assignment.
-/

namespace Netlib.Check.CampusTCPStartupPrimaryServices

open CampusTCPModel CampusTCPRecoveryStartupCold

namespace E
export CampusTCPStartupTransferExecution (initial Monitor monitorAt actions)
end E
namespace P
export CampusTCPStartupMonitor (Monitor)
end P
namespace M
export CampusTCPStartupTransferMonitor (Config)
end M
namespace R
export CampusTCPRoundEnvironment (Environment environment TransportOnly)
end R

variable {input : Input} {before : State input} {effect : Effect input} {gateway : Gateway} {id : String}

private theorem install_owners (computed : installConfiguration input before gateway id = .ok effect) :
    effect.state.owners = before.owners := by
  unfold installConfiguration at computed
  repeat' first
    | (solve | cases computed; cases gateway <;> rfl)
    | cases computed
    | split at computed
    | dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
        throw, throwThe, MonadExceptOf.throw] at computed

private theorem stage_owners (computed : stageAttachment input before gateway id = .ok effect) :
    effect.state.owners = before.owners := by
  unfold stageAttachment at computed
  repeat' first
    | (solve | cases computed; cases gateway <;> rfl)
    | cases computed
    | split at computed
    | dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure,
        throw, throwThe, MonadExceptOf.throw] at computed

private theorem guard_owners (computed : installIngress input before gateway id = .ok effect) :
    effect.state.owners = before.owners := by
  unfold installIngress at computed
  repeat' first
    | (solve | cases computed; cases gateway <;> rfl)
    | cases computed
    | split at computed
    | dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
        throw, throwThe, MonadExceptOf.throw] at computed

private theorem authentication_owners (computed : processCore input before (.authentication index) = .ok effect) :
    effect.state.owners = before.owners := by
  simp only [processCore] at computed
  repeat' first
    | (solve | cases computed; rfl)
    | cases computed
    | split at computed
    | dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed

theorem Step.cold_owners (actual : Step input) (cold : ColdEvent actual.event) :
    actual.result.state.owners = actual.before.owners := by
  by_cases transport : R.TransportOnly actual.event
  · exact (congrArg CampusTCPRoundEnvironment.Environment.owners (CampusTCPRoundEnvironment.Step.environment actual transport)).symm
  obtain ⟨effect, custody, computed, final⟩ := actual.processed
  have frame : effect.state.owners = actual.before.owners := by
    cases event : actual.event with
    | authentication index => rw [event] at computed; exact authentication_owners computed
    | install id | installAt gateway id => rw [event] at computed; exact install_owners computed
    | stage id | stageAt gateway id => rw [event] at computed; exact stage_owners computed
    | installGuard id | installGuardAt gateway id => rw [event] at computed; exact guard_owners computed
    | _ => simp only [event, ColdEvent, R.TransportOnly, not_true_eq_false] at cold transport
  simpa only [final] using frame

variable {initial final : State input} {events remaining : List Event} {steps : List (Step input)}

theorem Trace.cold_owners (trace : Trace input initial events steps final remaining)
    (cold : ∀ actual ∈ steps, ColdEvent actual.event) : final.owners = initial.owners := by
  induction trace with
  | done => rfl
  | stop head blocked rest => exact Step.cold_owners head (cold head (by simp))
  | next head supported rest ih =>
    exact (ih (fun actual member => cold actual (List.mem_cons_of_mem _ member))).trans
      (Step.cold_owners head (cold head (by simp)))

theorem Trace.each_cold_owners (trace : Trace input initial events steps final remaining)
    (cold : ∀ actual ∈ steps, ColdEvent actual.event) (actual : Step input) (member : actual ∈ steps) :
    actual.before.owners = initial.owners := by
  induction trace with
  | done => cases member
  | stop head blocked rest =>
    have same : actual = head := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
    subst actual
    rfl
  | next head supported rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst actual
      rfl
    · exact (ih (fun selected inside => cold selected (List.mem_cons_of_mem _ inside)) later).trans
        (Step.cold_owners head (cold head (by simp)))

theorem Report.owner_primary (report : Report input events) (cold : ColdProfile report)
    (actual : Step input) (member : actual ∈ report.steps) (actor : Actor) : actual.before.owner actor = .primary := by
  have owners := Trace.each_cold_owners report.trace cold actual member
  change actual.before.owners.get actor.leg = .primary
  rw [owners]
  cases actor <;> rfl

theorem Report.pending_primary (report : Report input events) (cold : ColdProfile report)
    (item : Work.Item (Ticket input.active input.passive)) (member : item ∈ report.final.work.pending) :
    item.value.gateway = .primary := by
  obtain ⟨assignment, index, ingress, produced, present, _, _, exactItem, _⟩ :=
    CampusTCPOrigins.Report.pending_origin report item member
  rw [exactItem]
  change assignment.before.owner produced.actor = .primary
  exact Report.owner_primary report cold assignment present produced.actor

theorem Report.service_primary (report : Report input events) (cold : ColdProfile report)
    (actual : Step input) (member : actual ∈ report.steps) (served : Served input)
    (recorded : actual.result.service = some served) : served.ticket.value.gateway = .primary := by
  obtain ⟨id, observed, completed, _, _, ticket, _, _⟩ := CampusTCPOrigins.service_origin actual served recorded
  obtain ⟨prior, later, history, preceding, _, _⟩ := CampusTCPFacts.step_origin report actual member
  let beforeReport : Report input (prior.map (·.event)) := ⟨actual.before, prior, [], preceding⟩
  have beforeCold : ColdProfile beforeReport := by
    intro selected inside
    apply cold selected
    rw [history]
    exact List.mem_append_left _ inside
  rw [ticket]
  exact Report.pending_primary beforeReport beforeCold completed.item completed.member

theorem Report.primary_services (report : Report input events) (cold : ColdProfile report) :
    CampusTCPRecoveryStartupTransport.PrimaryServices report := by
  intro served member
  obtain ⟨actual, present, recorded⟩ := List.mem_filterMap.mp member
  exact Report.service_primary report cold actual present served recorded

theorem Report.cut_primary_services (report : Report input events) (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) report.steps = true)
    (within : count ≤ report.steps.length)
    (ending : E.monitorAt config (E.initial config) report.steps count = .startup current)
    (cold : CampusTCPStartupProfile.ColdMode current.mode) :
    CampusTCPRecoveryStartupTransport.PrimaryServices (CampusTCPSchedule.Report.cut report count within) :=
  Report.primary_services _ (CampusTCPStartupProfileFacts.Report.cut_cold_profile report prep actions within ending cold)

end Netlib.Check.CampusTCPStartupPrimaryServices
