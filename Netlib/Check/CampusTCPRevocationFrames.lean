import Netlib.Check.CampusTCPRevocationTargets
import Netlib.Check.CampusTCPRevocationMonitor
import Netlib.Check.CampusTCPRoundEnvironment

/-!
# Stored sources during TCP revocation

Actual installation events select the fixed native source.
Transport operations preserve the policy and interface environment.
-/

namespace Netlib.Check.CampusTCPRevocationFrames

open CampusTCPModel
open CampusTCPRevocationTargets
namespace M
export CampusTCPRevocationMonitor (Installation requested)
end M
namespace E
export CampusTCPRoundEnvironment (Environment LocalEnvironment environment localEnvironment TransportOnly)
end E

private theorem install_configuration_environment (before : State input) (gateway : Gateway) (name : String)
    (effect : Effect input) (computed : installConfiguration input before gateway name = .ok effect) :
    ∃ configuration, (input.contextFor gateway).configs.find? (·.id == name) = some configuration ∧
      E.environment effect.state =
        E.environment (before.write gateway { before.resident gateway with configuration }) := by
  unfold installConfiguration at computed
  repeat' first
    | (solve | cases computed; exact ⟨_, by assumption, rfl⟩)
    | (cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
        throw, throwThe, MonadExceptOf.throw] at computed)

private theorem install_ingress_environment (before : State input) (gateway : Gateway) (name : String)
    (effect : Effect input) (computed : installIngress input before gateway name = .ok effect) :
    ∃ guard, (input.deployment gateway).guards.find? (·.id == name) = some guard ∧
      E.environment effect.state = E.environment (before.write gateway { before.resident gateway with guard }) := by
  unfold installIngress at computed
  repeat' first
    | (solve | cases computed; exact ⟨_, by assumption, rfl⟩)
    | (cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
        throw, throwThe, MonadExceptOf.throw] at computed)

theorem Step.forward_environment (actual : Step input) (gateway : Gateway) (name : String)
    (selected : M.requested actual.event = some (.forward gateway, name)) :
    ∃ configuration, (input.contextFor gateway).configs.find? (·.id == name) = some configuration ∧
      E.environment actual.result.state =
        E.environment (actual.before.write gateway { actual.before.resident gateway with configuration }) := by
  obtain ⟨effect, custody, computed, result⟩ := actual.processed
  have origin : installConfiguration input actual.before gateway name = .ok effect := by
    cases event : actual.event <;> simp [event, CampusTCPRevocationMonitor.requested] at selected
    all_goals rcases selected with ⟨rfl, rfl⟩; simpa only [event, processCore] using computed
  obtain ⟨configuration, found, same⟩ := install_configuration_environment actual.before gateway name effect origin
  exact ⟨configuration, found, by simpa only [result, E.environment] using same⟩

theorem Step.ingress_environment (actual : Step input) (gateway : Gateway) (name : String)
    (selected : M.requested actual.event = some (.ingress gateway, name)) :
    ∃ guard, (input.deployment gateway).guards.find? (·.id == name) = some guard ∧
      E.environment actual.result.state = E.environment (actual.before.write gateway { actual.before.resident gateway with guard }) := by
  obtain ⟨effect, custody, computed, result⟩ := actual.processed
  have origin : installIngress input actual.before gateway name = .ok effect := by
    cases event : actual.event <;> simp [event, CampusTCPRevocationMonitor.requested] at selected
    all_goals rcases selected with ⟨rfl, rfl⟩; simpa only [event, processCore] using computed
  obtain ⟨guard, found, same⟩ := install_ingress_environment actual.before gateway name effect origin
  exact ⟨guard, found, by simpa only [result, E.environment] using same⟩

theorem environment_resident (before after : State input) (same : E.environment before = E.environment after)
    (gateway : Gateway) : E.localEnvironment (before.resident gateway) = E.localEnvironment (after.resident gateway) := by
  cases gateway
  · exact congrArg CampusTCPRoundEnvironment.Environment.primary same
  · exact congrArg CampusTCPRoundEnvironment.Environment.standby same

theorem Target.forward_of_environment (target : Target input cut gateway) (before after : State input)
    (same : E.environment before = E.environment after) (installed : target.ForwardInstalled before) :
    target.ForwardInstalled after := by
  have configuration := congrArg CampusTCPRoundEnvironment.LocalEnvironment.configuration (environment_resident before after same gateway)
  exact configuration.symm.trans installed

theorem Target.ingress_of_environment (target : Target input cut gateway) (before after : State input)
    (same : E.environment before = E.environment after) (installed : target.IngressInstalled before) :
    target.IngressInstalled after := by
  have guard := congrArg CampusTCPRoundEnvironment.LocalEnvironment.guard (environment_resident before after same gateway)
  exact guard.symm.trans installed

theorem Target.current_of_environment (target : Target input cut gateway) (before after : State input)
    (same : E.environment before = E.environment after) (current : target.CurrentAt before) :
    target.CurrentAt after := by
  have authentication := congrArg CampusTCPRoundEnvironment.Environment.authentication same
  have resident := environment_resident before after same gateway
  have live := congrArg CampusTCPRoundEnvironment.LocalEnvironment.live resident
  have staged := congrArg (fun value : E.LocalEnvironment => value.attachments.map (·.value)) resident
  exact ⟨authentication.symm.trans current.1, live.symm.trans current.2.1, staged.symm.trans current.2.2⟩

theorem Step.target_forward (actual : Step input) (target : Target input cut gateway)
    (selected : M.requested actual.event = some (.forward gateway, target.names.configuration)) :
    target.ForwardInstalled actual.result.state := by
  obtain ⟨configuration, found, same⟩ := Step.forward_environment actual gateway target.names.configuration selected
  have source : configuration = target.configuration := Option.some.inj (found.symm.trans target.configurationFound)
  subst configuration
  apply Target.forward_of_environment target _ _ same.symm
  simp only [Target.ForwardInstalled, State.resident_write]

theorem Step.target_ingress (actual : Step input) (target : Target input cut gateway)
    (selected : M.requested actual.event = some (.ingress gateway, target.names.guard)) :
    target.IngressInstalled actual.result.state := by
  obtain ⟨guard, found, same⟩ := Step.ingress_environment actual gateway target.names.guard selected
  have source : guard = target.guard := Option.some.inj (found.symm.trans target.guardFound)
  subst guard
  apply Target.ingress_of_environment target _ _ same.symm
  simp only [Target.IngressInstalled, State.resident_write]

theorem Step.transport_current (actual : Step input) (target : Target input cut gateway)
    (selected : E.TransportOnly actual.event) (current : target.CurrentAt actual.before) :
    target.CurrentAt actual.result.state :=
  Target.current_of_environment target _ _ (CampusTCPRoundEnvironment.Step.environment actual selected) current

theorem Step.transport_forward (actual : Step input) (target : Target input cut gateway)
    (selected : E.TransportOnly actual.event) (installed : target.ForwardInstalled actual.before) :
    target.ForwardInstalled actual.result.state :=
  Target.forward_of_environment target _ _ (CampusTCPRoundEnvironment.Step.environment actual selected) installed

theorem Step.transport_ingress (actual : Step input) (target : Target input cut gateway)
    (selected : E.TransportOnly actual.event) (installed : target.IngressInstalled actual.before) :
    target.IngressInstalled actual.result.state :=
  Target.ingress_of_environment target _ _ (CampusTCPRoundEnvironment.Step.environment actual selected) installed

private theorem current_write_configuration (target : Target input cut gateway) (state : State input)
    (owner : Gateway) (configuration : Check.ConntrackLifecycle.Config) (current : target.CurrentAt state) :
    target.CurrentAt (state.write owner { state.resident owner with configuration }) := by
  cases gateway <;> cases owner <;> exact current

private theorem current_write_guard (target : Target input cut gateway) (state : State input)
    (owner : Gateway) (guard : Guard) (current : target.CurrentAt state) :
    target.CurrentAt (state.write owner { state.resident owner with guard }) := by
  cases gateway <;> cases owner <;> exact current

theorem Step.install_current (actual : Step input) (target : Target input cut gateway)
    (installation : M.Installation) (name : String)
    (selected : M.requested actual.event = some (installation, name)) (current : target.CurrentAt actual.before) :
    target.CurrentAt actual.result.state := by
  cases installation with
  | forward owner =>
    obtain ⟨configuration, found, same⟩ := Step.forward_environment actual owner name selected
    exact Target.current_of_environment target _ _ same.symm
      (current_write_configuration target actual.before owner configuration current)
  | ingress owner =>
    obtain ⟨guard, found, same⟩ := Step.ingress_environment actual owner name selected
    exact Target.current_of_environment target _ _ same.symm
      (current_write_guard target actual.before owner guard current)

theorem Step.forward_preserves_forward (actual : Step input) (target : Target input cut gateway)
    (owner : Gateway) (name : String) (selected : M.requested actual.event = some (.forward owner, name))
    (different : gateway ≠ owner) (installed : target.ForwardInstalled actual.before) :
    target.ForwardInstalled actual.result.state := by
  obtain ⟨configuration, found, same⟩ := Step.forward_environment actual owner name selected
  apply Target.forward_of_environment target _ _ same.symm
  cases gateway <;> cases owner <;>
    simp_all only [Target.ForwardInstalled, State.write, State.resident, ne_eq, not_true_eq_false]

theorem Step.forward_preserves_ingress (actual : Step input) (target : Target input cut gateway)
    (owner : Gateway) (name : String) (selected : M.requested actual.event = some (.forward owner, name))
    (installed : target.IngressInstalled actual.before) : target.IngressInstalled actual.result.state := by
  obtain ⟨configuration, found, same⟩ := Step.forward_environment actual owner name selected
  apply Target.ingress_of_environment target _ _ same.symm
  cases gateway <;> cases owner <;> exact installed

theorem Step.ingress_preserves_forward (actual : Step input) (target : Target input cut gateway)
    (owner : Gateway) (name : String) (selected : M.requested actual.event = some (.ingress owner, name))
    (installed : target.ForwardInstalled actual.before) : target.ForwardInstalled actual.result.state := by
  obtain ⟨guard, found, same⟩ := Step.ingress_environment actual owner name selected
  apply Target.forward_of_environment target _ _ same.symm
  cases gateway <;> cases owner <;> exact installed

theorem Step.ingress_preserves_ingress (actual : Step input) (target : Target input cut gateway)
    (owner : Gateway) (name : String) (selected : M.requested actual.event = some (.ingress owner, name))
    (different : gateway ≠ owner) (installed : target.IngressInstalled actual.before) :
    target.IngressInstalled actual.result.state := by
  obtain ⟨guard, found, same⟩ := Step.ingress_environment actual owner name selected
  apply Target.ingress_of_environment target _ _ same.symm
  cases gateway <;> cases owner <;>
    simp_all only [Target.IngressInstalled, State.write, State.resident, ne_eq, not_true_eq_false]

def _root_.Netlib.Check.CampusTCPRevocationTargets.Targets.names (targets : Targets input cut) : M.Installation → String
  | .forward gateway => (targets.get gateway).names.configuration
  | .ingress gateway => (targets.get gateway).names.guard

def _root_.Netlib.Check.CampusTCPRevocationTargets.Targets.Stored (targets : Targets input cut) : M.Installation → State input → Prop
  | .forward gateway, state => (targets.get gateway).ForwardInstalled state
  | .ingress gateway, state => (targets.get gateway).IngressInstalled state

theorem Step.requested_stored (actual : Step input) (targets : Targets input cut) (installation : M.Installation)
    (selected : M.requested actual.event = some (installation, targets.names installation)) :
    targets.Stored installation actual.result.state := by
  cases installation with
  | forward gateway => exact Step.target_forward actual (targets.get gateway) selected
  | ingress gateway => exact Step.target_ingress actual (targets.get gateway) selected

theorem selected_requested (names : M.Installation → String) (event : Event) (installation : M.Installation)
    (selected : CampusTCPRevocationMonitor.selected names event = some installation) :
    M.requested event = some (installation, names installation) := by
  cases request : M.requested event with
  | none => simp only [CampusTCPRevocationMonitor.selected, request, reduceCtorEq] at selected
  | some pair =>
    rcases pair with ⟨chosen, name⟩
    by_cases same : name = names chosen
    · simp only [CampusTCPRevocationMonitor.selected, request, same, ite_true, Option.some.injEq] at selected
      subst chosen
      simp only [same]
    · simp only [CampusTCPRevocationMonitor.selected, request, same, ite_false, reduceCtorEq] at selected

theorem Step.selected_stored (actual : Step input) (targets : Targets input cut) (installation : M.Installation)
    (selected : CampusTCPRevocationMonitor.selected targets.names actual.event = some installation) :
    targets.Stored installation actual.result.state :=
  Step.requested_stored actual targets installation (selected_requested _ _ _ selected)

theorem Step.stored (actual : Step input) (targets : Targets input cut) (installation : M.Installation)
    (allowed : E.TransportOnly actual.event ∨
      ∃ changed, M.requested actual.event = some (changed, targets.names changed))
    (installed : targets.Stored installation actual.before) : targets.Stored installation actual.result.state := by
  rcases allowed with transport | ⟨changed, selected⟩
  · cases installation with
    | forward gateway => exact Step.transport_forward actual (targets.get gateway) transport installed
    | ingress gateway => exact Step.transport_ingress actual (targets.get gateway) transport installed
  · cases installation with
    | forward gateway =>
      cases changed with
      | forward owner =>
        by_cases same : gateway = owner
        · subst owner
          exact Step.target_forward actual (targets.get gateway) selected
        · exact Step.forward_preserves_forward actual (targets.get gateway) owner _ selected same installed
      | ingress owner => exact Step.ingress_preserves_forward actual (targets.get gateway) owner _ selected installed
    | ingress gateway =>
      cases changed with
      | forward owner => exact Step.forward_preserves_ingress actual (targets.get gateway) owner _ selected installed
      | ingress owner =>
        by_cases same : gateway = owner
        · subst owner
          exact Step.target_ingress actual (targets.get gateway) selected
        · exact Step.ingress_preserves_ingress actual (targets.get gateway) owner _ selected same installed

theorem Step.current (actual : Step input) (targets : Targets input cut)
    (allowed : E.TransportOnly actual.event ∨
      ∃ changed, M.requested actual.event = some (changed, targets.names changed))
    (current : targets.CurrentAt actual.before) : targets.CurrentAt actual.result.state := by
  intro gateway
  rcases allowed with transport | ⟨changed, selected⟩
  · exact Step.transport_current actual (targets.get gateway) transport (current gateway)
  · exact Step.install_current actual (targets.get gateway) changed _ selected (current gateway)

def _root_.Netlib.Check.CampusTCPRevocationTargets.Targets.Established (targets : Targets input cut)
    (monitor : CampusTCPRevocationMonitor.Monitor) (state : State input) : Prop :=
  ∀ installation, installation ∉ monitor → targets.Stored installation state

theorem initial_established (targets : Targets input cut) (state : State input) :
    targets.Established CampusTCPRevocationMonitor.initial state := by
  intro installation absent
  cases installation with
  | forward gateway => cases gateway <;> simp [CampusTCPRevocationMonitor.initial] at absent
  | ingress gateway => cases gateway <;> simp [CampusTCPRevocationMonitor.initial] at absent

theorem Step.established (actual : Step input) (targets : Targets input cut)
    (monitor : CampusTCPRevocationMonitor.Monitor)
    (allowed : E.TransportOnly actual.event ∨
      ∃ changed, M.requested actual.event = some (changed, targets.names changed))
    (prior : targets.Established monitor actual.before) :
    targets.Established (CampusTCPRevocationMonitor.observe targets.names monitor actual.event) actual.result.state := by
  intro installation absent
  cases selected : CampusTCPRevocationMonitor.selected targets.names actual.event with
  | none =>
    simp only [CampusTCPRevocationMonitor.observe, selected] at absent
    exact Step.stored actual targets installation allowed (prior installation absent)
  | some changed =>
    by_cases same : installation = changed
    · subst installation
      exact Step.selected_stored actual targets changed selected
    · have missing : installation ∉ monitor := by
        intro member
        apply absent
        simp only [CampusTCPRevocationMonitor.observe, selected]
        exact (List.mem_erase_of_ne same).mpr member
      exact Step.stored actual targets installation allowed (prior installation missing)

theorem established_installed (targets : Targets input cut) (state : State input)
    (established : targets.Established [] state) : targets.Installed state := by
  intro gateway
  exact ⟨established (.forward gateway) (by simp), established (.ingress gateway) (by simp)⟩

theorem Trace.established (trace : Trace input initial events steps final remaining) (targets : Targets input cut)
    (monitor : CampusTCPRevocationMonitor.Monitor)
    (allowed : ∀ actual ∈ steps, E.TransportOnly actual.event ∨
      ∃ changed, M.requested actual.event = some (changed, targets.names changed))
    (prior : targets.Established monitor initial) :
    targets.Established
      (CampusTCPRevocationMonitor.monitorAt targets.names monitor steps steps.length) final := by
  induction trace generalizing monitor with
  | done state => exact prior
  | stop head blocked tail =>
    exact Step.established head targets monitor (allowed head (by simp)) prior
  | next head supported rest ih =>
    exact ih (CampusTCPRevocationMonitor.observe targets.names monitor head.event)
      (fun actual member => allowed actual (List.mem_cons_of_mem _ member))
      (Step.established head targets monitor (allowed head (by simp)) prior)

theorem Trace.current (trace : Trace input initial events steps final remaining) (targets : Targets input cut)
    (allowed : ∀ actual ∈ steps, E.TransportOnly actual.event ∨
      ∃ changed, M.requested actual.event = some (changed, targets.names changed))
    (prior : targets.CurrentAt initial) : targets.CurrentAt final := by
  induction trace with
  | done state => exact prior
  | stop head blocked tail => exact Step.current head targets (allowed head (by simp)) prior
  | next head supported rest ih =>
    exact ih (fun actual member => allowed actual (List.mem_cons_of_mem _ member))
      (Step.current head targets (allowed head (by simp)) prior)

end Netlib.Check.CampusTCPRevocationFrames
