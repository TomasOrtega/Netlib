import Netlib.Check.CampusRevocationRank
import Netlib.Protocol.SafeHandoffPolicyFrames

/-!
# Operational frames for the checked revocation actions

Each retained policy comes from the actual stored gateway configuration.
The action check preserves the selected authentication prefix.
-/

namespace Netlib.Check.CampusRevocationControl

open Packet Protocol
open StatefulFailover (Gateway)
open CampusRevocationModel
open CampusRevocationTargets

private theorem network_configurations (before : State) (observation : CampusDeployment.Observation)
    (result : CampusDeployment.Result input)
    (computed : CampusDeployment.step input budget before.campus observation = .ok result)
    (evidence : CampusDeployment.NetworkEvidence input result.before) (kind : result.payload = .network evidence) :
    result.state.deployment.handoff.configurations =
      SafeHandoff.nextConfigurations before.campus.deployment.handoff evidence.event := by
  have prior := CampusDeployment.step_before input budget before.campus observation result computed
  have actual := evidence.actual_step
  have configurations := SafeHandoff.step_configurations result.before.deployment.handoff evidence.event
    evidence.model actual.1
  change (CampusDeployment.Payload.state result.payload).deployment.handoff.configurations = _
  rw [kind]
  change evidence.operated.state.handoff.configurations = _
  rw [actual.2, configurations]
  exact congrArg (fun state : CampusDeployment.State =>
    SafeHandoff.nextConfigurations state.deployment.handoff evidence.event) prior

theorem allowed_authentication (targets : Targets input after) (actual : Step input budget)
    (permitted : allowed targets actual = true) :
    actual.effect.state.campus.authentication = actual.before.campus.authentication := by
  change actual.effect.payload.state.campus.authentication = _
  cases payload : actual.effect.payload with
  | campus observation result computed =>
    have prior := CampusDeployment.step_before input budget actual.before.campus observation result computed
    cases kind : result.payload with
    | authentication evidence => simp [allowed, payload, kind] at permitted
    | withdraw evidence => simp [allowed, payload, kind] at permitted
    | network evidence =>
      simpa only [Payload.state, Payload.campusState, CampusDeployment.Result.state, kind, CampusDeployment.Payload.state] using
        congrArg CampusDeployment.State.authentication prior
  | packet call outcome computed certificate => rfl
  | deliver capacity => rfl
  | idle => rfl

theorem allowed_withdrawn (targets : Targets input after) (actual : Step input budget)
    (permitted : allowed targets actual = true) :
    actual.effect.state.campus.deployment.withdrawn = actual.before.campus.deployment.withdrawn := by
  change actual.effect.payload.state.campus.deployment.withdrawn = _
  cases payload : actual.effect.payload with
  | campus observation result computed =>
    have prior := CampusDeployment.step_before input budget actual.before.campus observation result computed
    cases kind : result.payload with
    | authentication evidence => simp [allowed, payload, kind] at permitted
    | withdraw evidence => simp [allowed, payload, kind] at permitted
    | network evidence =>
      obtain ⟨_, _, _, _, retained, _⟩ := CampusWithdrawal.step_operation_facts result.before.deployment
        evidence.event evidence.operated evidence.computed
      change (CampusDeployment.Payload.state result.payload).deployment.withdrawn = _
      rw [kind]
      exact retained.trans (congrArg (fun state : CampusDeployment.State => state.deployment.withdrawn) prior)
  | packet call outcome computed certificate => rfl
  | deliver capacity => rfl
  | idle => rfl

theorem step_binding (actual : Step input budget) (entry : NetfilterNAT.Entry)
    (binding : actual.before.campus.deployment.handoff.binding = some entry) :
    actual.effect.state.campus.deployment.handoff.binding = some entry := by
  change actual.effect.payload.state.campus.deployment.handoff.binding = _
  cases payload : actual.effect.payload with
  | campus observation result computed =>
    have prior := CampusDeployment.step_before input budget actual.before.campus observation result computed
    have before : result.before.deployment.handoff.binding = some entry := by rw [prior]; exact binding
    change (CampusDeployment.Payload.state result.payload).deployment.handoff.binding = _
    cases kind : result.payload with
    | authentication evidence => simpa only [kind, CampusDeployment.Payload.state] using before
    | network evidence =>
      have operation := evidence.actual_step
      change evidence.operated.state.handoff.binding = _
      rw [operation.2]
      exact SafeHandoff.step_binding result.before.deployment.handoff evidence.event evidence.model entry before operation.1
    | withdraw evidence =>
      have retained := (CampusWithdrawal.step_withdraw_facts result.before.deployment evidence.operated evidence.computed).2.2.2.1
      change evidence.operated.state.handoff.binding = _
      rw [retained]
      exact before
  | packet call outcome computed certificate => exact binding
  | deliver capacity => exact binding
  | idle => exact binding

theorem allowed_installed (targets : Targets input after) (actual : Step input budget)
    (permitted : allowed targets actual = true) (gateway : Gateway)
    (present : installed targets actual.before gateway = true) : installed targets actual.effect.state gateway = true := by
  apply (installed_correct targets actual.effect.state gateway).mpr
  have initial := (installed_correct targets actual.before gateway).mp present
  change actual.effect.payload.state.campus.deployment.handoff.configurations gateway = _
  cases payload : actual.effect.payload with
  | campus observation result computed =>
    cases kind : result.payload with
    | authentication evidence => simp [allowed, payload, kind] at permitted
    | withdraw evidence => simp [allowed, payload, kind] at permitted
    | network evidence =>
      change result.state.deployment.handoff.configurations gateway = _
      rw [network_configurations actual.before observation result computed evidence kind]
      cases event : evidence.event with
      | install selected configuration =>
        have chosen : sameConfiguration configuration (targets.get selected) = true := by
          simpa only [allowed, payload, kind, event] using permitted
        have target := (sameConfiguration_correct configuration (targets.get selected)).mp chosen
        by_cases equal : gateway = selected
        · subst gateway
          simpa [SafeHandoff.nextConfigurations] using target
        · simpa [SafeHandoff.nextConfigurations, equal] using initial
      | establish call | stage zone key | commit timeout | handoff leg selected | fence selected | forget
          | assign direction source | serve id => exact initial
  | packet call outcome computed certificate => exact initial
  | deliver capacity => exact initial
  | idle => exact initial

theorem serves_install (targets : Targets input after) (actual : Step input budget) (gateway : Gateway)
    (served : serves targets (.install gateway) (some actual) = true) :
    installed targets actual.effect.state gateway = true := by
  apply (installed_correct targets actual.effect.state gateway).mpr
  change actual.effect.payload.state.campus.deployment.handoff.configurations gateway = _
  cases payload : actual.effect.payload with
  | campus observation result computed =>
    cases kind : result.payload with
    | authentication evidence => simp [serves, payload, kind] at served
    | withdraw evidence => simp [serves, payload, kind] at served
    | network evidence =>
      change result.state.deployment.handoff.configurations gateway = _
      rw [network_configurations actual.before observation result computed evidence kind]
      cases event : evidence.event with
      | install selected configuration =>
        have selectedTarget : selected = gateway ∧ sameConfiguration configuration (targets.get gateway) = true := by
          simpa only [serves, payload, kind, event, Bool.and_eq_true, decide_eq_true_eq] using served
        obtain ⟨same, chosen⟩ := selectedTarget
        subst selected
        simpa [SafeHandoff.nextConfigurations] using
          (sameConfiguration_correct configuration (targets.get gateway)).mp chosen
      | establish call | stage zone key | commit timeout | handoff leg selected | fence selected | forget
          | assign direction source | serve id => simp [serves, payload, kind, event] at served
  | packet call outcome computed certificate => simp [serves, payload] at served
  | deliver capacity => simp [serves, payload] at served
  | idle => simp [serves, payload] at served

end Netlib.Check.CampusRevocationControl
