import Netlib.Check.CampusRevocationModel
import Netlib.Check.CampusRevocationTargets
import Netlib.Check.CampusRevocationTrace

/-!
# Actual authentication triggers for campus revocation

The trigger consumes the next recorded authentication observation.
Its event determines the revoked state at that same replay cut.
-/

namespace Netlib.Check.CampusRevocationTrigger

open Protocol CampusRevocationModel

variable {input : Input} {budget : Nat}

def triggerEvent : EAPSession.Event → Bool
  | .authentication .logoff | .application .revoke | .close => true
  | _ => false

theorem triggerEvent_correct (event : EAPSession.Event) :
    triggerEvent event = true ↔ event = .authentication .logoff ∨
      event = .application .revoke ∨ event = .close := by
  cases event with
  | authentication event => cases event <;> simp [triggerEvent]
  | application event => cases event <;> simp [triggerEvent]
  | close => simp [triggerEvent]

def triggered (actual : Step input budget) : Bool :=
  match actual.effect.payload with
  | .campus _ result _ => match result.payload with
    | .authentication evidence => triggerEvent evidence.source.event
    | _ => false
  | _ => false

private theorem audit_append_final (context : Context) (initial : EAPSession.State)
    (prior later : List EAP.Observation) :
    (EAP.audit context initial (prior ++ later)).final =
      (EAP.audit context (EAP.audit context initial prior).final later).final := by
  induction prior generalizing initial with
  | nil => rfl
  | cons head tail ih =>
    simpa only [List.cons_append, EAP.audit] using ih (EAPSession.step context initial head.event)

private theorem current_succ (authentication : EAP.Input) (slot : Nat)
    (within : slot < authentication.observations.length) :
    SessionInstallation.current authentication (slot + 1) =
      EAPSession.step authentication.context (SessionInstallation.current authentication slot)
        (authentication.observations[slot]'within).event := by
  change (EAP.audit authentication.context EAPSession.State.initial
    (authentication.observations.take (slot + 1))).final = _
  rw [List.take_succ_eq_append_getElem within, audit_append_final]
  rfl

theorem triggered_source (actual : Step input budget) (selected : triggered actual = true) :
    ∃ source : EAP.Observation,
      input.authentication.observations[actual.before.campus.authentication]? = some source ∧
      (source.event = .authentication .logoff ∨ source.event = .application .revoke ∨ source.event = .close) ∧
      actual.effect.state.campus.authentication = actual.before.campus.authentication + 1 := by
  cases payload : actual.effect.payload with
  | campus observation result computed =>
    cases oldPayload : result.payload with
    | authentication evidence =>
      have before := CampusDeployment.step_before input budget actual.before.campus observation result computed
      have kind : triggerEvent evidence.source.event = true := by
        simpa only [triggered, payload, oldPayload] using selected
      refine ⟨evidence.source, ?_, (triggerEvent_correct _).mp kind, ?_⟩
      · have found := List.getElem?_eq_getElem evidence.available
        simpa only [CampusDeployment.AuthenticationEvidence.source, before] using found
      · change actual.effect.payload.state.campus.authentication = _
        rw [payload]
        change result.payload.state.authentication = _
        rw [oldPayload]
        change result.before.authentication + 1 = _
        rw [before]
    | network evidence => simp only [triggered, payload, oldPayload, Bool.false_eq_true] at selected
    | withdraw evidence => simp only [triggered, payload, oldPayload, Bool.false_eq_true] at selected
  | packet call outcome computed certificate => simp only [triggered, payload, Bool.false_eq_true] at selected
  | deliver capacity => simp only [triggered, payload, Bool.false_eq_true] at selected
  | idle => simp only [triggered, payload, Bool.false_eq_true] at selected

theorem triggered_revoked (actual : Step input budget) (selected : triggered actual = true) :
    CampusRevocationTargets.revoked input actual.effect.state.campus.authentication = true := by
  obtain ⟨source, found, kind, after⟩ := triggered_source actual selected
  have within : actual.before.campus.authentication < input.authentication.observations.length :=
    (List.getElem?_eq_some_iff.mp found).1
  have same : input.authentication.observations[actual.before.campus.authentication]'within = source :=
    (List.getElem?_eq_some_iff.mp found).2
  have current := current_succ input.authentication actual.before.campus.authentication within
  rw [same] at current
  rw [after]
  apply (CampusRevocationTargets.revoked_correct _ _).mpr
  rw [current]
  rcases kind with logoff | revoke | close
  · rw [logoff]; exact Or.inl rfl
  · rw [revoke]; exact Or.inr rfl
  · rw [close]; exact Or.inl rfl

def triggerAt (steps : List (Step input budget)) : Nat → Bool
  | 0 => false
  | slot + 1 => match steps[slot]? with
    | none => false
    | some actual => triggered actual

theorem triggerAt_selected (steps : List (Step input budget)) (cut : Nat)
    (selected : triggerAt steps cut = true) :
    ∃ slot actual, cut = slot + 1 ∧ steps[slot]? = some actual ∧ triggered actual = true := by
  cases cut with
  | zero => simp only [triggerAt, Bool.false_eq_true] at selected
  | succ slot =>
    cases found : steps[slot]? with
    | none => simp only [triggerAt, found, Bool.false_eq_true] at selected
    | some actual =>
      exact ⟨slot, actual, rfl, found, by simpa only [triggerAt, found] using selected⟩

theorem triggerAt_bounds (steps : List (Step input budget)) (cut : Nat)
    (selected : triggerAt steps cut = true) : 0 < cut ∧ cut ≤ steps.length := by
  obtain ⟨slot, actual, rfl, found, _⟩ := triggerAt_selected steps cut selected
  have within := (List.getElem?_eq_some_iff.mp found).1
  exact ⟨by omega, by omega⟩

theorem triggerAt_source {initial final : State} {steps : List (Step input budget)}
    (trace : Trace input budget initial steps final) (cut : Nat) (selected : triggerAt steps cut = true) :
    ∃ slot source, cut = slot + 1 ∧
      input.authentication.observations[(stateAt initial steps slot).campus.authentication]? = some source ∧
      (source.event = .authentication .logoff ∨ source.event = .application .revoke ∨ source.event = .close) ∧
      (stateAt initial steps cut).campus.authentication = (stateAt initial steps slot).campus.authentication + 1 := by
  obtain ⟨slot, actual, rfl, found, trigger⟩ := triggerAt_selected steps cut selected
  obtain ⟨source, sourceFound, kind, after⟩ := triggered_source actual trigger
  obtain ⟨before, _, current⟩ := trace.at_step found
  refine ⟨slot, source, rfl, ?_, kind, ?_⟩
  · rw [← before]
    exact sourceFound
  · rw [← current, ← before]
    exact after

theorem triggerAt_revoked {initial final : State} {steps : List (Step input budget)}
    (trace : Trace input budget initial steps final) (cut : Nat) (selected : triggerAt steps cut = true) :
    CampusRevocationTargets.revoked input (stateAt initial steps cut).campus.authentication = true := by
  obtain ⟨slot, actual, rfl, found, trigger⟩ := triggerAt_selected steps cut selected
  have after := (trace.at_step found).2.2
  rw [← after]
  exact triggered_revoked actual trigger

theorem run_triggerAt_revoked (execution : Run input budget initial events) (cut : Nat)
    (selected : triggerAt execution.steps cut = true) :
    CampusRevocationTargets.revoked input (stateAt initial execution.steps cut).campus.authentication = true :=
  triggerAt_revoked execution.trace cut selected

theorem report_triggerAt_revoked (report : Report input budget events) (cut : Nat)
    (selected : triggerAt report.steps cut = true) :
    CampusRevocationTargets.revoked input (stateAt input.initial report.steps cut).campus.authentication = true :=
  triggerAt_revoked report.trace cut selected

end Netlib.Check.CampusRevocationTrigger
