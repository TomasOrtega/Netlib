import Netlib.Check.CampusTCPSchedule

/-!
# Recorded authentication cuts for TCP revocation

The selected TCP step consumes the next authentication observation.
The observation determines the revoked state at that same cut.
-/

namespace Netlib.Check.CampusTCPRevocationTrigger

open Protocol
open CampusTCPModel

variable {input : Input}

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

def revoked (input : Input) (after : Nat) : Bool :=
  !(SessionInstallation.current input.context.authentication after).auth.authorized ||
    (SessionInstallation.current input.context.authentication after).session.credential.isNone

theorem revoked_correct (input : Input) (after : Nat) :
    revoked input after = true ↔
      (SessionInstallation.current input.context.authentication after).auth.authorized = false ∨
      (SessionInstallation.current input.context.authentication after).session.credential = none := by
  simp [revoked]

def triggered (actual : Step input) : Bool :=
  match actual.event with
  | .authentication index =>
    match input.context.authentication.observations[index]? with
    | none => false
    | some source => triggerEvent source.event
  | _ => false

theorem Step.authentication_source (actual : Step input) (index : Nat)
    (selected : actual.event = CampusTCPModel.Event.authentication index) :
    index = actual.before.authentication ∧
      index < input.context.authentication.observations.length ∧
      actual.result.state.authentication = index + 1 := by
  obtain ⟨effect, custody, evaluated, result⟩ := actual.processed
  rw [selected] at evaluated
  simp only [processCore] at evaluated
  split at evaluated
  · cases evaluated
  · rename_i same
    split at evaluated
    · rename_i available
      cases evaluated
      rw [result]
      exact ⟨by omega, by omega, by dsimp; omega⟩
    · cases evaluated

theorem triggered_source (actual : Step input) (selected : triggered actual = true) :
    ∃ index source, actual.event = CampusTCPModel.Event.authentication index ∧
      index = actual.before.authentication ∧
      input.context.authentication.observations[index]? = some source ∧
      (source.event = .authentication .logoff ∨ source.event = .application .revoke ∨ source.event = .close) ∧
      actual.result.state.authentication = index + 1 := by
  cases event : actual.event <;> simp only [triggered, event, Bool.false_eq_true] at selected
  rename_i index
  cases found : input.context.authentication.observations[index]? with
  | none => simp only [found, Bool.false_eq_true] at selected
  | some source =>
    have fields := Step.authentication_source actual index event
    exact ⟨index, source, rfl, fields.1, found,
      (triggerEvent_correct _).mp (by simpa only [found] using selected), fields.2.2⟩

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

theorem triggered_revoked (actual : Step input) (selected : triggered actual = true) :
    revoked input actual.result.state.authentication = true := by
  obtain ⟨index, source, event, _, found, kind, after⟩ := triggered_source actual selected
  have within := (List.getElem?_eq_some_iff.mp found).1
  have same : input.context.authentication.observations[index]'within = source :=
    (List.getElem?_eq_some_iff.mp found).2
  have current := current_succ input.context.authentication index within
  rw [same] at current
  rw [after]
  apply (revoked_correct input (index + 1)).mpr
  rw [current]
  rcases kind with logoff | revoke | close
  · rw [logoff]; exact Or.inl rfl
  · rw [revoke]; exact Or.inr rfl
  · rw [close]; exact Or.inl rfl

def triggerAt (steps : List (Step input)) : Nat → Bool
  | 0 => false
  | slot + 1 => match steps[slot]? with
    | none => false
    | some actual => triggered actual

theorem triggerAt_selected (steps : List (Step input)) (cut : Nat)
    (selected : triggerAt steps cut = true) :
    ∃ slot actual, cut = slot + 1 ∧ steps[slot]? = some actual ∧ triggered actual = true := by
  cases cut with
  | zero => simp only [triggerAt, Bool.false_eq_true] at selected
  | succ slot =>
    cases found : steps[slot]? with
    | none => simp only [triggerAt, found, Bool.false_eq_true] at selected
    | some actual => exact ⟨slot, actual, rfl, found, by simpa only [triggerAt, found] using selected⟩

theorem triggerAt_bounds (steps : List (Step input)) (cut : Nat)
    (selected : triggerAt steps cut = true) : 0 < cut ∧ cut ≤ steps.length := by
  obtain ⟨slot, actual, rfl, found, _⟩ := triggerAt_selected steps cut selected
  have within := (List.getElem?_eq_some_iff.mp found).1
  exact ⟨by omega, by omega⟩

theorem report_triggerAt_revoked (report : Report input events) (cut : Nat)
    (selected : triggerAt report.steps cut = true) :
    revoked input (CampusTCPSchedule.stateAt input.initial report.steps cut).authentication = true := by
  obtain ⟨slot, actual, rfl, found, selected⟩ := triggerAt_selected report.steps cut selected
  have within := (List.getElem?_eq_some_iff.mp found).1
  obtain ⟨head, same, _, _, after⟩ := CampusTCPSchedule.Trace.at report.trace slot within
  have equal : head = actual := Option.some.inj (same.symm.trans found)
  rw [← after, equal]
  exact triggered_revoked actual selected

end Netlib.Check.CampusTCPRevocationTrigger
