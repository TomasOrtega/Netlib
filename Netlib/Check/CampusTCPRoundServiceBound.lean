import Netlib.Check.CampusTCPRoundMonitor

/-!
# Service bounds on stored round schedules

The check examines the demands and actions in evaluated slots.
It does not assume that a packet operation succeeds.
-/

namespace Netlib.Check.CampusTCPRoundServiceBound

open CampusTCPModel
namespace R
export CampusTCPRoundMonitor (Config Monitor Action nextAction monitorAt actionOf)
end R
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

variable {input : Input}

def pendingAt (config : R.Config) (initial : State input) (monitor : R.Monitor)
    (steps : List (Step input)) (slot : Nat) : Option R.Action :=
  R.nextAction config (S.stateAt initial steps slot) (R.monitorAt config monitor steps slot)

def Serviced (config : R.Config) (initial : State input) (monitor : R.Monitor)
    (steps : List (Step input)) (bound : Nat) : Prop :=
  ∀ start, start + bound ≤ steps.length → ∀ demand,
    pendingAt config initial monitor steps start = some demand →
    (∀ offset, offset < bound → pendingAt config initial monitor steps (start + offset) = some demand) →
    ∃ offset, offset < bound ∧ R.actionOf (S.eventAt steps (start + offset)) = some demand

def check (config : R.Config) (initial : State input) (monitor : R.Monitor)
    (steps : List (Step input)) (bound : Nat) : Bool :=
  (List.range (steps.length + 1)).all fun start =>
    if start + bound ≤ steps.length then
      match pendingAt config initial monitor steps start with
      | none => true
      | some demand =>
        if (List.range bound).all (fun offset => decide (pendingAt config initial monitor steps (start + offset) = some demand)) then
          (List.range bound).any (fun offset => decide (R.actionOf (S.eventAt steps (start + offset)) = some demand))
        else true
    else true

theorem check_correct (config : R.Config) (initial : State input) (monitor : R.Monitor)
    (steps : List (Step input)) (bound : Nat) :
    check config initial monitor steps bound = true ↔ Serviced config initial monitor steps bound := by
  constructor
  · intro checked start within demand pending persistent
    have member : start ∈ List.range (steps.length + 1) := List.mem_range.mpr (by omega)
    have selected := List.all_eq_true.mp checked start member
    have retained : (List.range bound).all (fun offset => decide
        (pendingAt config initial monitor steps (start + offset) = some demand)) = true := by
      apply List.all_eq_true.mpr
      intro offset inside
      exact decide_eq_true (persistent offset (List.mem_range.mp inside))
    simp only [within, ↓reduceIte, pending, retained] at selected
    obtain ⟨offset, inside, action⟩ := List.any_eq_true.mp selected
    exact ⟨offset, List.mem_range.mp inside, of_decide_eq_true action⟩
  · intro serviced
    apply List.all_eq_true.mpr
    intro start member
    by_cases within : start + bound ≤ steps.length
    · simp only [within, ↓reduceIte]
      cases pending : pendingAt config initial monitor steps start with
      | none => rfl
      | some demand =>
        simp only
        split
        · rename_i retained
          have persistent : ∀ offset, offset < bound →
              pendingAt config initial monitor steps (start + offset) = some demand := by
            intro offset inside
            exact of_decide_eq_true (List.all_eq_true.mp retained offset (List.mem_range.mpr inside))
          obtain ⟨offset, inside, action⟩ := serviced start within demand pending persistent
          exact List.any_eq_true.mpr ⟨offset, List.mem_range.mpr inside, decide_eq_true action⟩
        · rfl
    · simp only [within, ↓reduceIte]

theorem action_event (event : Event) (action : R.Action) (selected : R.actionOf event = some action) :
    event = action.event := by
  cases event <;> simp only [CampusTCPRoundMonitor.actionOf, reduceCtorEq, Option.some.injEq] at selected
  all_goals try cases selected
  all_goals try rfl
  rename_i ticket observed
  cases observed with
  | none =>
    simp only [Option.some.injEq] at selected
    cases selected
    rfl
  | some seen => cases selected

def allowed (config : R.Config) (before : State input) (monitor : R.Monitor) (event : Event) : Bool :=
  (match R.nextAction config before monitor with
    | none => false
    | some action => decide (R.actionOf event = some action)) || CampusTCPRoundMonitor.sameClock before event

theorem allowed_correct (config : R.Config) (before : State input) (monitor : R.Monitor) (event : Event) :
    allowed config before monitor event = true ↔ CampusTCPRoundMonitor.Allowed config before monitor event := by
  unfold allowed CampusTCPRoundMonitor.Allowed CampusTCPRoundMonitor.nextEvent
  cases selected : R.nextAction config before monitor with
  | none => simp only [Option.map_none, reduceCtorEq, false_or, Bool.false_or]
  | some action =>
    simp only [Option.map_some, Option.some.injEq, Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (served | clock)
      · exact .inl (action_event event action served).symm
      · exact .inr clock
    · rintro (served | clock)
      · rw [← served]
        exact .inl action.actionOf_event
      · exact .inr clock

def actions (config : R.Config) (initial : State input) (monitor : R.Monitor) (steps : List (Step input)) : Bool :=
  (List.range steps.length).all fun slot => allowed config (S.stateAt initial steps slot)
    (R.monitorAt config monitor steps slot) (S.eventAt steps slot)

theorem actions_correct (config : R.Config) (initial : State input) (monitor : R.Monitor) (steps : List (Step input)) :
    actions config initial monitor steps = true ↔
      ∀ slot, slot < steps.length → CampusTCPRoundMonitor.Allowed config (S.stateAt initial steps slot)
        (R.monitorAt config monitor steps slot) (S.eventAt steps slot) := by
  simp only [actions, List.all_eq_true, List.mem_range, allowed_correct]

end Netlib.Check.CampusTCPRoundServiceBound
