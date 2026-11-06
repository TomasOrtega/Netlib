import Netlib.Check.CampusTCPRoundPhaseBase

/-!
# Actual report identity and suffixes

The same initial state and event list determine the stored checked steps.
Suffix proofs use those steps without another model run.
-/

namespace Netlib.Check.CampusTCPRoundReport

open CampusTCPModel

variable {input : Input}

private theorem Trace.agree (first : Trace input initial events firstSteps firstFinal firstRemaining)
    (second : Trace input otherInitial otherEvents secondSteps secondFinal secondRemaining)
    (sameInitial : initial = otherInitial) (sameEvents : events = otherEvents) :
    firstSteps = secondSteps ∧ firstFinal = secondFinal ∧ firstRemaining = secondRemaining := by
  induction first generalizing otherInitial otherEvents secondSteps secondFinal secondRemaining with
  | done state =>
    cases second with
    | done other => exact ⟨rfl, sameInitial, rfl⟩
    | stop other blocked rest => cases sameEvents
    | next other supported rest => cases sameEvents
  | stop head stopped tail =>
    cases second with
    | done state => cases sameEvents
    | stop other blocked rest =>
      have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event head other sameInitial (List.cons.inj sameEvents).1
      subst other
      exact ⟨rfl, rfl, (List.cons.inj sameEvents).2⟩
    | next other supported rest =>
      have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event head other sameInitial (List.cons.inj sameEvents).1
      subst other
      simp only [stopped, Bool.false_eq_true] at supported
  | next head supported rest ih =>
    cases second with
    | done state => cases sameEvents
    | stop other blocked tail =>
      have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event head other sameInitial (List.cons.inj sameEvents).1
      subst other
      simp only [supported, Bool.true_eq_false] at blocked
    | next other accepted later =>
      have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event head other sameInitial (List.cons.inj sameEvents).1
      subst other
      obtain ⟨steps, final, remaining⟩ := ih later rfl (List.cons.inj sameEvents).2
      exact ⟨congrArg (head :: ·) steps, final, remaining⟩

theorem Trace.unique (first : Trace input initial events firstSteps firstFinal firstRemaining)
    (second : Trace input initial events secondSteps secondFinal secondRemaining) :
    firstSteps = secondSteps ∧ firstFinal = secondFinal ∧ firstRemaining = secondRemaining :=
  Trace.agree first second rfl rfl

theorem Trace.final_unique (first : Trace input initial events firstSteps firstFinal firstRemaining)
    (second : Trace input initial events secondSteps secondFinal secondRemaining) : firstFinal = secondFinal :=
  (Trace.unique first second).2.1

theorem Report.steps_unique (first second : Report input events) : first.steps = second.steps :=
  (Trace.unique first.trace second.trace).1

theorem Report.final_unique (first second : Report input events) : first.final = second.final :=
  Trace.final_unique first.trace second.trace

theorem Report.remaining_unique (first second : Report input events) : first.remaining = second.remaining :=
  (Trace.unique first.trace second.trace).2.2

theorem Report.unique (first second : Report input events) : first = second := by
  have final := Report.final_unique first second
  have steps := Report.steps_unique first second
  have remaining := Report.remaining_unique first second
  cases first
  cases second
  simp_all only

private theorem stateAt_append (state : State input) (prior later : List (Step input)) :
    CampusTCPSchedule.stateAt state (prior ++ later) prior.length =
      CampusTCPSchedule.stateAt state prior prior.length := by
  induction prior generalizing state with
  | nil => cases later <;> rfl
  | cons head tail ih => exact ih head.result.state

private theorem Trace.drop_complete (trace : Trace input initial events steps final remaining)
    (finished : remaining = []) (supported : ∀ actual ∈ steps, actual.result.supported = true)
    (count : Nat) (within : count ≤ steps.length) :
    Trace input (CampusTCPSchedule.stateAt initial steps count) ((steps.drop count).map (·.event))
      (steps.drop count) final [] := by
  induction trace generalizing count with
  | done state =>
    have zero : count = 0 := by simp only [List.length_nil] at within; omega
    subst count
    exact .done state
  | stop head blocked tail =>
    have accepted := supported head (by simp)
    simp only [blocked, Bool.false_eq_true] at accepted
  | next head accepted rest ih =>
    cases count with
    | zero =>
      have covered := (Trace.next head accepted rest).covered
      rw [finished, List.append_nil] at covered
      rw [List.drop_zero]
      have complete := Trace.next head accepted rest
      rw [finished] at complete
      simpa only [CampusTCPSchedule.stateAt_zero, covered] using complete
    | succ count =>
      have bound : count ≤ _ := Nat.le_of_succ_le_succ within
      simpa only [List.drop_succ_cons, CampusTCPSchedule.stateAt] using
        ih finished (fun actual member => supported actual (List.mem_cons_of_mem _ member)) count bound

theorem Trace.suffix (anchor : Trace input initial anchorEvents anchorSteps anchorFinal anchorRemaining)
    (current : Trace input initial currentEvents currentSteps currentFinal currentRemaining)
    (supported : ∀ actual ∈ currentSteps, actual.result.supported = true) (finished : currentRemaining = [])
    (steps : currentSteps = anchorSteps ++ extra) :
    Trace input anchorFinal (extra.map (·.event)) extra currentFinal [] := by
  have within : anchorSteps.length ≤ currentSteps.length := by rw [steps, List.length_append]; omega
  have trace := Trace.drop_complete current finished supported anchorSteps.length within
  have cut : CampusTCPSchedule.stateAt initial currentSteps anchorSteps.length = anchorFinal := by
    rw [steps, stateAt_append]
    exact CampusTCPSchedule.Trace.last_state anchor
  rw [cut, steps, List.drop_left] at trace
  exact trace

theorem Report.suffix (anchor : Report input anchorEvents) (current : Report input currentEvents)
    (supported : current.supported = true) (finished : current.remaining = [])
    (steps : current.steps = anchor.steps ++ extra) :
    Trace input anchor.final (extra.map (·.event)) extra current.final [] :=
  Trace.suffix anchor.trace current.trace (List.all_eq_true.mp supported) finished steps

end Netlib.Check.CampusTCPRoundReport
