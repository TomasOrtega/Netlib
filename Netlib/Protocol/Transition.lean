import Netlib.Protocol.Session

namespace Netlib.Protocol

universe u v w x y z

/-- An event labels each permitted state change. -/
structure Transition (State : Type u) (Label : Type v) where
  step : State → Label → State → Prop

namespace Transition

variable {State : Type u} {Label : Type v}

inductive Trace (system : Transition State Label) : State → List Label → State → Prop
  | nil (state) : Trace system state [] state
  | cons {before middle after label labels} :
      system.step before label middle → Trace system middle labels after →
      Trace system before (label :: labels) after

namespace Trace

variable {system : Transition State Label}

theorem append {before middle after : State} {left right : List Label}
    (first : system.Trace before left middle) (second : system.Trace middle right after) :
    system.Trace before (left ++ right) after := by
  induction first with
  | nil => exact second
  | cons edge _ ih => exact .cons edge (ih second)

theorem split {before after : State} {left right : List Label}
    (trace : system.Trace before (left ++ right) after) :
    ∃ middle, system.Trace before left middle ∧ system.Trace middle right after := by
  induction left generalizing before with
  | nil => exact ⟨before, .nil before, trace⟩
  | cons label labels ih =>
    cases trace with
    | cons edge tail =>
      obtain ⟨middle, first, second⟩ := ih tail
      exact ⟨middle, .cons edge first, second⟩

end Trace

def Invariant (system : Transition State Label) (property : State → Prop) : Prop :=
  ∀ before label after, property before → system.step before label after → property after

theorem Invariant.trace {system : Transition State Label} {property : State → Prop}
    (preserved : system.Invariant property) {before after : State} {labels : List Label}
    (initial : property before) (trace : system.Trace before labels after) : property after := by
  induction trace with
  | nil => exact initial
  | cons edge _ ih => exact ih (preserved _ _ _ initial edge)

/-- Every prefix, including the initial state, satisfies the invariant. -/
theorem Invariant.intermediate {system : Transition State Label} {property : State → Prop}
    (preserved : system.Invariant property) {before middle after : State}
    {firstLabels suffix : List Label} (initial : property before)
    (first : system.Trace before firstLabels middle)
    (_whole : system.Trace middle suffix after) : property middle :=
  preserved.trace initial first

def ofFunction (advance : State → Label → State) : Transition State Label :=
  ⟨fun before label after => advance before label = after⟩

theorem function_trace (advance : State → Label → State) (state : State)
    (labels : List Label) :
    (ofFunction advance).Trace state labels (labels.foldl advance state) := by
  induction labels generalizing state with
  | nil => exact .nil state
  | cons label labels ih => exact .cons rfl (ih (advance state label))

theorem function_trace_unique (advance : State → Label → State)
    {before after : State} {labels : List Label}
    (trace : (ofFunction advance).Trace before labels after) :
    after = labels.foldl advance before := by
  induction trace with
  | nil => rfl
  | cons edge _ ih =>
    change advance _ _ = _ at edge
    simpa only [List.foldl_cons, edge] using ih

/-- Independent events interleave; joint events change both states. -/
inductive ProductLabel (Left : Type v) (Right : Type x) where
  | left (label : Left)
  | right (label : Right)
  | both (left : Left) (right : Right)
  deriving Repr, DecidableEq

def product {Other : Type w} {OtherLabel : Type x}
    (left : Transition State Label) (right : Transition Other OtherLabel) :
    Transition (State × Other) (ProductLabel Label OtherLabel) where
  step before label after := match label with
    | .left event => left.step before.1 event after.1 ∧ after.2 = before.2
    | .right event => after.1 = before.1 ∧ right.step before.2 event after.2
    | .both a b => left.step before.1 a after.1 ∧ right.step before.2 b after.2

theorem invariant_product {Other : Type w} {OtherLabel : Type x}
    {left : Transition State Label} {right : Transition Other OtherLabel}
    {leftProperty : State → Prop} {rightProperty : Other → Prop}
    (leftSafe : left.Invariant leftProperty) (rightSafe : right.Invariant rightProperty) :
    (product left right).Invariant (fun state => leftProperty state.1 ∧ rightProperty state.2) := by
  intro before label after safe edge
  cases label with
  | left event => exact ⟨leftSafe _ _ _ safe.1 edge.1, edge.2 ▸ safe.2⟩
  | right event => exact ⟨edge.1 ▸ safe.1, rightSafe _ _ _ safe.2 edge.2⟩
  | both a b => exact ⟨leftSafe _ _ _ safe.1 edge.1, rightSafe _ _ _ safe.2 edge.2⟩

end Transition

/-- Each concrete step denotes a finite abstract trace, possibly empty. -/
structure TraceRefinement {Concrete : Type u} {Abstract : Type w}
    {ConcreteLabel : Type v} {AbstractLabel : Type x}
    (concrete : Transition Concrete ConcreteLabel) (abstract : Transition Abstract AbstractLabel) where
  project : Concrete → Abstract
  labels : ConcreteLabel → List AbstractLabel
  simulate : ∀ before label after, concrete.step before label after →
    abstract.Trace (project before) (labels label) (project after)

namespace TraceRefinement

variable {Concrete : Type u} {Abstract : Type w}
variable {ConcreteLabel : Type v} {AbstractLabel : Type x}
variable {concrete : Transition Concrete ConcreteLabel} {abstract : Transition Abstract AbstractLabel}

theorem trace (refinement : TraceRefinement concrete abstract)
    {before after : Concrete} {events : List ConcreteLabel}
    (execution : concrete.Trace before events after) :
    abstract.Trace (refinement.project before) (events.flatMap refinement.labels)
      (refinement.project after) := by
  induction execution with
  | nil => exact .nil _
  | cons edge _ ih => exact (refinement.simulate _ _ _ edge).append ih

def identity (system : Transition Concrete ConcreteLabel) : TraceRefinement system system where
  project := id
  labels event := [event]
  simulate _ _ after edge := .cons edge (.nil after)

def comp {Higher : Type y} {HigherLabel : Type z}
    {higher : Transition Higher HigherLabel}
    (lower : TraceRefinement concrete abstract) (upper : TraceRefinement abstract higher) :
    TraceRefinement concrete higher where
  project := upper.project ∘ lower.project
  labels event := (lower.labels event).flatMap upper.labels
  simulate _ _ _ edge := upper.trace (lower.simulate _ _ _ edge)

/-- Safety transfers along executions without assuming termination or progress. -/
theorem safe {property : Abstract → Prop} (refinement : TraceRefinement concrete abstract)
    (preserved : abstract.Invariant property)
    {before after : Concrete} {events : List ConcreteLabel}
    (initial : property (refinement.project before))
    (execution : concrete.Trace before events after) : property (refinement.project after) :=
  preserved.trace initial (refinement.trace execution)

theorem invariant {property : Abstract → Prop} (refinement : TraceRefinement concrete abstract)
    (preserved : abstract.Invariant property) :
    concrete.Invariant (property ∘ refinement.project) := by
  intro before event after initial edge
  exact preserved.trace initial (refinement.simulate before event after edge)

end TraceRefinement

namespace Session

def transition (context : Context) : Transition Session Event :=
  Transition.ofFunction (step context)

theorem transition_safe (context : Context) :
    (transition context).Invariant (Safe context) := by
  intro before event after _ edge
  change step context before event = after at edge
  subst after
  exact step_safe context before event

theorem transition_run (context : Context) (initial : Session) (events : List Event) :
    (transition context).Trace initial events (run context initial events) :=
  Transition.function_trace _ _ _

end Session
end Netlib.Protocol
