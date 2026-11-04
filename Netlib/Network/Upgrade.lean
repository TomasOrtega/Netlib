import Netlib.Protocol.Transition
import Netlib.Network.Architecture

namespace Netlib.Network.Upgrade

universe u v w

/-- Snapshots include both endpoints and every intermediate state. -/
def snapshots {State : Type u} {Command : Type v} (advance : State → Command → State) :
    State → List Command → List State
  | initial, [] => [initial]
  | initial, command :: commands => initial :: snapshots advance (advance initial command) commands

def Preserves {State : Type u} {Command : Type v} (advance : State → Command → State)
    (contract : State → Prop) (initial : State) (commands : List Command) : Prop :=
  ∀ state ∈ snapshots advance initial commands, contract state

theorem preserves_nil {State : Type u} {Command : Type v}
    (advance : State → Command → State) (contract : State → Prop) (initial : State) :
    Preserves advance contract initial [] ↔ contract initial := by
  simp [Preserves, snapshots]

theorem preserves_cons {State : Type u} {Command : Type v}
    (advance : State → Command → State) (contract : State → Prop)
    (initial : State) (command : Command) (commands : List Command) :
    Preserves advance contract initial (command :: commands) ↔
      contract initial ∧ Preserves advance contract (advance initial command) commands := by
  simp [Preserves, snapshots]

theorem initial_safe {State : Type u} {Command : Type v}
    {advance : State → Command → State} {contract : State → Prop}
    {initial : State} {commands : List Command}
    (safe : Preserves advance contract initial commands) : contract initial := by
  apply safe initial
  cases commands <;> simp [snapshots]

theorem final_mem {State : Type u} {Command : Type v}
    (advance : State → Command → State) (initial : State) (commands : List Command) :
    commands.foldl advance initial ∈ snapshots advance initial commands := by
  induction commands generalizing initial with
  | nil => simp [snapshots]
  | cons command commands ih =>
    exact List.mem_cons_of_mem _ (ih (advance initial command))

theorem final_safe {State : Type u} {Command : Type v}
    {advance : State → Command → State} {contract : State → Prop}
    {initial : State} {commands : List Command}
    (safe : Preserves advance contract initial commands) :
    contract (commands.foldl advance initial) := safe _ (final_mem _ _ _)

theorem preserves_append {State : Type u} {Command : Type v}
    (advance : State → Command → State) (contract : State → Prop)
    (initial : State) (first second : List Command) :
    Preserves advance contract initial (first ++ second) ↔
      Preserves advance contract initial first ∧
      Preserves advance contract (first.foldl advance initial) second := by
  induction first generalizing initial with
  | nil =>
    simp only [List.nil_append, List.foldl_nil, preserves_nil]
    exact ⟨fun safe => ⟨initial_safe safe, safe⟩, fun safe => safe.2⟩
  | cons command commands ih =>
    simp only [List.cons_append, List.foldl_cons, preserves_cons, ih]
    exact and_assoc.symm

theorem of_invariant {State : Type u} {Command : Type v}
    {advance : State → Command → State} {contract : State → Prop}
    (invariant : (Protocol.Transition.ofFunction advance).Invariant contract)
    (initial : State) (commands : List Command) (safe : contract initial) :
    Preserves advance contract initial commands := by
  induction commands generalizing initial with
  | nil => exact (preserves_nil _ _ _).mpr safe
  | cons command commands ih =>
    exact (preserves_cons _ _ _ _ _).mpr
      ⟨safe, ih (advance initial command) (invariant _ _ _ safe rfl)⟩

/-- Checking endpoints alone cannot establish this condition. -/
def check {State : Type u} {Command : Type v} (advance : State → Command → State)
    (observe : State → Bool) (initial : State) (commands : List Command) : Bool :=
  (snapshots advance initial commands).all observe

theorem check_correct {State : Type u} {Command : Type v}
    (advance : State → Command → State) (observe : State → Bool) (contract : State → Prop)
    (faithful : ∀ state, observe state = true ↔ contract state)
    (initial : State) (commands : List Command) :
    check advance observe initial commands = true ↔ Preserves advance contract initial commands := by
  simp only [check, List.all_eq_true, Preserves, faithful]

structure Plan {State : Type u} {Command : Type v} (advance : State → Command → State)
    (contract : State → Prop) (initial : State) (commands : List Command) : Type where
  safe : Preserves advance contract initial commands

namespace Plan

def append {State : Type u} {Command : Type v}
    {advance : State → Command → State} {contract : State → Prop}
    {initial : State} {first second : List Command}
    (left : Plan advance contract initial first)
    (right : Plan advance contract (first.foldl advance initial) second) :
    Plan advance contract initial (first ++ second) :=
  ⟨(preserves_append _ _ _ _ _).mpr ⟨left.safe, right.safe⟩⟩

theorem final_safe {State : Type u} {Command : Type v}
    {advance : State → Command → State} {contract : State → Prop}
    {initial : State} {commands : List Command}
    (plan : Plan advance contract initial commands) :
    contract (commands.foldl advance initial) := Upgrade.final_safe plan.safe

end Plan

/-- An accepted check carries the property for every snapshot. -/
def certify {State : Type u} {Command : Type v}
    (advance : State → Command → State) (observe : State → Bool) (contract : State → Prop)
    (faithful : ∀ state, observe state = true ↔ contract state)
    (initial : State) (commands : List Command) : Option (Plan advance contract initial commands) :=
  if accepted : check advance observe initial commands = true then
    some ⟨(check_correct _ _ _ faithful _ _).mp accepted⟩
  else none

theorem certify_isSome_iff {State : Type u} {Command : Type v}
    (advance : State → Command → State) (observe : State → Bool) (contract : State → Prop)
    (faithful : ∀ state, observe state = true ↔ contract state)
    (initial : State) (commands : List Command) :
    (certify advance observe contract faithful initial commands).isSome = true ↔
      Preserves advance contract initial commands := by
  unfold certify
  split
  next accepted => simp only [Option.isSome_some, true_iff]; exact (check_correct _ _ _ faithful _ _).mp accepted
  next rejected =>
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    exact fun safe => rejected ((check_correct _ _ _ faithful _ _).mpr safe)

/-- A projected plan transfers a contract through a commuting implementation. -/
theorem preserves_of_projection {State : Type u} {Abstract : Type w} {Command : Type v}
    (advance : State → Command → State) (abstractAdvance : Abstract → Command → Abstract)
    (project : State → Abstract)
    (commutes : ∀ state command, project (advance state command) = abstractAdvance (project state) command)
    (abstractContract : Abstract → Prop) (concreteContract : State → Prop)
    (transfer : ∀ state, abstractContract (project state) → concreteContract state)
    (initial : State) (commands : List Command)
    (safe : Preserves abstractAdvance abstractContract (project initial) commands) :
    Preserves advance concreteContract initial commands := by
  induction commands generalizing initial with
  | nil =>
    exact (preserves_nil _ _ _).mpr (transfer initial ((preserves_nil _ _ _).mp safe))
  | cons command commands ih =>
    obtain ⟨head, tail⟩ := (preserves_cons _ _ _ _ _).mp safe
    apply (preserves_cons advance concreteContract initial command commands).mpr
    refine ⟨transfer initial head, ih (advance initial command) ?_⟩
    simpa only [commutes] using tail

end Netlib.Network.Upgrade
