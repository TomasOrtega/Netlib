import Netlib.Model.DomainContract
import Netlib.Network.Upgrade

/-!
# Independent finite native update plans

A cursor consumes only the next declared revision. Product traces cover every
interleaving, with exact local operation order and native revision provenance.
-/

namespace Netlib.Federation.Plan

open Protocol

abbrev Cursor (plan : Plan) := Fin plan.versions.length
abbrev Operation (plan : Plan) := Fin plan.updates.length

def revisionAt (plan : Plan) (cursor : plan.Cursor) : Revision := plan.versions[cursor.val]'cursor.isLt

def update (plan : Plan) (operation : plan.Operation) : Revision := plan.updates[operation.val]'operation.isLt

def initialCursor (plan : Plan) : plan.Cursor := ⟨0, by simp [Plan.versions]⟩

def transition (plan : Plan) : Transition plan.Cursor plan.Operation where
  step before operation after := operation.val = before.val ∧ after.val = before.val + 1

theorem at_mem (plan : Plan) (cursor : plan.Cursor) : plan.revisionAt cursor ∈ plan.versions := by
  apply List.mem_of_getElem?
  exact List.getElem?_eq_some_iff.mpr ⟨cursor.isLt, rfl⟩

@[simp] theorem at_initial (plan : Plan) : plan.revisionAt plan.initialCursor = plan.initial := rfl

theorem step_revision (plan : Plan) {before after : plan.Cursor} {operation : plan.Operation}
    (edge : plan.transition.step before operation after) : plan.revisionAt after = plan.update operation := by
  have next : after.val = operation.val + 1 := by have := edge.1; have := edge.2; omega
  have available := operation.isLt
  let nextCursor : plan.Cursor := ⟨operation.val + 1, by simp only [Plan.versions, List.length_cons]; omega⟩
  have same : after = nextCursor := Fin.ext next
  rw [same]
  rfl

theorem terminal_no_step (plan : Plan) (before after : plan.Cursor) (operation : plan.Operation)
    (terminal : before.val = plan.updates.length) : ¬plan.transition.step before operation after := by
  intro edge
  have available := operation.isLt
  have selected := edge.1
  omega

theorem next_step (plan : Plan) (before : plan.Cursor) (available : before.val < plan.updates.length) :
    ∃ operation after, plan.transition.step before operation after := by
  refine ⟨⟨before.val, available⟩, ⟨before.val + 1, ?_⟩, rfl, rfl⟩
  simp only [Plan.versions, List.length_cons]
  omega

theorem trace_count (plan : Plan) {before after : plan.Cursor} {events : List plan.Operation}
    (trace : plan.transition.Trace before events after) : after.val = before.val + events.length := by
  induction trace with
  | nil => simp
  | cons edge _ ih =>
    have next := edge.2
    simp only [List.length_cons]
    omega

theorem trace_order (plan : Plan) {before after : plan.Cursor} {events : List plan.Operation}
    (trace : plan.transition.Trace before events after) :
    events.map Fin.val = List.range' before.val events.length := by
  induction trace with
  | nil => rfl
  | cons edge _ ih =>
    simp only [List.map_cons, List.length_cons, List.range'_succ, ih, edge.1, edge.2]

private theorem replacement_snapshots {State : Type u} (initial : State) (updates : List State) :
    Network.Upgrade.snapshots (fun _ next => next) initial updates = initial :: updates := by
  induction updates generalizing initial with
  | nil => rfl
  | cons next rest ih => simp only [Network.Upgrade.snapshots, ih]

theorem checked_of_preserves (plan : Plan) (property : Revision → Prop)
    (checked : Network.Upgrade.Preserves (fun _ next => next) property plan.initial plan.updates) :
    ∀ revision ∈ plan.versions, property revision := by
  simpa only [Network.Upgrade.Preserves, replacement_snapshots, Plan.versions] using checked

theorem checked_invariant (plan : Plan) (property : Revision → Prop)
    (checked : ∀ revision ∈ plan.versions, property revision) :
    plan.transition.Invariant (fun cursor => property (plan.revisionAt cursor)) := by
  intro _ _ after _ _
  exact checked _ (plan.at_mem after)

def interleaving (left right : Plan) :
    Transition (left.Cursor × right.Cursor) (Transition.ProductLabel left.Operation right.Operation) :=
  Transition.product left.transition right.transition

def jointInitial (left right : Plan) : left.Cursor × right.Cursor := (left.initialCursor, right.initialCursor)

def leftProjection (left right : Plan) : TraceRefinement (interleaving left right) left.transition where
  project := Prod.fst
  labels
    | .left operation => [operation]
    | .right _ => []
    | .both operation _ => [operation]
  simulate before event after edge := by
    cases event with
    | left operation => exact .cons edge.1 (.nil _)
    | right operation => rw [edge.1]; exact .nil _
    | both operation peer => exact .cons edge.1 (.nil _)

def rightProjection (left right : Plan) : TraceRefinement (interleaving left right) right.transition where
  project := Prod.snd
  labels
    | .left _ => []
    | .right operation => [operation]
    | .both _ operation => [operation]
  simulate before event after edge := by
    cases event with
    | left operation => rw [edge.2]; exact .nil _
    | right operation => exact .cons edge.2 (.nil _)
    | both peer operation => exact .cons edge.2 (.nil _)

def leftEvents (left right : Plan) (events : List (Transition.ProductLabel left.Operation right.Operation)) :
    List left.Operation := events.flatMap (leftProjection left right).labels

def rightEvents (left right : Plan) (events : List (Transition.ProductLabel left.Operation right.Operation)) :
    List right.Operation := events.flatMap (rightProjection left right).labels

variable {left right : Plan} {events : List (Transition.ProductLabel left.Operation right.Operation)}
variable {current : left.Cursor × right.Cursor}

theorem local_traces (trace : (interleaving left right).Trace (jointInitial left right) events current) :
    left.transition.Trace left.initialCursor (leftEvents left right events) current.1 ∧
      right.transition.Trace right.initialCursor (rightEvents left right events) current.2 :=
  ⟨(leftProjection left right).trace trace, (rightProjection left right).trace trace⟩

theorem interleaving_counts (trace : (interleaving left right).Trace (jointInitial left right) events current) :
    current.1.val = (leftEvents left right events).length ∧
      current.2.val = (rightEvents left right events).length := by
  have first := left.trace_count (local_traces trace).1
  have second := right.trace_count (local_traces trace).2
  simpa only [initialCursor, Nat.zero_add] using And.intro first second

theorem interleaving_order (trace : (interleaving left right).Trace (jointInitial left right) events current) :
    (leftEvents left right events).map Fin.val = List.range' 0 current.1.val ∧
      (rightEvents left right events).map Fin.val = List.range' 0 current.2.val := by
  have first := left.trace_order (local_traces trace).1
  have second := right.trace_order (local_traces trace).2
  rw [← (interleaving_counts trace).1] at first
  rw [← (interleaving_counts trace).2] at second
  exact ⟨first, second⟩

theorem all_checked (leftProperty rightProperty : Revision → Prop)
    (leftChecked : ∀ revision ∈ left.versions, leftProperty revision)
    (rightChecked : ∀ revision ∈ right.versions, rightProperty revision)
    (trace : (interleaving left right).Trace (jointInitial left right) events current) :
    leftProperty (left.revisionAt current.1) ∧ rightProperty (right.revisionAt current.2) := by
  have invariant := Transition.invariant_product (left.checked_invariant leftProperty leftChecked)
    (right.checked_invariant rightProperty rightChecked)
  apply invariant.trace _ trace
  change leftProperty (left.revisionAt left.initialCursor) ∧ rightProperty (right.revisionAt right.initialCursor)
  rw [at_initial, at_initial]
  exact ⟨leftChecked _ (by simp [Plan.versions]), rightChecked _ (by simp [Plan.versions])⟩

theorem prefix_checked (leftProperty rightProperty : Revision → Prop)
    (leftChecked : ∀ revision ∈ left.versions, leftProperty revision)
    (rightChecked : ∀ revision ∈ right.versions, rightProperty revision)
    {prior later : List (Transition.ProductLabel left.Operation right.Operation)}
    (trace : (interleaving left right).Trace (jointInitial left right) (prior ++ later) current) :
    ∃ middle, (interleaving left right).Trace (jointInitial left right) prior middle ∧
      (interleaving left right).Trace middle later current ∧
      leftProperty (left.revisionAt middle.1) ∧ rightProperty (right.revisionAt middle.2) := by
  obtain ⟨middle, first, rest⟩ := trace.split
  exact ⟨middle, first, rest, all_checked leftProperty rightProperty leftChecked rightChecked first⟩

theorem left_step {before after : left.Cursor × right.Cursor} {operation : left.Operation}
    (edge : (interleaving left right).step before (.left operation) after) :
    operation.val = before.1.val ∧ after.1.val = before.1.val + 1 ∧
      left.revisionAt after.1 = left.update operation ∧ after.2 = before.2 :=
  ⟨edge.1.1, edge.1.2, left.step_revision edge.1, edge.2⟩

theorem right_step {before after : left.Cursor × right.Cursor} {operation : right.Operation}
    (edge : (interleaving left right).step before (.right operation) after) :
    operation.val = before.2.val ∧ after.2.val = before.2.val + 1 ∧
      right.revisionAt after.2 = right.update operation ∧ after.1 = before.1 :=
  ⟨edge.2.1, edge.2.2, right.step_revision edge.2, edge.1⟩


theorem both_step {before after : left.Cursor × right.Cursor}
    {first : left.Operation} {second : right.Operation}
    (edge : (interleaving left right).step before (.both first second) after) :
    first.val = before.1.val ∧ second.val = before.2.val ∧
      after.1.val = before.1.val + 1 ∧ after.2.val = before.2.val + 1 ∧
      left.revisionAt after.1 = left.update first ∧ right.revisionAt after.2 = right.update second :=
  ⟨edge.1.1, edge.2.1, edge.1.2, edge.2.2, left.step_revision edge.1, right.step_revision edge.2⟩

theorem interleaving_limits (trace : (interleaving left right).Trace (jointInitial left right) events current) :
    (leftEvents left right events).length ≤ left.updates.length ∧
      (rightEvents left right events).length ≤ right.updates.length := by
  have first := current.1.isLt
  have second := current.2.isLt
  simp only [Plan.versions, List.length_cons] at first second
  rw [← (interleaving_counts trace).1, ← (interleaving_counts trace).2]
  omega

theorem both_linearizes {before after : left.Cursor × right.Cursor}
    {first : left.Operation} {second : right.Operation}
    (edge : (interleaving left right).step before (.both first second) after) :
    (interleaving left right).Trace before [.left first, .right second] after ∧
      (interleaving left right).Trace before [.right second, .left first] after := by
  constructor
  · exact .cons (middle := (after.1, before.2)) ⟨edge.1, rfl⟩ (.cons (middle := after) ⟨rfl, edge.2⟩ (.nil after))
  · exact .cons (middle := (before.1, after.2)) ⟨rfl, edge.2⟩ (.cons (middle := after) ⟨edge.1, rfl⟩ (.nil after))

end Netlib.Federation.Plan
