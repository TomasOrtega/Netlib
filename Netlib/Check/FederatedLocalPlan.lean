import Netlib.Check.DomainContractNative
import Netlib.Check.FederatedPlan

/-!
# Native certificates for complete local update plans

The aggregate work guard precedes native packet checking. Certificates retain
every declared revision in order, including the initial native snapshot.
-/

namespace Netlib.Federation.LocalPlan

def workEstimate (plan : Plan) : Nat :=
  (plan.versions.map (Native.workEstimate plan.contract)).sum

structure Checked (plan : Plan) where
  limits : Native.Limits
  named : ∀ revision ∈ plan.versions, revision.id ≠ ""
  unique : (plan.versions.map (·.id)).Nodup
  workWithin : workEstimate plan ≤ limits.work
  revisions : List ((revision : Revision) × Native.Checked plan.contract revision)
  covered : revisions.map Sigma.fst = plan.versions

private def verify (condition : Prop) [Decidable condition] (message : String) :
    Except String { _value : Unit // condition } :=
  if accepted : condition then .ok ⟨(), accepted⟩ else .error message

private def checkVersions (contract : Contract) (limits : Native.Limits) (index : Nat) :
    (versions : List Revision) →
    Except String { values : List ((revision : Revision) × Native.Checked contract revision) //
      values.map Sigma.fst = versions }
  | [] => return ⟨[], rfl⟩
  | revision :: rest => do
    let head ← (Native.check contract revision limits).mapError
      (fun reason => s!"Operator {contract.id}, revision {index} ({revision.id}): {reason}")
    let tail ← checkVersions contract limits (index + 1) rest
    return ⟨⟨revision, head⟩ :: tail.val, by simp only [List.map_cons, tail.property]⟩

def check (plan : Plan) (limits : Native.Limits := {}) : Except String (Checked plan) := do
  let named ← verify (plan.versions.all (fun revision => decide (revision.id ≠ "")) = true)
    s!"Operator {plan.contract.id}: a native revision identity is empty."
  let unique ← verify (plan.versions.map (·.id)).Nodup
    s!"Operator {plan.contract.id}: native revision identities must be unique across the complete plan."
  let work ← verify (workEstimate plan ≤ limits.work)
    s!"Operator {plan.contract.id}: complete plan work estimate {workEstimate plan} exceeds budget {limits.work}."
  let revisions ← checkVersions plan.contract limits 0 plan.versions
  return ⟨limits,
    (by simpa only [List.all_eq_true, decide_eq_true_eq] using named.property),
    unique.property, work.property, revisions.val, revisions.property⟩

variable {plan : Plan}

theorem Checked.length (value : Checked plan) : value.revisions.length = plan.versions.length := by
  simpa only [List.length_map] using congrArg List.length value.covered

def Checked.entry (value : Checked plan) (cursor : plan.Cursor) :
    (revision : Revision) × Native.Checked plan.contract revision :=
  value.revisions[cursor.val]'(by rw [value.length]; exact cursor.isLt)

theorem Checked.entry_mem (value : Checked plan) (cursor : plan.Cursor) :
    value.entry cursor ∈ value.revisions :=
  List.mem_of_getElem rfl

theorem Checked.entry_revision (value : Checked plan) (cursor : plan.Cursor) :
    (value.entry cursor).1 = plan.revisionAt cursor := by
  unfold Checked.entry Plan.revisionAt
  simp only [← value.covered, List.getElem_map]

def Checked.nativeAt (value : Checked plan) (cursor : plan.Cursor) :
    Native.Checked plan.contract (plan.revisionAt cursor) :=
  (value.entry_revision cursor) ▸ (value.entry cursor).2

private theorem transported_mem {contract : Contract}
    {values : List ((revision : Revision) × Native.Checked contract revision)}
    {revision target : Revision} (same : revision = target)
    (certificate : Native.Checked contract revision) (member : ⟨revision, certificate⟩ ∈ values) :
    ⟨target, same ▸ certificate⟩ ∈ values := by
  cases same
  exact member

theorem Checked.nativeAt_stored (value : Checked plan) (cursor : plan.Cursor) :
    ⟨plan.revisionAt cursor, value.nativeAt cursor⟩ ∈ value.revisions :=
  transported_mem (value.entry_revision cursor) (value.entry cursor).2 (value.entry_mem cursor)

theorem Checked.checked_all (value : Checked plan) :
    ∀ revision ∈ plan.versions, Nonempty (Native.Checked plan.contract revision) := by
  intro revision member
  rw [← value.covered] at member
  obtain ⟨⟨actual, certificate⟩, _, same⟩ := List.mem_map.mp member
  dsimp only at same
  subst actual
  exact ⟨certificate⟩

theorem Checked.provenance (value : Checked plan) (cursor : plan.Cursor)
    (selected : Case) (member : selected ∈ plan.contract.cases) (header : Packet.Header)
    (accepted : selected.selector.accepts header = true) (arc : Arc) (present : arc ∈ selected.must) :
    Nonempty (Native.Provenance (value.nativeAt cursor) selected header arc) :=
  (value.nativeAt cursor).provenance selected member header accepted arc present

variable {left right : Plan}

theorem all_checked (first : Checked left) (second : Checked right)
    {events : List (Protocol.Transition.ProductLabel left.Operation right.Operation)}
    {current : left.Cursor × right.Cursor}
    (trace : (Plan.interleaving left right).Trace (Plan.jointInitial left right) events current) :
    Nonempty (Native.Checked left.contract (left.revisionAt current.1)) ∧
      Nonempty (Native.Checked right.contract (right.revisionAt current.2)) :=
  Plan.all_checked _ _ first.checked_all second.checked_all trace

theorem prefix_checked (first : Checked left) (second : Checked right)
    {prior later : List (Protocol.Transition.ProductLabel left.Operation right.Operation)}
    {current : left.Cursor × right.Cursor}
    (trace : (Plan.interleaving left right).Trace (Plan.jointInitial left right) (prior ++ later) current) :
    ∃ middle, (Plan.interleaving left right).Trace (Plan.jointInitial left right) prior middle ∧
      (Plan.interleaving left right).Trace middle later current ∧
      Nonempty (Native.Checked left.contract (left.revisionAt middle.1)) ∧
      Nonempty (Native.Checked right.contract (right.revisionAt middle.2)) :=
  Plan.prefix_checked _ _ first.checked_all second.checked_all trace

end Netlib.Federation.LocalPlan
