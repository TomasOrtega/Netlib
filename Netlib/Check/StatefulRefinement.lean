import Netlib.Import.NftablesStateful
import Netlib.Packet.Partition

/-!
# Static refinement of stateful filter chains

Every state and packet context is checked. Hook and priority must agree.
This does not model update history, revocation, or existing-flow admission.
-/

namespace Netlib.Check.StatefulRefinement

open Packet
open Packet.StatefulACL (CTState)
open Netlib.Import

def states : List CTState := [.new, .established, .related, .invalid, .untracked]

theorem state_mem (state : CTState) : state ∈ states := by
  cases state <;> simp [states]

def Meaning (stronger weaker : NftablesStateful.Snapshot) : Prop :=
  ∀ state header, stronger.permits state header = true → weaker.permits state header = true

def rules (snapshot : NftablesStateful.Snapshot) (state : CTState) : ACL :=
  snapshot.compile.specialize state

theorem rules_allows (snapshot : NftablesStateful.Snapshot) (state : CTState) (header : Header) :
    (rules snapshot state).allows header = snapshot.permits state header := by
  rw [rules, StatefulACL.Policy.allows_specialize, NftablesStateful.Snapshot.compile_allows]

def check (stronger weaker : NftablesStateful.Snapshot) : Bool :=
  states.all fun state => Partition.checkACLRefines (rules stronger state) (rules weaker state)

theorem check_correct (stronger weaker : NftablesStateful.Snapshot) :
    check stronger weaker = true ↔ Meaning stronger weaker := by
  simp only [check, List.all_eq_true, Partition.checkACLRefines_iff, ACL.Refines, rules_allows]
  constructor
  · intro accepted state header allowed
    exact accepted state (state_mem state) header allowed
  · intro accepted state _ header allowed
    exact accepted state header allowed

def sameContext (stronger weaker : NftablesStateful.Snapshot) : Bool :=
  stronger.hook == weaker.hook && stronger.priority == weaker.priority

theorem sameContext_iff (stronger weaker : NftablesStateful.Snapshot) :
    sameContext stronger weaker = true ↔
      stronger.hook = weaker.hook ∧ stronger.priority = weaker.priority := by
  simp [sameContext]

def stateCellCount (stronger weaker : NftablesStateful.Snapshot) (state : CTState) : Nat :=
  (Partition.ofRulesAndRoutes [rules stronger state, rules weaker state]
    ([] : List (List (Routing.Entry Unit)))).cellCount

def cellCount (stronger weaker : NftablesStateful.Snapshot) : Nat :=
  (states.map (stateCellCount stronger weaker)).sum

def checkBudget (stronger weaker : NftablesStateful.Snapshot) (budget : Nat := 100000) : Except String Bool :=
  if sameContext stronger weaker then
    if cellCount stronger weaker ≤ budget then .ok (check stronger weaker)
    else .error "Stateful refinement exceeds the total state/header cell budget."
  else .error "Stateful refinement requires the same native hook and priority."

theorem checkBudget_correct (stronger weaker : NftablesStateful.Snapshot) (budget : Nat) (value : Bool)
    (completed : checkBudget stronger weaker budget = .ok value) :
    value = true ↔ Meaning stronger weaker := by
  unfold checkBudget at completed
  split at completed
  · split at completed
    · cases completed
      exact check_correct stronger weaker
    · cases completed
  · cases completed

structure Context where
  state : CTState
  header : Header
  deriving Repr, BEq, DecidableEq

private def firstCounterexample (stronger weaker : NftablesStateful.Snapshot) : List CTState → Option Context
  | [] => none
  | state :: remaining =>
    match Partition.aclCounterexample (rules stronger state) (rules weaker state) with
    | some header => some ⟨state, header⟩
    | none => firstCounterexample stronger weaker remaining

private theorem firstCounterexample_sound (stronger weaker : NftablesStateful.Snapshot)
    (remaining : List CTState) (context : Context)
    (found : firstCounterexample stronger weaker remaining = some context) :
    stronger.permits context.state context.header = true ∧ weaker.permits context.state context.header = false := by
  induction remaining with
  | nil => simp [firstCounterexample] at found
  | cons state remaining ih =>
    cases selected : Partition.aclCounterexample (rules stronger state) (rules weaker state) with
    | none => exact ih (by simpa [firstCounterexample, selected] using found)
    | some header =>
      have same : context = ⟨state, header⟩ := by
        simpa [firstCounterexample, selected] using found.symm
      subst context
      have result := Partition.aclCounterexample_sound _ _ _ selected
      simpa only [rules_allows] using result

private theorem firstCounterexample_none_iff (stronger weaker : NftablesStateful.Snapshot)
    (remaining : List CTState) :
    firstCounterexample stronger weaker remaining = none ↔
      remaining.all (fun state => Partition.checkACLRefines (rules stronger state) (rules weaker state)) = true := by
  induction remaining with
  | nil => simp [firstCounterexample]
  | cons state remaining ih =>
    have equivalent := (Partition.aclCounterexample_none_iff (rules stronger state) (rules weaker state)).trans
      (Partition.checkACLRefines_iff (rules stronger state) (rules weaker state)).symm
    cases selected : Partition.aclCounterexample (rules stronger state) (rules weaker state) with
    | none =>
      have accepted := equivalent.mp selected
      simp [firstCounterexample, selected, accepted, ih]
    | some header =>
      have rejected : Partition.checkACLRefines (rules stronger state) (rules weaker state) = false := by
        cases result : Partition.checkACLRefines (rules stronger state) (rules weaker state) with
        | false => rfl
        | true => have absent := equivalent.mpr result; simp [selected] at absent
      simp [firstCounterexample, selected, rejected]

def counterexample (stronger weaker : NftablesStateful.Snapshot) : Option Context :=
  firstCounterexample stronger weaker states

theorem counterexample_sound (stronger weaker : NftablesStateful.Snapshot) (context : Context)
    (found : counterexample stronger weaker = some context) :
    stronger.permits context.state context.header = true ∧ weaker.permits context.state context.header = false :=
  firstCounterexample_sound stronger weaker states context found

theorem counterexample_none_iff (stronger weaker : NftablesStateful.Snapshot) :
    counterexample stronger weaker = none ↔ Meaning stronger weaker :=
  (firstCounterexample_none_iff stronger weaker states).trans (check_correct stronger weaker)

end Netlib.Check.StatefulRefinement
