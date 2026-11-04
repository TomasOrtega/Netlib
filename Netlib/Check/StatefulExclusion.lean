import Netlib.Check.StatefulRefinement

/-!
# Exact exclusion at a late filter

The forbidden class describes output-stage headers, including prior translations.
Static exclusion does not establish capture completeness or kernel refinement.
-/

namespace Netlib.Check.StatefulExclusion

open Packet
open Packet.StatefulACL (CTState)
open Netlib.Import

def Blocks (snapshot : NftablesStateful.Snapshot) (forbidden : Match) : Prop :=
  ∀ state header, forbidden.Holds header → snapshot.evaluate state header = .deny

def states : List CTState := StatefulRefinement.states

theorem state_mem (state : CTState) : state ∈ states := StatefulRefinement.state_mem state

private def rules (snapshot : NftablesStateful.Snapshot) (state : CTState) : ACL :=
  StatefulRefinement.rules snapshot state

private theorem rules_allows (snapshot : NftablesStateful.Snapshot) (state : CTState) (header : Header) :
    (rules snapshot state).allows header = snapshot.permits state header :=
  StatefulRefinement.rules_allows snapshot state header

def partition (snapshot : NftablesStateful.Snapshot) (forbidden : Match) (state : CTState) : Partition :=
  Partition.ofRulesAndRoutes [rules snapshot state] ([] : List (List (Routing.Entry Unit))) [forbidden]

private def violation (snapshot : NftablesStateful.Snapshot) (forbidden : Match)
    (state : CTState) (header : Header) : Bool :=
  forbidden.accepts header && (rules snapshot state).allows header

private theorem violation_stable (snapshot : NftablesStateful.Snapshot) (forbidden : Match)
    (state : CTState) (header : Header) :
    violation snapshot forbidden state ((partition snapshot forbidden state).representative header) =
      violation snapshot forbidden state header := by
  have selected : forbidden ∈ (partition snapshot forbidden state).tests := by
    simp [partition, Partition.ofRulesAndRoutes]
  have ruleIncluded (rule : Packet.Rule) (member : rule ∈ rules snapshot state) :
      rule.test ∈ (partition snapshot forbidden state).tests :=
    Partition.rule_included _ _ [forbidden] _ (by simp) rule member
  simp only [violation, (partition snapshot forbidden state).match_stable forbidden selected header,
    (partition snapshot forbidden state).acl_allows_stable (rules snapshot state) ruleIncluded header]

private theorem permits_false_iff (snapshot : NftablesStateful.Snapshot) (state : CTState) (header : Header) :
    snapshot.permits state header = false ↔ snapshot.evaluate state header = .deny := by
  cases selected : snapshot.evaluate state header <;> simp [NftablesStateful.Snapshot.permits, selected]

private theorem no_violation_iff (snapshot : NftablesStateful.Snapshot) (forbidden : Match)
    (state : CTState) (header : Header) :
    (violation snapshot forbidden state header).not = true ↔
      forbidden.Holds header → snapshot.evaluate state header = .deny := by
  have boolean (left right : Bool) : (left && right).not = true ↔ left = true → right = false := by
    cases left <;> cases right <;> simp
  unfold violation
  rw [rules_allows, boolean, Match.accepts_iff, permits_false_iff]

def checkState (snapshot : NftablesStateful.Snapshot) (forbidden : Match) (state : CTState) : Bool :=
  (partition snapshot forbidden state).check fun header => !(violation snapshot forbidden state header)

theorem checkState_correct (snapshot : NftablesStateful.Snapshot) (forbidden : Match) (state : CTState) :
    checkState snapshot forbidden state = true ↔
      ∀ header, forbidden.Holds header → snapshot.evaluate state header = .deny := by
  have complete := (partition snapshot forbidden state).check_iff
    (fun header => !(violation snapshot forbidden state header))
    (fun header => congrArg Bool.not (violation_stable snapshot forbidden state header))
  exact complete.trans (forall_congr' fun header => no_violation_iff snapshot forbidden state header)

def check (snapshot : NftablesStateful.Snapshot) (forbidden : Match) : Bool :=
  states.all (checkState snapshot forbidden)

theorem check_correct (snapshot : NftablesStateful.Snapshot) (forbidden : Match) :
    check snapshot forbidden = true ↔ Blocks snapshot forbidden := by
  simp only [check, List.all_eq_true, checkState_correct]
  constructor
  · intro accepted state header selected
    exact accepted state (state_mem state) header selected
  · intro blocked state _ header selected
    exact blocked state header selected

def stateCellCount (snapshot : NftablesStateful.Snapshot) (forbidden : Match) (state : CTState) : Nat :=
  (partition snapshot forbidden state).cellCount

def cellCount (snapshot : NftablesStateful.Snapshot) (forbidden : Match) : Nat :=
  (states.map (stateCellCount snapshot forbidden)).sum

def nativeContext (snapshot : NftablesStateful.Snapshot) : Bool :=
  snapshot.hook == "postrouting" && decide (100 < snapshot.priority ∧ snapshot.priority < 2147483647)

theorem nativeContext_iff (snapshot : NftablesStateful.Snapshot) :
    nativeContext snapshot = true ↔
      snapshot.hook = "postrouting" ∧ 100 < snapshot.priority ∧ snapshot.priority < 2147483647 := by
  simp [nativeContext]

def checkBudget (snapshot : NftablesStateful.Snapshot) (forbidden : Match)
    (budget : Nat := 100000) : Except String Bool :=
  if nativeContext snapshot then
    if cellCount snapshot forbidden ≤ budget then .ok (check snapshot forbidden)
    else .error "Stateful exclusion exceeds the total state/header cell budget."
  else .error "A native exclusion barrier requires postrouting priority strictly between 100 and 2147483647."

theorem checkBudget_correct (snapshot : NftablesStateful.Snapshot) (forbidden : Match) (budget : Nat) (value : Bool)
    (completed : checkBudget snapshot forbidden budget = .ok value) :
    value = true ↔ Blocks snapshot forbidden := by
  unfold checkBudget at completed
  split at completed
  · split at completed
    · cases completed
      exact check_correct snapshot forbidden
    · cases completed
  · cases completed

theorem checkBudget_context (snapshot : NftablesStateful.Snapshot) (forbidden : Match) (budget : Nat) (value : Bool)
    (completed : checkBudget snapshot forbidden budget = .ok value) :
    snapshot.hook = "postrouting" ∧ 100 < snapshot.priority ∧ snapshot.priority < 2147483647 := by
  unfold checkBudget at completed
  split at completed
  · rename_i context
    exact (nativeContext_iff snapshot).mp context
  · cases completed

theorem blocks_of_checkBudget (snapshot : NftablesStateful.Snapshot) (forbidden : Match) (budget : Nat)
    (completed : checkBudget snapshot forbidden budget = .ok true) : Blocks snapshot forbidden :=
  (checkBudget_correct snapshot forbidden budget true completed).mp rfl

structure Context where
  state : CTState
  header : Header
  deriving Repr, BEq, DecidableEq

private def counterexampleState (snapshot : NftablesStateful.Snapshot) (forbidden : Match) (state : CTState) : Option Header :=
  (partition snapshot forbidden state).representatives.find? (violation snapshot forbidden state)

private theorem counterexampleState_sound (snapshot : NftablesStateful.Snapshot) (forbidden : Match)
    (state : CTState) (header : Header) (found : counterexampleState snapshot forbidden state = some header) :
    forbidden.Holds header ∧ snapshot.evaluate state header = .permit := by
  have selected : violation snapshot forbidden state header = true := List.find?_some found
  have selected : forbidden.accepts header = true ∧ (rules snapshot state).allows header = true :=
    Bool.and_eq_true_iff.mp selected
  rw [Match.accepts_iff, rules_allows] at selected
  simpa only [NftablesStateful.Snapshot.permits, decide_eq_true_eq] using selected

private theorem counterexampleState_none_iff (snapshot : NftablesStateful.Snapshot) (forbidden : Match) (state : CTState) :
    counterexampleState snapshot forbidden state = none ↔ checkState snapshot forbidden state = true := by
  simp [counterexampleState, checkState, Partition.check, List.find?_eq_none, List.all_eq_true]

private def firstCounterexample (snapshot : NftablesStateful.Snapshot) (forbidden : Match) : List CTState → Option Context
  | [] => none
  | state :: remaining =>
    match counterexampleState snapshot forbidden state with
    | some header => some ⟨state, header⟩
    | none => firstCounterexample snapshot forbidden remaining

private theorem firstCounterexample_sound (snapshot : NftablesStateful.Snapshot) (forbidden : Match)
    (remaining : List CTState) (context : Context) (found : firstCounterexample snapshot forbidden remaining = some context) :
    forbidden.Holds context.header ∧ snapshot.evaluate context.state context.header = .permit := by
  induction remaining with
  | nil => simp [firstCounterexample] at found
  | cons state remaining ih =>
    cases selected : counterexampleState snapshot forbidden state with
    | none => exact ih (by simpa [firstCounterexample, selected] using found)
    | some header =>
      have same : context = ⟨state, header⟩ := by simpa [firstCounterexample, selected] using found.symm
      subst context
      exact counterexampleState_sound snapshot forbidden state header selected

private theorem firstCounterexample_none_iff (snapshot : NftablesStateful.Snapshot) (forbidden : Match)
    (remaining : List CTState) : firstCounterexample snapshot forbidden remaining = none ↔
      remaining.all (checkState snapshot forbidden) = true := by
  induction remaining with
  | nil => simp [firstCounterexample]
  | cons state remaining ih =>
    cases selected : counterexampleState snapshot forbidden state with
    | none =>
      have accepted := (counterexampleState_none_iff snapshot forbidden state).mp selected
      simp [firstCounterexample, selected, accepted, ih]
    | some header =>
      have rejected : checkState snapshot forbidden state = false := by
        cases result : checkState snapshot forbidden state with
        | false => rfl
        | true =>
          have absent := (counterexampleState_none_iff snapshot forbidden state).mpr result
          simp [selected] at absent
      simp [firstCounterexample, selected, rejected]

def counterexample (snapshot : NftablesStateful.Snapshot) (forbidden : Match) : Option Context :=
  firstCounterexample snapshot forbidden states

theorem counterexample_sound (snapshot : NftablesStateful.Snapshot) (forbidden : Match) (context : Context)
    (found : counterexample snapshot forbidden = some context) :
    forbidden.Holds context.header ∧ snapshot.evaluate context.state context.header = .permit :=
  firstCounterexample_sound snapshot forbidden states context found

theorem counterexample_none_iff (snapshot : NftablesStateful.Snapshot) (forbidden : Match) :
    counterexample snapshot forbidden = none ↔ Blocks snapshot forbidden :=
  (firstCounterexample_none_iff snapshot forbidden states).trans (check_correct snapshot forbidden)

end Netlib.Check.StatefulExclusion
