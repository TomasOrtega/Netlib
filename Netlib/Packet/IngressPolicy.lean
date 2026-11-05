import Netlib.Packet.Partition

/-!
# Numeric ingress guards

An installed rule observes the current kernel interface index and packet header.
It cannot observe controller lifetime labels or authenticate a principal.
-/

namespace Netlib.Packet.IngressPolicy

structure Rule where
  ingress : Option Nat
  traffic : Match
  action : Action
  deriving Repr, DecidableEq

def Rule.interfaceMatches (rule : Rule) (index : Nat) : Bool :=
  match rule.ingress with
  | none => true
  | some selected => decide (index = selected)

def Rule.accepts (rule : Rule) (index : Nat) (header : Header) : Bool :=
  rule.interfaceMatches index && rule.traffic.accepts header

private def specializeRules : List Rule → Nat → ACL
  | [], _ => []
  | rule :: rules, index => if rule.interfaceMatches index then
      ⟨rule.traffic, rule.action⟩ :: specializeRules rules index else specializeRules rules index

structure Policy where
  rules : List Rule := []
  fallback : Action := .deny
  deriving Repr, DecidableEq

def Policy.specialize (policy : Policy) (index : Nat) : ACL :=
  specializeRules policy.rules index ++ [⟨{}, policy.fallback⟩]

def Policy.evaluate (policy : Policy) (index : Nat) (header : Header) : Action :=
  (policy.specialize index).evaluate .deny header

def Policy.allows (policy : Policy) (index : Nat) (header : Header) : Bool :=
  (policy.specialize index).allows header

theorem Policy.evaluate_nil (fallback : Action) (index : Nat) (header : Header) :
    (⟨[], fallback⟩ : Policy).evaluate index header = fallback := by
  simp [Policy.evaluate, Policy.specialize, specializeRules, ACL.evaluate, ACL.lookup, Match.accepts]

theorem Policy.evaluate_cons (rule : Rule) (rules : List Rule) (fallback : Action) (index : Nat) (header : Header) :
    (⟨rule :: rules, fallback⟩ : Policy).evaluate index header =
      if rule.accepts index header then rule.action else (⟨rules, fallback⟩ : Policy).evaluate index header := by
  cases selected : rule.interfaceMatches index <;> cases matched : rule.traffic.accepts header <;>
    simp [Policy.evaluate, Policy.specialize, specializeRules, selected, Rule.accepts,
      matched, ACL.evaluate, ACL.lookup]

def Policy.indices (policy : Policy) : List Nat := policy.rules.flatMap (fun rule => rule.ingress.toList)

private def fresh : List Nat → Nat
  | [] => 0
  | index :: indices => max (index + 1) (fresh indices)

private theorem member_lt_fresh (indices : List Nat) (index : Nat) (member : index ∈ indices) : index < fresh indices := by
  induction indices with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | inside
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (ih inside) (Nat.le_max_right _ _)

private def representative (indices : List Nat) (index : Nat) : Nat :=
  if index ∈ indices then index else fresh indices

private theorem interface_stable (rule : Rule) (indices : List Nat)
    (included : ∀ selected, rule.ingress = some selected → selected ∈ indices) (index : Nat) :
    rule.interfaceMatches (representative indices index) = rule.interfaceMatches index := by
  cases selected : rule.ingress with
  | none => simp [Rule.interfaceMatches, selected]
  | some value =>
    have member := included value selected
    by_cases present : index ∈ indices
    · simp [representative, present]
    · have different : index ≠ value := by intro same; exact present (same ▸ member)
      have freshDifferent : fresh indices ≠ value := Nat.ne_of_gt (member_lt_fresh indices value member)
      simp [Rule.interfaceMatches, selected, representative, present, different, freshDifferent]

private theorem specialize_stable (rules : List Rule) (indices : List Nat)
    (included : ∀ rule ∈ rules, ∀ selected, rule.ingress = some selected → selected ∈ indices) (index : Nat) :
    specializeRules rules (representative indices index) = specializeRules rules index := by
  induction rules with
  | nil => rfl
  | cons rule rules ih =>
    have same := interface_stable rule indices (included rule (by simp)) index
    have rest := ih (fun next member => included next (List.mem_cons_of_mem _ member))
    simp only [specializeRules, same, rest]

private theorem index_included (policy : Policy) (rule : Rule) (member : rule ∈ policy.rules)
    (selected : Nat) (found : rule.ingress = some selected) : selected ∈ policy.indices := by
  exact List.mem_flatMap.mpr ⟨rule, member, by simp [found]⟩

def interfaceRepresentatives (left right : Policy) : List Nat :=
  let indices := left.indices ++ right.indices
  (indices ++ [fresh indices]).eraseDups

private theorem representative_mem (left right : Policy) (index : Nat) :
    representative (left.indices ++ right.indices) index ∈ interfaceRepresentatives left right := by
  simp only [interfaceRepresentatives, List.mem_eraseDups]
  unfold representative
  split
  · exact List.mem_append_left _ ‹_›
  · exact List.mem_append_right _ (by simp)

private theorem policies_stable (left right : Policy) (index : Nat) :
    left.specialize (representative (left.indices ++ right.indices) index) = left.specialize index ∧
    right.specialize (representative (left.indices ++ right.indices) index) = right.specialize index := by
  constructor
  · exact congrArg (· ++ [⟨{}, left.fallback⟩]) (specialize_stable left.rules _
      (fun rule member selected found => List.mem_append_left _ (index_included left rule member selected found)) index)
  · exact congrArg (· ++ [⟨{}, right.fallback⟩]) (specialize_stable right.rules _
      (fun rule member selected found => List.mem_append_right _ (index_included right rule member selected found)) index)

def Equivalent (left right : Policy) : Prop := ∀ index header, left.allows index header = right.allows index header

def check (left right : Policy) : Bool :=
  (interfaceRepresentatives left right).all fun index =>
    Partition.checkACLRefines (left.specialize index) (right.specialize index) &&
      Partition.checkACLRefines (right.specialize index) (left.specialize index)

theorem check_correct (left right : Policy) : check left right = true ↔ Equivalent left right := by
  simp only [check, List.all_eq_true, Bool.and_eq_true, Partition.checkACLRefines_iff, ACL.Refines]
  constructor
  · intro checked index header
    have tested := checked _ (representative_mem left right index)
    obtain ⟨first, second⟩ := policies_stable left right index
    simp only [first, second] at tested
    exact Bool.eq_iff_iff.mpr ⟨tested.1 header, tested.2 header⟩
  · intro equivalent index _
    constructor
    · intro header permitted
      exact (equivalent index header).symm.trans permitted
    · intro header permitted
      exact (equivalent index header).trans permitted

def cellCount (left right : Policy) : Nat :=
  ((interfaceRepresentatives left right).map fun index =>
    let first := left.specialize index
    let second := right.specialize index
    (Partition.ofRulesAndRoutes [first, second] ([] : List (List (Routing.Entry Unit)))).cellCount * 2).sum

def checkBudget (left right : Policy) (budget : Nat := 100000) : Except String Bool :=
  if cellCount left right ≤ budget then .ok (check left right)
  else .error "Ingress equivalence exceeds the interface/header partition budget."

theorem checkBudget_correct (left right : Policy) (budget : Nat) (value : Bool)
    (accepted : checkBudget left right budget = .ok value) : value = true ↔ Equivalent left right := by
  unfold checkBudget at accepted
  split at accepted
  · have same := Except.ok.inj accepted
    rw [← same]
    exact check_correct left right
  · cases accepted

end Netlib.Packet.IngressPolicy
