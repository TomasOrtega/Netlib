import Netlib.Packet.ACL

/-!
# Packet and conntrack-state rules

The state is supplied for the current packet at the selected filter stage.
It does not assert a transport handshake or policy authorization.
-/

namespace Netlib.Packet.StatefulACL

inductive CTState where
  | new
  | established
  | related
  | invalid
  | untracked
  deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq

structure Rule where
  test : Match
  states : Option (List CTState)
  action : Action
  deriving Repr, BEq, DecidableEq

abbrev Policy := List Rule

namespace Rule

def stateAccepts (rule : Rule) (state : CTState) : Bool :=
  match rule.states with
  | none => true
  | some states => states.contains state

def accepts (rule : Rule) (state : CTState) (header : Header) : Bool :=
  rule.test.accepts header && rule.stateAccepts state

def Matches (rule : Rule) (state : CTState) (header : Header) : Prop :=
  rule.test.Holds header ∧ match rule.states with
    | none => True
    | some states => state ∈ states

theorem stateAccepts_iff (rule : Rule) (state : CTState) :
    rule.stateAccepts state = true ↔ match rule.states with
      | none => True
      | some states => state ∈ states := by
  cases selected : rule.states <;> simp [stateAccepts, selected]

theorem accepts_iff (rule : Rule) (state : CTState) (header : Header) :
    rule.accepts state header = true ↔ rule.Matches state header := by
  simp only [accepts, Bool.and_eq_true, Match.accepts_iff, stateAccepts_iff, Matches]

@[simp] theorem accepts_none (test : Match) (action : Action) (state : CTState) (header : Header) :
    (⟨test, none, action⟩ : Rule).accepts state header = test.accepts header := by
  simp [accepts, stateAccepts]

@[simp] theorem accepts_empty (test : Match) (action : Action) (state : CTState) (header : Header) :
    (⟨test, some [], action⟩ : Rule).accepts state header = false := by
  simp [accepts, stateAccepts]

def ofRule (rule : Packet.Rule) : Rule := ⟨rule.test, none, rule.action⟩

def toRule (rule : Rule) : Packet.Rule := ⟨rule.test, rule.action⟩

theorem ofRule_toRule (rule : Rule) (unguarded : rule.states = none) :
    ofRule rule.toRule = rule := by
  cases rule
  cases unguarded
  rfl

def Refines (stronger weaker : Rule) : Prop :=
  ∀ state header, stronger.accepts state header = true → weaker.accepts state header = true

theorem refines_refl (rule : Rule) : rule.Refines rule := fun _ _ => id

theorem Refines.trans {first second third : Rule} (left : first.Refines second)
    (right : second.Refines third) : first.Refines third :=
  fun state header accepted => right state header (left state header accepted)

end Rule

namespace Policy

def lookup : Policy → CTState → Header → Option Action
  | [], _, _ => none
  | rule :: rules, state, header =>
    if rule.accepts state header then some rule.action else lookup rules state header

def evaluate (fallback : Action) (rules : Policy) (state : CTState) (header : Header) : Action :=
  (lookup rules state header).getD fallback

def allows (rules : Policy) (state : CTState) (header : Header) : Bool :=
  decide (evaluate .deny rules state header = .permit)

inductive FirstMatch : Policy → CTState → Header → Action → Prop
  | here (rule : Rule) (rules : Policy) (state : CTState) (header : Header)
      (acceptedMatch : rule.Matches state header) : FirstMatch (rule :: rules) state header rule.action
  | skip (rule : Rule) {rules : Policy} {state : CTState} {header : Header} {action : Action}
      (rejects : ¬rule.Matches state header) (next : FirstMatch rules state header action) :
      FirstMatch (rule :: rules) state header action

theorem lookup_eq_some_iff (rules : Policy) (state : CTState) (header : Header) (action : Action) :
    lookup rules state header = some action ↔ FirstMatch rules state header action := by
  induction rules with
  | nil => simp [lookup]; intro impossible; cases impossible
  | cons rule rules ih =>
    cases accepted : rule.accepts state header with
    | false =>
      have rejected : ¬rule.Matches state header := by
        rw [← Rule.accepts_iff, accepted]
        exact Bool.noConfusion
      simp only [lookup, accepted, Bool.false_eq_true, ite_false, ih]
      constructor
      · exact .skip rule rejected
      · intro first
        cases first with
        | here _ _ _ _ acceptedMatch => exact False.elim (rejected acceptedMatch)
        | skip _ _ next => exact next
    | true =>
      have acceptedMatch := (Rule.accepts_iff rule state header).mp accepted
      simp only [lookup, accepted, ite_true, Option.some.injEq]
      constructor
      · intro same; subst action; exact .here rule rules state header acceptedMatch
      · intro first
        cases first with
        | here => rfl
        | skip _ rejected _ => exact False.elim (rejected acceptedMatch)

theorem lookup_eq_none_iff (rules : Policy) (state : CTState) (header : Header) :
    lookup rules state header = none ↔ ∀ rule ∈ rules, ¬rule.Matches state header := by
  induction rules with
  | nil => simp [lookup]
  | cons rule rules ih =>
    cases accepted : rule.accepts state header <;>
      simp [lookup, accepted, ih, ← Rule.accepts_iff]

@[simp] theorem evaluate_nil (fallback : Action) (state : CTState) (header : Header) :
    evaluate fallback [] state header = fallback := rfl

@[simp] theorem allows_nil (state : CTState) (header : Header) :
    allows [] state header = false := rfl

theorem evaluate_eq_iff (fallback action : Action) (rules : Policy) (state : CTState) (header : Header) :
    evaluate fallback rules state header = action ↔
      FirstMatch rules state header action ∨
        (fallback = action ∧ ∀ rule ∈ rules, ¬rule.Matches state header) := by
  rw [← lookup_eq_some_iff, ← lookup_eq_none_iff]
  cases selected : lookup rules state header <;> simp [evaluate, selected]

theorem default_deny_iff (rules : Policy) (state : CTState) (header : Header) :
    allows rules state header = true ↔ FirstMatch rules state header .permit := by
  simp only [allows, decide_eq_true_eq, evaluate_eq_iff]
  simp

theorem default_permit_iff (rules : Policy) (state : CTState) (header : Header) :
    evaluate .permit rules state header = .permit ↔ ¬FirstMatch rules state header .deny := by
  rw [← lookup_eq_some_iff]
  cases selected : lookup rules state header with
  | none => simp [evaluate, selected]
  | some action => cases action <;> simp [evaluate, selected]

theorem evaluate_cons_accepts (fallback : Action) (rule : Rule) (rules : Policy)
    (state : CTState) (header : Header) (accepted : rule.accepts state header = true) :
    evaluate fallback (rule :: rules) state header = rule.action := by
  simp [evaluate, lookup, accepted]

theorem evaluate_cons_rejects (fallback : Action) (rule : Rule) (rules : Policy)
    (state : CTState) (header : Header) (rejected : rule.accepts state header = false) :
    evaluate fallback (rule :: rules) state header = evaluate fallback rules state header := by
  simp [evaluate, lookup, rejected]

theorem lookup_append (left right : Policy) (state : CTState) (header : Header) :
    lookup (left ++ right) state header =
      (lookup left state header).orElse (fun _ => lookup right state header) := by
  induction left with
  | nil => rfl
  | cons rule rules ih =>
    cases accepted : rule.accepts state header <;> simp [lookup, accepted, ih]

theorem evaluate_append (fallback : Action) (left right : Policy) (state : CTState) (header : Header) :
    evaluate fallback (left ++ right) state header =
      evaluate (evaluate fallback right state header) left state header := by
  simp only [evaluate, lookup_append]
  cases lookup left state header <;> rfl

theorem first_match_append {left : Policy} {state : CTState} {header : Header} {action : Action}
    (first : FirstMatch left state header action) (right : Policy) :
    FirstMatch (left ++ right) state header action := by
  induction first with
  | here rule rules state header acceptedMatch => exact .here rule (rules ++ right) state header acceptedMatch
  | skip rule rejected _ ih => exact .skip rule rejected ih

theorem shadowed_rule (first second : Rule) (rest : Policy) (covered : second.Refines first)
    (fallback : Action) (state : CTState) (header : Header) :
    evaluate fallback (first :: second :: rest) state header =
      evaluate fallback (first :: rest) state header := by
  cases firstAccepted : first.accepts state header with
  | true => simp [evaluate, lookup, firstAccepted]
  | false =>
    have secondRejected : second.accepts state header = false := by
      cases secondAccepted : second.accepts state header with
      | false => rfl
      | true => have := covered state header secondAccepted; simp_all
    simp [evaluate, lookup, firstAccepted, secondRejected]

def Refines (stronger weaker : Policy) : Prop :=
  ∀ state header, stronger.allows state header = true → weaker.allows state header = true

theorem refines_refl (rules : Policy) : rules.Refines rules := fun _ _ => id

theorem Refines.trans {first second third : Policy} (left : first.Refines second)
    (right : second.Refines third) : first.Refines third :=
  fun state header accepted => right state header (left state header accepted)

theorem prepend_deny_refines (test : Match) (states : Option (List CTState)) (rules : Policy) :
    Refines (⟨test, states, .deny⟩ :: rules) rules := by
  intro state header permitted
  cases accepted : (⟨test, states, .deny⟩ : Rule).accepts state header <;>
    simp_all [allows, evaluate, lookup]

def specialize (rules : Policy) (state : CTState) : ACL :=
  rules.filterMap fun rule => if rule.stateAccepts state then some rule.toRule else none

theorem lookup_specialize (rules : Policy) (state : CTState) (header : Header) :
    ACL.lookup (rules.specialize state) header = rules.lookup state header := by
  induction rules with
  | nil => rfl
  | cons rule rules ih =>
    simp only [specialize, Rule.toRule] at ih
    cases selected : rule.stateAccepts state <;>
      simp [specialize, selected, lookup, Rule.accepts, Rule.toRule, ACL.lookup, ih]

theorem evaluate_specialize (fallback : Action) (rules : Policy) (state : CTState) (header : Header) :
    ACL.evaluate fallback (rules.specialize state) header = rules.evaluate fallback state header := by
  simp [ACL.evaluate, evaluate, lookup_specialize]

theorem allows_specialize (rules : Policy) (state : CTState) (header : Header) :
    ACL.allows (rules.specialize state) header = rules.allows state header := by
  simp [ACL.allows, allows, evaluate_specialize]

theorem refines_iff_specialize (stronger weaker : Policy) :
    stronger.Refines weaker ↔ ∀ state, ACL.Refines (stronger.specialize state) (weaker.specialize state) := by
  simp only [Refines, ACL.Refines, allows_specialize]

def ofACL (rules : ACL) : Policy := rules.map Rule.ofRule

theorem lookup_ofACL (rules : ACL) (state : CTState) (header : Header) :
    lookup (ofACL rules) state header = ACL.lookup rules header := by
  induction rules with
  | nil => rfl
  | cons rule rules ih =>
    simp only [ofACL] at ih
    simp [ofACL, lookup, Rule.ofRule, ACL.lookup, ih]

theorem evaluate_ofACL (fallback : Action) (rules : ACL) (state : CTState) (header : Header) :
    evaluate fallback (ofACL rules) state header = ACL.evaluate fallback rules header := by
  simp [evaluate, ACL.evaluate, lookup_ofACL]

theorem allows_ofACL (rules : ACL) (state : CTState) (header : Header) :
    allows (ofACL rules) state header = ACL.allows rules header := by
  simp [allows, ACL.allows, evaluate_ofACL]

theorem evaluate_eq_of_unguarded (fallback : Action) (rules : Policy)
    (unguarded : ∀ rule ∈ rules, rule.states = none) (state : CTState) (header : Header) :
    evaluate fallback rules state header = ACL.evaluate fallback (rules.map Rule.toRule) header := by
  have same : ofACL (rules.map Rule.toRule) = rules := by
    induction rules with
    | nil => rfl
    | cons rule rules ih =>
      have selected := unguarded rule (by simp)
      have tail := ih (fun next member => unguarded next (by simp [member]))
      change Rule.ofRule rule.toRule :: ofACL (rules.map Rule.toRule) = rule :: rules
      rw [Rule.ofRule_toRule rule selected, tail]
  calc
    evaluate fallback rules state header = evaluate fallback (ofACL (rules.map Rule.toRule)) state header :=
      congrArg (fun policy => evaluate fallback policy state header) same.symm
    _ = _ := evaluate_ofACL _ _ _ _

end Policy
end Netlib.Packet.StatefulACL
