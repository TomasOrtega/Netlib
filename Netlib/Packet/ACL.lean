import Netlib.Packet.Basic
import Netlib.Network.Basic

/-!
# Access control lists

An access control list checks rules in order.
The first matching rule supplies an action.
A link policy can remove packet paths from a network.
-/

namespace Netlib.Packet

/-- A rule permits or denies a packet. -/
inductive Action where
  | permit
  | deny
  deriving Repr, BEq, DecidableEq

/-- A rule has a packet match and an action. -/
structure Rule where
  test : Match
  action : Action
  deriving Repr, BEq, DecidableEq

/-- An access control list checks its rules in order. -/
abbrev ACL := List Rule

namespace ACL

/-- The first rule that accepts the header supplies the action. -/
def lookup : ACL → Header → Option Action
  | [], _ => none
  | rule :: rules, header =>
    if rule.test.accepts header then some rule.action else lookup rules header

/-- The default action applies when no rule accepts the header. -/
def evaluate (default : Action) (rules : ACL) (header : Header) : Action :=
  (lookup rules header).getD default

/-- The standard policy denies packets that have no matching rule. -/
def allows (rules : ACL) (header : Header) : Bool :=
  decide (evaluate .deny rules header = .permit)

/-- This relation records the first rule that accepts a header. -/
inductive FirstMatch : ACL → Header → Action → Prop
  | here (rule : Rule) (rules : ACL) (header : Header)
      (accepts : rule.test.accepts header = true) :
      FirstMatch (rule :: rules) header rule.action
  | skip (rule : Rule) {rules : ACL} {header : Header} {action : Action}
      (rejects : rule.test.accepts header = false) (next : FirstMatch rules header action) :
      FirstMatch (rule :: rules) header action

theorem lookup_eq_some_iff (rules : ACL) (header : Header) (action : Action) :
    lookup rules header = some action ↔ FirstMatch rules header action := by
  induction rules with
  | nil => simp [lookup]; intro h; cases h
  | cons rule rules ih =>
    cases accepts : rule.test.accepts header with
    | false =>
      simp only [lookup, accepts, Bool.false_eq_true, ite_false, ih]
      constructor
      · exact .skip rule accepts
      · intro first
        cases first with
        | here _ _ _ impossible => simp_all
        | skip _ _ tail => exact tail
    | true =>
      simp only [lookup, accepts, ite_true, Option.some.injEq]
      constructor
      · intro same; subst action; exact .here rule rules header accepts
      · intro first
        cases first with
        | here => rfl
        | skip _ impossible _ => simp_all

theorem lookup_eq_none_iff (rules : ACL) (header : Header) :
    lookup rules header = none ↔ ∀ rule ∈ rules, rule.test.accepts header = false := by
  induction rules with
  | nil => simp [lookup]
  | cons rule rules ih =>
    cases accepts : rule.test.accepts header <;> simp [lookup, accepts, ih]

@[simp] theorem evaluate_nil (default : Action) (header : Header) :
    evaluate default [] header = default := rfl

@[simp] theorem allows_nil (header : Header) : allows [] header = false := rfl

theorem default_deny_iff (rules : ACL) (header : Header) :
    allows rules header = true ↔ FirstMatch rules header .permit := by
  rw [← lookup_eq_some_iff]
  unfold allows evaluate
  cases lookup rules header with
  | none => simp
  | some action => cases action <;> simp

theorem lookup_append (left right : ACL) (header : Header) :
    lookup (left ++ right) header = (lookup left header).orElse (fun _ => lookup right header) := by
  induction left with
  | nil => rfl
  | cons rule rules ih =>
    cases accepts : rule.test.accepts header <;> simp [lookup, accepts, ih]

/-- The second list is used only when the first list has no match. -/
theorem evaluate_append (default : Action) (left right : ACL) (header : Header) :
    evaluate default (left ++ right) header =
      evaluate (evaluate default right header) left header := by
  simp only [evaluate, lookup_append]
  cases lookup left header <;> rfl

theorem evaluate_cons_accepts (default : Action) (rule : Rule) (rules : ACL) (header : Header)
    (accepts : rule.test.accepts header = true) :
    evaluate default (rule :: rules) header = rule.action := by
  simp [evaluate, lookup, accepts]

theorem evaluate_cons_rejects (default : Action) (rule : Rule) (rules : ACL) (header : Header)
    (rejects : rule.test.accepts header = false) :
    evaluate default (rule :: rules) header = evaluate default rules header := by
  simp [evaluate, lookup, rejects]

/-- A first matching rule keeps its action when more rules follow. -/
theorem first_match_append {left : ACL} {header : Header} {action : Action}
    (first : FirstMatch left header action) (right : ACL) :
    FirstMatch (left ++ right) header action := by
  induction first with
  | here rule rules header accepts => exact .here rule (rules ++ right) header accepts
  | skip rule rejects _ ih => exact .skip rule rejects ih

/-- Extra rules cannot remove an existing permit under the deny default. -/
theorem allows_append_of_allows {left : ACL} {header : Header}
    (allowed : allows left header = true) (right : ACL) :
    allows (left ++ right) header = true :=
  (default_deny_iff _ _).mpr (first_match_append ((default_deny_iff _ _).mp allowed) right)

/-- A deny rule at the start cannot add a permitted packet. -/
theorem prepend_deny_restricts (test : Match) (rules : ACL) (header : Header)
    (allowed : allows (⟨test, .deny⟩ :: rules) header = true) :
    allows rules header = true := by
  cases accepts : test.accepts header with
  | false =>
    unfold allows evaluate at *
    simpa only [lookup, accepts, Bool.false_eq_true, ite_false] using allowed
  | true => simp [allows, evaluate, lookup, accepts] at allowed

/-- A rule has no effect when an earlier rule always covers its match. -/
theorem shadowed_rule (first second : Rule) (rest : ACL)
    (covered : second.test.Refines first.test) (default : Action) (header : Header) :
    evaluate default (first :: second :: rest) header =
      evaluate default (first :: rest) header := by
  cases firstAccepts : first.test.accepts header with
  | true => simp [evaluate, lookup, firstAccepts]
  | false =>
    have secondRejects : second.test.accepts header = false := by
      cases secondAccepts : second.test.accepts header with
      | false => rfl
      | true => have := covered header secondAccepts; simp_all
    simp [evaluate, lookup, firstAccepts, secondRejects]

/-- A policy is stronger when it permits no extra headers. -/
def Refines (stronger weaker : ACL) : Prop :=
  ∀ header, stronger.allows header = true → weaker.allows header = true

theorem refines_refl (rules : ACL) : rules.Refines rules := fun _ => id

theorem Refines.trans {a b c : ACL} (ab : a.Refines b) (bc : b.Refines c) :
    a.Refines c := fun header allowed => bc header (ab header allowed)

theorem prepend_deny_refines (test : Match) (rules : ACL) :
    Refines (⟨test, .deny⟩ :: rules) rules :=
  fun header allowed => prepend_deny_restricts test rules header allowed

/-- Both policies must permit a packet at two successive controls. -/
def serial (left right : ACL) (header : Header) : Bool :=
  left.allows header && right.allows header

theorem serial_comm (left right : ACL) (header : Header) :
    serial left right header = serial right left header := Bool.and_comm _ _

theorem serial_allows_iff (left right : ACL) (header : Header) :
    serial left right header = true ↔ left.allows header = true ∧ right.allows header = true := by
  simp [serial]

end ACL

namespace Forwarding

variable {Node : Type u}

/-- Each directed link has its own access control list. -/
def filter (net : Network Node) (policies : Node → Node → ACL) (header : Header) : Network Node :=
  net.restrict fun source target => (policies source target).allows header = true

theorem link_iff (net : Network Node) (policies : Node → Node → ACL) (header : Header)
    (source target : Node) :
    (filter net policies header).link source target ↔
      net.link source target ∧ (policies source target).allows header = true := Iff.rfl

/-- Packet rules can remove paths. They cannot add paths. -/
theorem reachable_original {net : Network Node} {policies : Node → Node → ACL}
    {header : Header} {source target : Node}
    (path : (filter net policies header).Reachable source target) :
    net.Reachable source target := Network.reachable_restrict _ path

theorem isolation_preserved {net : Network Node} {sources targets : Node → Prop}
    (isolated : net.Isolated sources targets) (policies : Node → Node → ACL) (header : Header) :
    (filter net policies header).Isolated sources targets :=
  Network.isolated_mono isolated (fun _ _ edge => edge.1)

theorem mediation_preserved {net : Network Node} {sources targets gateways : Node → Prop}
    (mediated : net.Mediated sources targets gateways) (policies : Node → Node → ACL)
    (header : Header) : (filter net policies header).Mediated sources targets gateways :=
  Network.mediated_mono mediated (fun _ _ edge => edge.1)

/-- Stronger link policies cannot introduce a new packet path. -/
theorem reachable_of_refines {net : Network Node} {stronger weaker : Node → Node → ACL}
    (refines : ∀ source target, (stronger source target).Refines (weaker source target))
    {header : Header} {source target : Node}
    (path : (filter net stronger header).Reachable source target) :
    (filter net weaker header).Reachable source target :=
  Network.Reachable.mono (net := filter net stronger header) (net' := filter net weaker header)
    (fun a b edge => ⟨edge.1, refines a b header edge.2⟩) path

theorem isolation_of_refines {net : Network Node} {stronger weaker : Node → Node → ACL}
    (refines : ∀ source target, (stronger source target).Refines (weaker source target))
    {header : Header} {sources targets : Node → Prop}
    (isolated : (filter net weaker header).Isolated sources targets) :
    (filter net stronger header).Isolated sources targets :=
  Network.isolated_mono (net := filter net weaker header) (net' := filter net stronger header)
    isolated (fun a b edge => ⟨edge.1, refines a b header edge.2⟩)

end Forwarding
end Netlib.Packet
