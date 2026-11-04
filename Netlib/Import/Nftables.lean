import Netlib.Import.NftablesSyntax

/-!
# IPv4 forward-chain snapshots

The format reference is nftables 1.1.3 with JSON schema 1.
The model covers one filter chain and normalized IPv4 headers.
Parsing and the relation to Linux execution require review.
-/

namespace Netlib.Import.Nftables

open Packet
open NftablesSyntax

def referenceVersion : String := NftablesSyntax.referenceVersion
def referenceURL : String := NftablesSyntax.referenceURL
def referenceHash : String := NftablesSyntax.referenceHash

structure SourceRule where
  source : Option Prefix := none
  destination : Option Prefix := none
  protocol : Option Protocol := none
  sourcePorts : Option PortRange := none
  destinationPorts : Option PortRange := none
  action : Action
  objectIndex : Nat
  expressionIndices : List Nat
  verdictIndex : Nat
  handle : Nat
  sourceID : String
  comment : Option String := none
  deriving Repr

private def optionalHolds (selected : Option α) (property : α → Prop) : Prop :=
  match selected with
  | none => True
  | some value => property value

private instance optionalHoldsDecidable (selected : Option α) (property : α → Prop)
    [∀ value, Decidable (property value)] : Decidable (optionalHolds selected property) := by
  cases selected <;> unfold optionalHolds <;> infer_instance

private theorem optionalHolds_iff (selected : Option α) (property : α → Prop) :
    (∀ value, selected = some value → property value) ↔ optionalHolds selected property := by
  cases selected <;> simp [optionalHolds]

namespace SourceRule

/-- All selected source-chain predicates must hold before its terminal verdict applies. -/
def Matches (rule : SourceRule) (header : Header) : Prop :=
  optionalHolds rule.source (fun block => block.contains header.source = true) ∧
  optionalHolds rule.destination (fun block => block.contains header.destination = true) ∧
  optionalHolds rule.protocol (fun protocol => protocol = header.protocol) ∧
  optionalHolds rule.sourcePorts (fun ports => ports.contains header.sourcePort = true) ∧
  optionalHolds rule.destinationPorts (fun ports => ports.contains header.destinationPort = true)

instance (rule : SourceRule) (header : Header) : Decidable (rule.Matches header) := by
  unfold Matches
  infer_instance

def accepts (rule : SourceRule) (header : Header) : Bool := decide (rule.Matches header)

def compile (rule : SourceRule) : Packet.Rule :=
  ⟨⟨rule.source, rule.destination, rule.protocol, rule.sourcePorts, rule.destinationPorts⟩, rule.action⟩

theorem compile_accepts (rule : SourceRule) (header : Header) :
    rule.compile.test.accepts header = rule.accepts header := by
  apply Bool.eq_iff_iff.mpr
  rw [accepts, decide_eq_true_eq, Packet.Match.accepts_iff]
  simp only [compile, Packet.Match.Holds, Matches, optionalHolds_iff]

end SourceRule

structure Snapshot where
  version : String
  releaseName : String
  table : String
  chain : String
  tableHandle : Nat
  chainHandle : Nat
  tableIndex : Nat
  chainIndex : Nat
  priority : Int
  policy : Action
  rules : List SourceRule
  deriving Repr

private def evaluateRules (policy : Action) : List SourceRule → Header → Action
  | [], _ => policy
  | rule :: rules, header =>
    if rule.accepts header then rule.action else evaluateRules policy rules header

private theorem compile_rules (rules : List SourceRule) (policy fallback : Action) (header : Header) :
    ACL.evaluate fallback (rules.map SourceRule.compile ++ [⟨{}, policy⟩]) header =
      evaluateRules policy rules header := by
  induction rules with
  | nil => simp [ACL.evaluate, ACL.lookup, Packet.Match.any_accepts, evaluateRules]
  | cons rule rules ih =>
    cases matched : rule.accepts header with
    | false =>
      rw [List.map_cons, List.cons_append,
        ACL.evaluate_cons_rejects fallback rule.compile _ header
          (by rw [SourceRule.compile_accepts]; exact matched)]
      simpa only [evaluateRules, matched, Bool.false_eq_true, ite_false] using ih
    | true =>
      rw [List.map_cons, List.cons_append,
        ACL.evaluate_cons_accepts fallback rule.compile _ header
          (by rw [SourceRule.compile_accepts]; exact matched)]
      simp [evaluateRules, matched, SourceRule.compile]

namespace Snapshot

def compile (snapshot : Snapshot) : ACL :=
  snapshot.rules.map SourceRule.compile ++ [⟨{}, snapshot.policy⟩]

def evaluate (snapshot : Snapshot) (header : Header) : Action :=
  evaluateRules snapshot.policy snapshot.rules header

def permits (snapshot : Snapshot) (header : Header) : Bool :=
  decide (snapshot.evaluate header = .permit)

def policySourceID (snapshot : Snapshot) : String := s!"nftables[{snapshot.chainIndex}].chain.policy"

theorem compile_evaluate (snapshot : Snapshot) (fallback : Action) (header : Header) :
    ACL.evaluate fallback snapshot.compile header = snapshot.evaluate header :=
  compile_rules snapshot.rules snapshot.policy fallback header

theorem compile_allows (snapshot : Snapshot) (header : Header) :
    snapshot.compile.allows header = snapshot.permits header := by
  simp only [ACL.allows, permits, compile_evaluate]

end Snapshot

private def parseMatch (rule : SourceRule) (json : Lean.Json) : Except String SourceRule := do
  let test ← parseHeaderMatch rule.compile.test json
  return { rule with
    source := test.source, destination := test.destination, protocol := test.protocol,
    sourcePorts := test.sourcePorts, destinationPorts := test.destinationPorts }

private def parseRule (input : RuleInput) : Except String SourceRule := do
  let expressions := input.expressions
  let mut rule : SourceRule := {
    action := .deny
    objectIndex := input.objectIndex
    expressionIndices := input.expressionIndices
    verdictIndex := 0
    handle := input.handle
    sourceID := input.sourceID
    comment := input.comment
  }
  let mut finished := false
  for expressionIndex in List.range expressions.size do
    let expression := expressions[expressionIndex]!
    let parsed : Except String SourceRule := do
      require (!finished) "Expressions after a terminal verdict are unsupported."
      let (kind, value) ← singleton expression
      match kind with
      | "match" => parseMatch rule value
      | "accept" | "drop" =>
        require (value == .null) "A terminal verdict must have a null value."
        return { rule with action := ← action kind, verdictIndex := expressionIndex }
      | _ => throw "Only matches and terminal accept/drop statements are supported."
    rule ← parsed.mapError (s!"{rule.sourceID}.expr[{expressionIndex}]: " ++ ·)
    let (kind, _) ← singleton expression
    finished := kind == "accept" || kind == "drop"
  require finished s!"{rule.sourceID}: A rule needs one terminal verdict."
  return rule

namespace Snapshot

def fromJson (json : Lean.Json) : Except String Snapshot := do
  let source ← envelope json
  let mut rules := []
  for input in source.rules do
    let rule ← (parseRule input).mapError (s!"nftables[{input.objectIndex}]: " ++ ·)
    rules := rule :: rules
  return ⟨source.version, source.releaseName, source.table, source.chain, source.tableHandle,
    source.chainHandle, source.tableIndex, source.chainIndex, source.priority, source.policy, rules.reverse⟩

def parse (text : String) : Except String Snapshot := do
  fromJson (← Netlib.Import.Json.parse text)

end Snapshot
end Netlib.Import.Nftables
