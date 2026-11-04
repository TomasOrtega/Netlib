import Netlib.Import.Nftables
import Netlib.Packet.StatefulACL

/-!
# IPv4 filter-chain state predicates

The reference is nftables 1.1.3 JSON schema 1, including its native `in` state lists.
The state describes the current packet at the selected filter stage.
Compilation preserves the structured chain for every supplied state and header.
This does not classify native packets or establish authentication, transport state, or policy provenance.
-/

namespace Netlib.Import.NftablesStateful

open Packet NftablesSyntax
open StatefulACL (CTState)

structure SourceRule extends Nftables.SourceRule where
  states : Option (List CTState) := none
  stateExpressionIndex : Option Nat := none
  deriving Repr

namespace SourceRule

def Matches (rule : SourceRule) (state : CTState) (header : Header) : Prop :=
  rule.toSourceRule.Matches header ∧ match rule.states with
    | none => True
    | some states => state ∈ states

instance (rule : SourceRule) (state : CTState) (header : Header) :
    Decidable (rule.Matches state header) := by
  unfold Matches
  cases rule.states <;> infer_instance

def accepts (rule : SourceRule) (state : CTState) (header : Header) : Bool :=
  decide (rule.Matches state header)

def compile (rule : SourceRule) : StatefulACL.Rule :=
  ⟨rule.toSourceRule.compile.test, rule.states, rule.action⟩

def stateSourceID (rule : SourceRule) : Option String :=
  rule.stateExpressionIndex.map (fun index => s!"{rule.sourceID}.expr[{index}]")

theorem compile_accepts (rule : SourceRule) (state : CTState) (header : Header) :
    rule.compile.accepts state header = rule.accepts state header := by
  apply Bool.eq_iff_iff.mpr
  rw [StatefulACL.Rule.accepts_iff, accepts, decide_eq_true_eq]
  change (rule.toSourceRule.compile.test.Holds header ∧ _) ↔
    (rule.toSourceRule.Matches header ∧ _)
  rw [← Packet.Match.accepts_iff, Nftables.SourceRule.compile_accepts]
  simp only [compile, Nftables.SourceRule.accepts, decide_eq_true_eq]
  rfl

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
  hook : String
  priority : Int
  policy : Action
  rules : List SourceRule
  deriving Repr

private def evaluateRules (policy : Action) : List SourceRule → CTState → Header → Action
  | [], _, _ => policy
  | rule :: rules, state, header =>
    if rule.accepts state header then rule.action else evaluateRules policy rules state header

private theorem compile_rules (rules : List SourceRule) (policy fallback : Action)
    (state : CTState) (header : Header) :
    StatefulACL.Policy.evaluate fallback (rules.map SourceRule.compile ++ [⟨{}, none, policy⟩]) state header =
      evaluateRules policy rules state header := by
  induction rules with
  | nil => simp [StatefulACL.Policy.evaluate, StatefulACL.Policy.lookup, evaluateRules]
  | cons rule rules ih =>
    cases matched : rule.accepts state header with
    | false =>
      rw [List.map_cons, List.cons_append,
        StatefulACL.Policy.evaluate_cons_rejects fallback rule.compile _ state header
          (by rw [SourceRule.compile_accepts]; exact matched)]
      simpa only [evaluateRules, matched, Bool.false_eq_true, ite_false] using ih
    | true =>
      rw [List.map_cons, List.cons_append,
        StatefulACL.Policy.evaluate_cons_accepts fallback rule.compile _ state header
          (by rw [SourceRule.compile_accepts]; exact matched)]
      simp [evaluateRules, matched, SourceRule.compile]

namespace Snapshot

def compile (snapshot : Snapshot) : StatefulACL.Policy :=
  snapshot.rules.map SourceRule.compile ++ [⟨{}, none, snapshot.policy⟩]

def evaluate (snapshot : Snapshot) (state : CTState) (header : Header) : Action :=
  evaluateRules snapshot.policy snapshot.rules state header

def permits (snapshot : Snapshot) (state : CTState) (header : Header) : Bool :=
  decide (snapshot.evaluate state header = .permit)

def policySourceID (snapshot : Snapshot) : String := s!"nftables[{snapshot.chainIndex}].chain.policy"

theorem compile_evaluate (snapshot : Snapshot) (fallback : Action) (state : CTState) (header : Header) :
    StatefulACL.Policy.evaluate fallback snapshot.compile state header = snapshot.evaluate state header :=
  compile_rules snapshot.rules snapshot.policy fallback state header

theorem compile_allows (snapshot : Snapshot) (state : CTState) (header : Header) :
    snapshot.compile.allows state header = snapshot.permits state header := by
  simp only [StatefulACL.Policy.allows, permits, compile_evaluate]

end Snapshot

private def parseState (json : Lean.Json) : Except String CTState := do
  match json with
  | .num _ =>
    match ← json.getNat? with
    | 1 => return .invalid
    | 2 => return .established
    | 4 => return .related
    | 8 => return .new
    | 64 => return .untracked
    | _ => throw "A state equality or set element requires one known state bit."
  | _ =>
    match ← json.getStr? with
    | "new" => return .new
    | "established" => return .established
    | "related" => return .related
    | "invalid" => return .invalid
    | "untracked" => return .untracked
    | value => throw s!"Unsupported conntrack state: {value}."

private def parseStates (operator : String) (right : Lean.Json) : Except String (List CTState) := do
  require (operator == "in" || operator == "==") "Only state membership and equality are supported."
  let values ← match right with
    | .str _ => pure [right]
    | .num _ => do
      if operator == "==" then pure [right]
      else
        let mask ← right.getNat?
        require (0 < mask && mask < 128 && !mask.testBit 4 && !mask.testBit 5)
          "A state mask must contain only supported nonzero state bits."
        pure ([(0, 1), (1, 2), (2, 4), (3, 8), (6, 64)].filterMap
          (fun (bit, value) => if mask.testBit bit then some (Lean.toJson value) else none))
    | .arr values => do
      require (operator == "in") "Bare state lists require the native in operator."
      pure values.toList
    | _ => do
      fields right ["set"]
      pure (← (← right.getObjVal? "set").getArr?).toList
  require (!values.isEmpty) "Empty conntrack state selections are unsupported."
  let mut states := []
  for value in values do
    let state ← parseState value
    require (!states.contains state) "Repeated conntrack state values are unsupported."
    states := state :: states
  return states.reverse

private def parseMatch (rule : SourceRule) (json : Lean.Json) (index : Nat) : Except String SourceRule := do
  fields json ["left", "right", "op"]
  let (kind, left) ← singleton (← json.getObjVal? "left")
  if kind == "ct" then
    fields left ["key"]
    require ((← str left "key") == "state") "Only conntrack state predicates are supported."
    require rule.states.isNone "Repeated conntrack state predicates are unsupported."
    return { rule with
      states := some (← parseStates (← str json "op") (← json.getObjVal? "right"))
      stateExpressionIndex := some index }
  else
    let test ← parseHeaderMatch rule.toSourceRule.compile.test json
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
    comment := input.comment }
  let mut finished := false
  for expressionIndex in List.range expressions.size do
    let expression := expressions[expressionIndex]!
    let parsed : Except String SourceRule := do
      require (!finished) "Expressions after a terminal verdict are unsupported."
      let (kind, value) ← singleton expression
      match kind with
      | "match" => parseMatch rule value expressionIndex
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
  let source ← envelope json ["forward", "postrouting"]
  let mut rules := []
  for input in source.rules do
    let rule ← (parseRule input).mapError (s!"nftables[{input.objectIndex}]: " ++ ·)
    rules := rule :: rules
  return ⟨source.version, source.releaseName, source.table, source.chain, source.tableHandle,
    source.chainHandle, source.tableIndex, source.chainIndex, source.hook, source.priority, source.policy, rules.reverse⟩

def parse (text : String) : Except String Snapshot := do
  fromJson (← Json.parse text)

end Snapshot
end Netlib.Import.NftablesStateful
