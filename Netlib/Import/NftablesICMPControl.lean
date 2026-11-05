import Netlib.Import.NftablesStateful
import Netlib.Packet.ICMPControl

/-!
# Selected native ICMP output policy

The complete table is retained; only the named output filter at priority zero is
compiled. Other declared chains are outside this adapter's policy claim. Deployment
validation must establish that those hooks are observers. Type/code predicates remain
in the structured policy, and their implied ICMP protocol constraint is explicit.
-/

namespace Netlib.Import.NftablesICMPControl

open Packet NftablesSyntax

structure SourceRule where
  base : NftablesStateful.SourceRule
  typeTests : List ICMPControl.Byte
  codeTests : List ICMPControl.Byte
  typeExpressionIndices : List Nat
  codeExpressionIndices : List Nat
  counterExpressionIndices : List Nat
  deriving Repr

def SourceRule.compile (rule : SourceRule) : ICMPControl.Rule :=
  ⟨rule.base.compile, rule.typeTests, rule.codeTests⟩

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
  policyDefault : Action
  rules : List SourceRule
  deriving Repr

def Snapshot.policy (snapshot : Snapshot) : ICMPControl.Policy :=
  ⟨snapshot.rules.map SourceRule.compile, snapshot.policyDefault⟩

def Snapshot.compile (snapshot : Snapshot) (kind : Protocol.ICMP.Kind) : StatefulACL.Policy :=
  snapshot.policy.compile kind

def Snapshot.evaluate (snapshot : Snapshot) (kind : Protocol.ICMP.Kind) (state : StatefulACL.CTState)
    (header : Header) : Action := snapshot.policy.evaluate kind state header

def Snapshot.permits (snapshot : Snapshot) (kind : Protocol.ICMP.Kind) (state : StatefulACL.CTState)
    (header : Header) : Bool := decide (snapshot.evaluate kind state header = .permit)

theorem Snapshot.compile_evaluate (snapshot : Snapshot) (fallback : Action) (kind : Protocol.ICMP.Kind)
    (state : StatefulACL.CTState) (header : Header) :
    StatefulACL.Policy.evaluate fallback (snapshot.compile kind) state header = snapshot.evaluate kind state header :=
  snapshot.policy.compile_evaluate fallback kind state header

def Snapshot.policySourceID (snapshot : Snapshot) : String := s!"nftables[{snapshot.chainIndex}].chain.policy"

private def nativeSnapshot (metadata table chain : Lean.Json) (rules : List Lean.Json) : Lean.Json :=
  Lean.Json.mkObj [("nftables", Lean.toJson ([metadata, table, chain] ++ rules))]

private def counter (value : Lean.Json) : Except String Unit := do
  fields value ["packets", "bytes"]
  let _ ← bounded 18446744073709551616 (← value.getObjVal? "packets")
  let _ ← bounded 18446744073709551616 (← value.getObjVal? "bytes")

private def parseRule (metadata table chain : Lean.Json) (input : Lean.Json) (index : Nat) :
    Except String SourceRule := do
  let expressions ← (← input.getObjVal? "expr").getArr?
  let mut types := []
  let mut codes := []
  let mut typeIndices := []
  let mut codeIndices := []
  let mut counterIndices := []
  let mut baseExpressions := []
  let mut baseIndices := []
  let mut verdict : Option Nat := none
  for expressionIndex in List.range expressions.size do
    require verdict.isNone "Expressions after a terminal verdict are unsupported."
    let expression := expressions[expressionIndex]!
    let (kind, value) ← singleton expression
    if kind == "counter" then
      require counterIndices.isEmpty "Repeated counter statements are unsupported."
      counter value
      counterIndices := [expressionIndex]
    else if kind == "match" then
      fields value ["left", "right", "op"]
      let (leftKind, left) ← singleton (← value.getObjVal? "left")
      let isICMP ← if leftKind == "payload" then do
          pure ((← str left "protocol") == "icmp")
        else pure false
      if isICMP then
        fields left ["protocol", "field"]
        require ((← str value "op") == "==") "Only numeric ICMP type/code equality is supported."
        let selected ← bounded 256 (← value.getObjVal? "right")
        match ← str left "field" with
        | "type" =>
          require types.isEmpty "Repeated ICMP type predicates are unsupported."
          types := [selected]
          typeIndices := [expressionIndex]
        | "code" =>
          require codes.isEmpty "Repeated ICMP code predicates are unsupported."
          codes := [selected]
          codeIndices := [expressionIndex]
        | _ => throw "Only ICMP type and code payload fields are supported."
      else
        baseExpressions := baseExpressions ++ [expression]
        baseIndices := baseIndices ++ [expressionIndex]
    else
      require (kind == "accept" || kind == "drop") "Only matches, anonymous counters, and terminal verdicts are supported."
      baseExpressions := baseExpressions ++ [expression]
      baseIndices := baseIndices ++ [expressionIndex]
      verdict := some expressionIndex
  require verdict.isSome "An ICMP control rule needs one terminal verdict."
  let rewritten := input.setObjVal! "expr" (Lean.toJson baseExpressions)
  let parsed ← NftablesStateful.Snapshot.fromJsonFor
    (nativeSnapshot metadata table chain [Lean.Json.mkObj [("rule", rewritten)]]) ["output"]
  let [base] := parsed.rules | throw "Expected one selected ICMP control rule."
  let test ← if types.isEmpty && codes.isEmpty then pure base.compile.test
    else withProtocol base.compile.test Protocol.icmp
  let sourceID := s!"nftables[{index}].rule.handle[{base.handle}]"
  let base : NftablesStateful.SourceRule := { base with
    protocol := test.protocol
    objectIndex := index
    sourceID
    expressionIndices := List.range expressions.size
    verdictIndex := verdict.getD 0
    stateExpressionIndex := base.stateExpressionIndex.bind (fun selected => baseIndices[selected]?) }
  return ⟨base, types, codes, typeIndices, codeIndices, counterIndices⟩

namespace Snapshot

def fromJson (json : Lean.Json) : Except String Snapshot := do
  fields json ["nftables"]
  let objects ← (← json.getObjVal? "nftables").getArr?
  let metadata :: tableObject :: rest := objects.toList | throw "Supply metainfo and a complete IPv4 table."
  let tableValue ← tableObject.getObjVal? "table"
  let tableName ← str tableValue "name"
  let mut chains := []
  let mut selected : Option (Nat × Lean.Json) := none
  for (object, offset) in rest.zipIdx do
    let (kind, value) ← singleton object
    if kind == "chain" then
      fields value ["family", "table", "name", "handle", "type", "hook", "prio", "policy"]
      require ((← str value "family") == "ip" && (← str value "table") == tableName)
        "Every declared chain must belong to the selected IPv4 table."
      let name ← str value "name"
      require (!name.isEmpty && !chains.contains name) "Chain names must be nonempty and unique."
      let _ ← handle value
      let _ ← (← value.getObjVal? "prio").getInt?
      chains := chains ++ [name]
      if name == "output" then
        require selected.isNone "The named output chain is duplicated."
        selected := some (offset + 2, object)
    else require (kind == "rule") "Only table chains and their rules are supported."
  let some (chainIndex, chainObject) := selected | throw "The named output filter chain is missing."
  let base ← NftablesStateful.Snapshot.fromJsonFor (nativeSnapshot metadata tableObject chainObject []) ["output"]
  require (base.chain == "output" && base.priority == 0) "Select the named output filter chain at priority zero."
  let mut rules := []
  for (object, offset) in rest.zipIdx do
    let (kind, value) ← singleton object
    if kind == "rule" then
      fields value ["family", "table", "chain", "expr", "handle"] ["comment"]
      require ((← str value "family") == "ip" && (← str value "table") == tableName)
        "Every rule must belong to the selected IPv4 table."
      let chain ← str value "chain"
      require (chains.contains chain) "A rule names an undeclared chain."
      let _ ← handle value
      let _ ← (← value.getObjVal? "expr").getArr?
      if chain == "output" then
        let parsed ← (parseRule metadata tableObject chainObject value (offset + 2)).mapError
          (s!"nftables[{offset + 2}]: " ++ ·)
        require (!(rules.any (fun rule : SourceRule => rule.base.handle == parsed.base.handle)))
          "The selected output chain contains duplicate rule handles."
        rules := rules ++ [parsed]
  return ⟨base.version, base.releaseName, base.table, base.chain, base.tableHandle, base.chainHandle,
    1, chainIndex, base.hook, base.priority, base.policy, rules⟩

def parse (text : String) : Except String Snapshot := do fromJson (← Json.parse text)

end Snapshot
end Netlib.Import.NftablesICMPControl
