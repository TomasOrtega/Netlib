import Lean
import Netlib.Import.IPv4
import Netlib.Import.Json
import Netlib.Packet.ACL

/-!
# IPv4 forward-chain snapshots

The format reference is nftables 1.1.3 with JSON schema 1.
The model covers one filter chain and normalized IPv4 headers.
Parsing and the relation to Linux execution require review.
-/

namespace Netlib.Import.Nftables

open Packet

def referenceVersion : String := "1.1.3"
def referenceURL : String := "https://netfilter.org/projects/nftables/files/nftables-1.1.3.tar.xz"
def referenceHash : String := "9c8a64b59c90b0825e540a9b8fcb9d2d942c636f81ba50199f068fde44f34ed8"

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

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def fields (json : Lean.Json) (required : List String) (optional : List String := []) :
    Except String Unit := do
  let object ← json.getObj?
  for (key, _) in object.toList do
    require ((required ++ optional).contains key) s!"Unsupported field: {key}."
  for key in required do
    let _ ← json.getObjVal? key

private def str (json : Lean.Json) (key : String) : Except String String :=
  json.getObjVal? key >>= Lean.Json.getStr?

private def nat (json : Lean.Json) (key : String) : Except String Nat :=
  json.getObjVal? key >>= Lean.Json.getNat?

private def handle (json : Lean.Json) : Except String Nat := do
  let value ← nat json "handle"
  require (0 < value && value < 18446744073709551616) "A handle must be a positive 64-bit integer."
  return value

private def bounded (limit : Nat) (json : Lean.Json) : Except String (Fin limit) := do
  let value ← json.getNat?
  if fits : value < limit then return ⟨value, fits⟩
  else throw "A packet field exceeds its numeric range."

private def optionalString (json : Lean.Json) (key : String) : Except String (Option String) :=
  match json.getObjVal? key with
  | .error _ => .ok none
  | .ok value => some <$> value.getStr?

private def singleton (json : Lean.Json) : Except String (String × Lean.Json) := do
  match (← json.getObj?).toList with
  | [entry] => return entry
  | _ => throw "Each snapshot object or expression must have exactly one key."

private def action (value : String) : Except String Action :=
  match value with
  | "accept" => .ok .permit
  | "drop" => .ok .deny
  | _ => .error "Only accept and drop verdicts are supported."

private def protocol (json : Lean.Json) : Except String Protocol := do
  match json with
  | .str "tcp" => return Protocol.tcp
  | .str "udp" => return Protocol.udp
  | .str "icmp" => return Protocol.icmp
  | .str _ => throw "Use tcp, udp, icmp, or a numeric protocol."
  | _ => bounded 256 json

private def parseAddressMatch (json : Lean.Json) : Except String Prefix := do
  match json with
  | .str address => IPv4.parsePrefix address
  | _ =>
    fields json ["prefix"]
    let value ← json.getObjVal? "prefix"
    fields value ["addr", "len"]
    let address ← IPv4.parseAddress (← str value "addr")
    let length ← bounded 33 (← value.getObjVal? "len")
    return ⟨address, length⟩

private def ports (json : Lean.Json) : Except String PortRange := do
  match json with
  | .num _ => return PortRange.single (← bounded 65536 json)
  | _ =>
    fields json ["range"]
    let values ← (← json.getObjVal? "range").getArr?
    match values.toList with
    | [first, last] =>
      let first ← bounded 65536 first
      let last ← bounded 65536 last
      require (first ≤ last) "A port range has reversed bounds."
      return ⟨first, last⟩
    | _ => throw "A port range must have two numeric bounds."

private def withProtocol (rule : SourceRule) (selected : Protocol) : Except String SourceRule := do
  match rule.protocol with
  | none => return { rule with protocol := some selected }
  | some existing =>
    require (existing == selected) "Conflicting explicit or implied transport protocols."
    return rule

private def parseMatch (rule : SourceRule) (json : Lean.Json) : Except String SourceRule := do
  fields json ["left", "right", "op"]
  require ((← str json "op") == "==") "Only equality matches are supported."
  let right ← json.getObjVal? "right"
  let (kind, left) ← singleton (← json.getObjVal? "left")
  match kind with
  | "meta" =>
    fields left ["key"]
    require ((← str left "key") == "l4proto") "Only l4proto metadata matches are supported."
    withProtocol rule (← protocol right)
  | "payload" =>
    fields left ["protocol", "field"]
    let family ← str left "protocol"
    let field ← str left "field"
    match family, field with
    | "ip", "saddr" =>
      require rule.source.isNone "Repeated source-address matches are unsupported."
      return { rule with source := some (← parseAddressMatch right) }
    | "ip", "daddr" =>
      require rule.destination.isNone "Repeated destination-address matches are unsupported."
      return { rule with destination := some (← parseAddressMatch right) }
    | "ip", "protocol" => withProtocol rule (← protocol right)
    | "tcp", "sport" | "udp", "sport" =>
      require rule.sourcePorts.isNone "Repeated source-port matches are unsupported."
      let rule ← withProtocol rule (if family == "tcp" then Protocol.tcp else Protocol.udp)
      return { rule with sourcePorts := some (← ports right) }
    | "tcp", "dport" | "udp", "dport" =>
      require rule.destinationPorts.isNone "Repeated destination-port matches are unsupported."
      let rule ← withProtocol rule (if family == "tcp" then Protocol.tcp else Protocol.udp)
      return { rule with destinationPorts := some (← ports right) }
    | _, _ => throw "Unsupported payload protocol or field."
  | _ => throw "Only named payload and l4proto expressions are supported."

private def parseRule (json : Lean.Json) (table chain : String) (index : Nat) : Except String SourceRule := do
  fields json ["family", "table", "chain", "expr", "handle"] ["comment"]
  require ((← str json "family") == "ip") "Only the ip family is supported."
  require ((← str json "table") == table && (← str json "chain") == chain)
    "A rule refers to a different table or chain."
  let handle ← handle json
  let expressions ← (← json.getObjVal? "expr").getArr?
  let mut rule : SourceRule := {
    action := .deny
    objectIndex := index
    expressionIndices := List.range expressions.size
    verdictIndex := 0
    handle := handle
    sourceID := s!"nftables[{index}].rule.handle[{handle}]"
    comment := ← optionalString json "comment"
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
  fields json ["nftables"]
  let objects ← (← json.getObjVal? "nftables").getArr?
  match objects.toList with
  | metadata :: tableObject :: chainObject :: ruleObjects =>
    fields metadata ["metainfo"]
    let metadata ← metadata.getObjVal? "metainfo"
    fields metadata ["version", "release_name", "json_schema_version"]
    let version ← str metadata "version"
    require (version == referenceVersion) "Use a complete nftables 1.1.3 snapshot."
    require ((← nat metadata "json_schema_version") == 1) "Only JSON schema 1 is supported."
    let releaseName ← str metadata "release_name"
    fields tableObject ["table"]
    let tableObject ← tableObject.getObjVal? "table"
    fields tableObject ["family", "name", "handle"] ["flags"]
    require ((← str tableObject "family") == "ip") "Only one IPv4 ip table is supported."
    match tableObject.getObjVal? "flags" with
    | .error _ => pure ()
    | .ok flags => require ((← flags.getArr?).isEmpty) "Table flags are unsupported."
    let table ← str tableObject "name"
    require (!table.isEmpty) "The table name is empty."
    let tableHandle ← handle tableObject
    fields chainObject ["chain"]
    let chainObject ← chainObject.getObjVal? "chain"
    fields chainObject ["family", "table", "name", "handle", "type", "hook", "prio", "policy"]
    require ((← str chainObject "family") == "ip" && (← str chainObject "table") == table)
      "The chain must belong to the declared IPv4 table."
    require ((← str chainObject "type") == "filter" && (← str chainObject "hook") == "forward")
      "Only one forward filter base chain is supported."
    let chain ← str chainObject "name"
    require (!chain.isEmpty) "The chain name is empty."
    let chainHandle ← handle chainObject
    let priority ← (← chainObject.getObjVal? "prio").getInt?
    require (-2147483648 ≤ priority && priority < 2147483648) "The chain priority exceeds 32 signed bits."
    let policy ← action (← str chainObject "policy")
    let mut rules := []
    for (object, index) in ruleObjects.zipIdx do
      (fields object ["rule"]).mapError (s!"nftables[{index + 3}]: " ++ ·)
      let rule ← (parseRule (← object.getObjVal? "rule") table chain (index + 3)).mapError
        (s!"nftables[{index + 3}]: " ++ ·)
      require (!(rules.any (fun existing : SourceRule => existing.handle == rule.handle)))
        s!"Duplicate rule handle: {rule.handle}."
      rules := rules ++ [rule]
    return ⟨version, releaseName, table, chain, tableHandle, chainHandle, 1, 2, priority, policy, rules⟩
  | _ => throw "Supply metainfo, one table, one forward chain, and its ordered rules."

def parse (text : String) : Except String Snapshot := do
  fromJson (← Netlib.Import.Json.parse text)

end Snapshot
end Netlib.Import.Nftables
