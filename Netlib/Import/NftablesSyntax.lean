import Lean
import Netlib.Import.IPv4
import Netlib.Import.Json
import Netlib.Packet.ACL

/-!
# Shared nftables snapshot syntax

Both forwarding profiles use the pinned producer envelope and named header matches.
Connection-state predicates belong to the separate stateful profile.
-/

namespace Netlib.Import.NftablesSyntax

open Packet

def referenceVersion : String := "1.1.3"
def referenceURL : String := "https://netfilter.org/projects/nftables/files/nftables-1.1.3.tar.xz"
def referenceHash : String := "9c8a64b59c90b0825e540a9b8fcb9d2d942c636f81ba50199f068fde44f34ed8"

def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

def fields (json : Lean.Json) (required : List String) (optional : List String := []) :
    Except String Unit := do
  let object ← json.getObj?
  for (key, _) in object.toList do
    require ((required ++ optional).contains key) s!"Unsupported field: {key}."
  for key in required do
    let _ ← json.getObjVal? key

def str (json : Lean.Json) (key : String) : Except String String :=
  json.getObjVal? key >>= Lean.Json.getStr?

def nat (json : Lean.Json) (key : String) : Except String Nat :=
  json.getObjVal? key >>= Lean.Json.getNat?

def handle (json : Lean.Json) : Except String Nat := do
  let value ← nat json "handle"
  require (0 < value && value < 18446744073709551616) "A handle must be a positive 64-bit integer."
  return value

def bounded (limit : Nat) (json : Lean.Json) : Except String (Fin limit) := do
  let value ← json.getNat?
  if fits : value < limit then return ⟨value, fits⟩
  else throw "A packet field exceeds its numeric range."

def optionalString (json : Lean.Json) (key : String) : Except String (Option String) :=
  match json.getObjVal? key with
  | .error _ => .ok none
  | .ok value => some <$> value.getStr?

def singleton (json : Lean.Json) : Except String (String × Lean.Json) := do
  match (← json.getObj?).toList with
  | [entry] => return entry
  | _ => throw "Each snapshot object or expression must have exactly one key."

def action (value : String) : Except String Action :=
  match value with
  | "accept" => .ok .permit
  | "drop" => .ok .deny
  | _ => .error "Only accept and drop verdicts are supported."

def protocol (json : Lean.Json) : Except String Protocol := do
  match json with
  | .str "tcp" => return Protocol.tcp
  | .str "udp" => return Protocol.udp
  | .str "icmp" => return Protocol.icmp
  | .str _ => throw "Use tcp, udp, icmp, or a numeric protocol."
  | _ => bounded 256 json

def parseAddressMatch (json : Lean.Json) : Except String Prefix := do
  match json with
  | .str address => IPv4.parsePrefix address
  | _ =>
    fields json ["prefix"]
    let value ← json.getObjVal? "prefix"
    fields value ["addr", "len"]
    let address ← IPv4.parseAddress (← str value "addr")
    let length ← bounded 33 (← value.getObjVal? "len")
    return ⟨address, length⟩

def ports (json : Lean.Json) : Except String PortRange := do
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

def withProtocol (rule : Match) (selected : Protocol) : Except String Match := do
  match rule.protocol with
  | none => return { rule with protocol := some selected }
  | some existing =>
    require (existing == selected) "Conflicting explicit or implied transport protocols."
    return rule

def parseHeaderMatch (rule : Match) (json : Lean.Json) : Except String Match := do
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

structure RuleInput where
  expressions : Array Lean.Json
  objectIndex : Nat
  expressionIndices : List Nat
  handle : Nat
  sourceID : String
  comment : Option String

def ruleInput (json : Lean.Json) (table chain : String) (index : Nat) : Except String RuleInput := do
  fields json ["family", "table", "chain", "expr", "handle"] ["comment"]
  require ((← str json "family") == "ip") "Only the ip family is supported."
  require ((← str json "table") == table && (← str json "chain") == chain)
    "A rule refers to a different table or chain."
  let handle ← handle json
  let expressions ← (← json.getObjVal? "expr").getArr?
  return {
    expressions
    objectIndex := index
    expressionIndices := List.range expressions.size
    handle
    sourceID := s!"nftables[{index}].rule.handle[{handle}]"
    comment := ← optionalString json "comment" }

structure Envelope where
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
  rules : List RuleInput

def envelope (json : Lean.Json) (hooks : List String := ["forward"]) : Except String Envelope := do
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
    let hook ← str chainObject "hook"
    require ((← str chainObject "type") == "filter" && hooks.contains hook)
      "Only one filter base chain at a supported hook is accepted."
    let chain ← str chainObject "name"
    require (!chain.isEmpty) "The chain name is empty."
    let chainHandle ← handle chainObject
    let priority ← (← chainObject.getObjVal? "prio").getInt?
    require (-2147483648 ≤ priority && priority < 2147483648) "The chain priority exceeds 32 signed bits."
    let policy ← action (← str chainObject "policy")
    let mut rules := []
    for (object, index) in ruleObjects.zipIdx do
      (fields object ["rule"]).mapError (s!"nftables[{index + 3}]: " ++ ·)
      let rule ← (ruleInput (← object.getObjVal? "rule") table chain (index + 3)).mapError
        (s!"nftables[{index + 3}]: " ++ ·)
      require (!(rules.any (fun existing : RuleInput => existing.handle == rule.handle)))
        s!"Duplicate rule handle: {rule.handle}."
      rules := rules ++ [rule]
    return ⟨version, releaseName, table, chain, tableHandle, chainHandle, 1, 2, hook, priority, policy, rules⟩
  | _ => throw "Supply metainfo, one table, one forward chain, and its ordered rules."

end Netlib.Import.NftablesSyntax
