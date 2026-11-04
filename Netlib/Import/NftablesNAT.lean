import Netlib.Import.NftablesSyntax
import Netlib.Protocol.NetfilterNAT

/-!
# Fixed-endpoint NAT tables

The profile reads one nftables 1.1.3 IPv4 table with prerouting DNAT and postrouting SNAT chains.
Each stage selects its first matching fixed rewrite. A miss preserves the header.
Candidates describe a proposed fresh tuple pair, not an allocation or an installed binding.
The theorems concern structured header translation, not kernel C, hook execution, or port allocation.
-/

namespace Netlib.Import.NftablesNAT

open Packet Protocol NftablesSyntax

inductive Kind where
  | destination
  | source
  deriving Repr, BEq, DecidableEq

structure CompiledRule where
  test : Match
  rewrite : Rewrite
  deriving Repr

def runRules : List CompiledRule → Header → Header
  | [], header => header
  | rule :: rules, header =>
    if rule.test.accepts header then rule.rewrite.apply header else runRules rules header

structure SourceRule where
  test : Match := {}
  kind : Kind
  address : Address
  port : Option Port
  objectIndex : Nat
  expressionIndices : List Nat
  verdictIndex : Nat
  handle : Nat
  sourceID : String
  comment : Option String
  deriving Repr

namespace SourceRule

def Matches (rule : SourceRule) (header : Header) : Prop := rule.test.Holds header

instance (rule : SourceRule) (header : Header) : Decidable (rule.Matches header) := by
  exact decidable_of_iff (rule.test.accepts header = true) (Packet.Match.accepts_iff _ _)

def accepts (rule : SourceRule) (header : Header) : Bool := decide (rule.Matches header)

def translate (rule : SourceRule) (header : Header) : Header :=
  match rule.kind with
  | .destination => { header with destination := rule.address, destinationPort := rule.port.getD header.destinationPort }
  | .source => { header with source := rule.address, sourcePort := rule.port.getD header.sourcePort }

def compile (rule : SourceRule) : CompiledRule :=
  ⟨rule.test, match rule.kind with
    | .destination => { destination := some rule.address, destinationPort := rule.port }
    | .source => { source := some rule.address, sourcePort := rule.port }⟩

theorem compile_accepts (rule : SourceRule) (header : Header) :
    rule.compile.test.accepts header = rule.accepts header := by
  apply Bool.eq_iff_iff.mpr
  simp only [compile, Packet.Match.accepts_iff, accepts]
  exact (decide_eq_true_iff (p := rule.Matches header)).symm

theorem compile_translate (rule : SourceRule) (header : Header) :
    rule.compile.rewrite.apply header = rule.translate header := by
  cases selected : rule.kind <;> simp [compile, translate, selected, Rewrite.apply]

theorem translate_protocol (rule : SourceRule) (header : Header) :
    (rule.translate header).protocol = header.protocol := by
  cases selected : rule.kind <;> simp [translate, selected]

end SourceRule

def evaluateRules : List SourceRule → Header → Header
  | [], header => header
  | rule :: rules, header =>
    if rule.accepts header then rule.translate header else evaluateRules rules header

theorem compile_rules (rules : List SourceRule) (header : Header) :
    runRules (rules.map SourceRule.compile) header = evaluateRules rules header := by
  induction rules with
  | nil => rfl
  | cons rule rules ih =>
    simp only [List.map_cons, runRules, SourceRule.compile_accepts, evaluateRules]
    split
    · exact rule.compile_translate header
    · exact ih

theorem evaluateRules_protocol (rules : List SourceRule) (header : Header) :
    (evaluateRules rules header).protocol = header.protocol := by
  induction rules with
  | nil => rfl
  | cons rule rules ih =>
    unfold evaluateRules
    split
    · exact rule.translate_protocol header
    · exact ih

structure Chain where
  name : String
  kind : Kind
  hook : String
  priority : Int
  handle : Nat
  objectIndex : Nat
  rules : List SourceRule
  deriving Repr

def Chain.compile (chain : Chain) : List CompiledRule := chain.rules.map SourceRule.compile

structure Snapshot where
  version : String
  releaseName : String
  table : String
  tableHandle : Nat
  tableIndex : Nat
  destinationChain : Chain
  sourceChain : Chain
  deriving Repr

namespace Snapshot

def destination (snapshot : Snapshot) (packet : Header) : Header :=
  runRules snapshot.destinationChain.compile packet

def source (snapshot : Snapshot) (packet : Header) : Header :=
  runRules snapshot.sourceChain.compile packet

def translated (snapshot : Snapshot) (packet : Header) : Header :=
  snapshot.source (snapshot.destination packet)

theorem destination_correct (snapshot : Snapshot) (packet : Header) :
    snapshot.destination packet = evaluateRules snapshot.destinationChain.rules packet :=
  compile_rules snapshot.destinationChain.rules packet

theorem source_correct (snapshot : Snapshot) (packet : Header) :
    snapshot.source packet = evaluateRules snapshot.sourceChain.rules packet :=
  compile_rules snapshot.sourceChain.rules packet

theorem destination_protocol (snapshot : Snapshot) (packet : Header) :
    (snapshot.destination packet).protocol = packet.protocol := by
  rw [destination_correct]
  exact evaluateRules_protocol _ _

theorem source_protocol (snapshot : Snapshot) (packet : Header) :
    (snapshot.source packet).protocol = packet.protocol := by
  rw [source_correct]
  exact evaluateRules_protocol _ _

theorem translated_protocol (snapshot : Snapshot) (packet : Header) :
    (snapshot.translated packet).protocol = packet.protocol := by
  rw [translated, source_protocol, destination_protocol]

def candidate (snapshot : Snapshot) (zone : Nat) (packet : Header) : NetfilterNAT.Entry :=
  let after := snapshot.translated packet
  { flow := ⟨packet, after.reverse, zone, zone, 0⟩
    sourceNAT := decide (packet.sourceEndpoint ≠ after.sourceEndpoint)
    destinationNAT := decide (packet.destinationEndpoint ≠ after.destinationEndpoint) }

theorem candidate_original (snapshot : Snapshot) (zone : Nat) (packet : Header) :
    (snapshot.candidate zone packet).flow.original = packet := rfl

theorem candidate_reply (snapshot : Snapshot) (zone : Nat) (packet : Header) :
    (snapshot.candidate zone packet).flow.reply = (snapshot.translated packet).reverse := rfl

theorem candidate_output (snapshot : Snapshot) (zone : Nat) (packet : Header) :
    (snapshot.candidate zone packet).flow.output .original = snapshot.translated packet := rfl

theorem candidate_compatible (snapshot : Snapshot) (zone : Nat) (packet : Header)
    (supported : packet.protocol = Packet.Protocol.tcp ∨ packet.protocol = Packet.Protocol.udp)
    (zoneBound : zone < 65536)
    (distinct : packet ≠ (snapshot.translated packet).reverse) :
    (snapshot.candidate zone packet).Compatible := by
  constructor
  · refine ⟨?_, supported, zoneBound, zoneBound, ?_, ?_⟩
    · exact (snapshot.translated_protocol packet).symm
    · change 0 < 4294967296
      decide
    · intro same
      exact distinct (congrArg Prod.snd same)
  · constructor
    · intro unchanged
      change packet.sourceEndpoint = (snapshot.translated packet).sourceEndpoint
      exact Decidable.byContradiction (of_decide_eq_false unchanged)
    · intro unchanged
      change packet.destinationEndpoint = (snapshot.translated packet).destinationEndpoint
      exact Decidable.byContradiction (of_decide_eq_false unchanged)

end Snapshot

private def parseChain (json : Lean.Json) (table : String) (index : Nat) : Except String Chain := do
  fields json ["chain"]
  let json ← json.getObjVal? "chain"
  fields json ["family", "table", "name", "handle", "type", "hook", "prio", "policy"]
  require ((← str json "family") == "ip" && (← str json "table") == table)
    "A NAT chain must belong to the declared IPv4 table."
  require ((← str json "type") == "nat" && (← str json "policy") == "accept")
    "Require NAT base chains with accept policy."
  let name ← str json "name"
  require (!name.isEmpty) "A NAT chain name is empty."
  let hook ← str json "hook"
  let priority ← (← json.getObjVal? "prio").getInt?
  let kind ←
    if hook == "prerouting" && priority == -100 then pure Kind.destination
    else if hook == "postrouting" && priority == 100 then pure Kind.source
    else throw "Require prerouting DNAT priority -100 and postrouting SNAT priority 100."
  return ⟨name, kind, hook, priority, ← handle json, index, []⟩

private def target (json : Lean.Json) : Except String (Address × Option Port) := do
  fields json ["addr"] ["port"]
  let address ← IPv4.parseAddress (← str json "addr")
  let port ← match json.getObjVal? "port" with
    | .error _ => pure none
    | .ok port => some <$> bounded 65536 port
  return (address, port)

private def parseRule (input : RuleInput) (kind : Kind) : Except String SourceRule := do
  let expressions := input.expressions
  let mut test : Match := {}
  let mut result : Option SourceRule := none
  for index in List.range expressions.size do
    let parsed : Except String (Match × Option SourceRule) := do
      require result.isNone "Expressions after a NAT target are unsupported."
      let (statement, value) ← singleton expressions[index]!
      match statement with
      | "match" => return (← parseHeaderMatch test value, none)
      | "dnat" | "snat" =>
        require ((kind == .destination && statement == "dnat") || (kind == .source && statement == "snat"))
          "A NAT target belongs to the wrong hook."
        let (address, port) ← target value
        return (test, some {
          test, kind, address, port
          objectIndex := input.objectIndex
          expressionIndices := input.expressionIndices
          verdictIndex := index
          handle := input.handle
          sourceID := input.sourceID
          comment := input.comment })
      | _ => throw "Only header matches and one fixed snat/dnat target are supported."
    let (nextTest, nextResult) ← parsed.mapError (s!"{input.sourceID}.expr[{index}]: " ++ ·)
    test := nextTest
    result := nextResult
  match result with
  | none => throw s!"{input.sourceID}: A NAT rule requires one target."
  | some rule => return rule

namespace Snapshot

def fromJson (json : Lean.Json) : Except String Snapshot := do
  fields json ["nftables"]
  let objects ← (← json.getObjVal? "nftables").getArr?
  match objects.toList with
  | metadata :: tableObject :: firstChain :: secondChain :: rules =>
    fields metadata ["metainfo"]
    let metadata ← metadata.getObjVal? "metainfo"
    fields metadata ["version", "release_name", "json_schema_version"]
    let version ← str metadata "version"
    require (version == referenceVersion && (← nat metadata "json_schema_version") == 1)
      "Require nftables 1.1.3 JSON schema 1."
    let releaseName ← str metadata "release_name"
    fields tableObject ["table"]
    let tableObject ← tableObject.getObjVal? "table"
    fields tableObject ["family", "name", "handle"] ["flags"]
    require ((← str tableObject "family") == "ip") "Only one IPv4 NAT table is supported."
    match tableObject.getObjVal? "flags" with
    | .error _ => pure ()
    | .ok value => require ((← value.getArr?).isEmpty) "NAT table flags are unsupported."
    let table ← str tableObject "name"
    require (!table.isEmpty) "The NAT table name is empty."
    let tableHandle ← handle tableObject
    let first ← parseChain firstChain table 2
    let second ← parseChain secondChain table 3
    require (first.kind != second.kind && first.name != second.name && first.handle != second.handle)
      "Require two distinct NAT chains with different hooks."
    let mut destination := if first.kind == .destination then first else second
    let mut source := if first.kind == .source then first else second
    let mut handles : List Nat := []
    for (object, offset) in rules.zipIdx do
      let index := offset + 4
      let parsed : Except String (SourceRule × Bool) := do
        fields object ["rule"]
        let json ← object.getObjVal? "rule"
        let name ← str json "chain"
        require (name == destination.name || name == source.name) "A NAT rule refers to another chain."
        let input ← ruleInput json table name index
        require (!handles.contains input.handle) "Duplicate NAT rule handle."
        let rule ← parseRule input (if name == destination.name then .destination else .source)
        return (rule, name == destination.name)
      let (rule, isDestination) ← parsed.mapError (s!"nftables[{index}]: " ++ ·)
      handles := rule.handle :: handles
      if isDestination then destination := { destination with rules := destination.rules ++ [rule] }
      else source := { source with rules := source.rules ++ [rule] }
    return ⟨version, releaseName, table, tableHandle, 1, destination, source⟩
  | _ => throw "Supply metainfo, one table, two NAT chains, and their ordered rules."

def parse (text : String) : Except String Snapshot := do
  fromJson (← Json.parse text)

end Snapshot
end Netlib.Import.NftablesNAT
