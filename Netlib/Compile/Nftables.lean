import Netlib.Compile.ACL
import Netlib.Import.Nftables

namespace Netlib.Compile.Nftables

open Packet
open Netlib.Import.Nftables (SourceRule Snapshot)

private def validPorts : Option PortRange → Bool
  | none => true
  | some range => decide (range.first ≤ range.last)

/-- Native transport payload matches require an explicit TCP or UDP protocol. -/
def capable (test : Match) : Bool :=
  (!(test.sourcePorts.isSome || test.destinationPorts.isSome) ||
    test.protocol == some Protocol.tcp || test.protocol == some Protocol.udp) &&
  validPorts test.sourcePorts && validPorts test.destinationPorts

private def predicateCount (test : Match) : Nat :=
  test.source.toList.length + test.destination.toList.length + test.protocol.toList.length +
    test.sourcePorts.toList.length + test.destinationPorts.toList.length

def sourceRule (index : Nat) (entry : ACL.Entry) : SourceRule where
  source := entry.rule.test.source
  destination := entry.rule.test.destination
  protocol := entry.rule.test.protocol
  sourcePorts := entry.rule.test.sourcePorts
  destinationPorts := entry.rule.test.destinationPorts
  action := entry.rule.action
  objectIndex := index
  expressionIndices := List.range (predicateCount entry.rule.test + 1)
  verdictIndex := predicateCount entry.rule.test
  handle := index
  sourceID := entry.requirementId
  comment := some entry.requirementId

theorem sourceRule_compile (index : Nat) (entry : ACL.Entry) :
    (sourceRule index entry).compile = entry.rule := rfl

private def sourceRules : Nat → List ACL.Entry → List SourceRule
  | _, [] => []
  | index, entry :: entries => sourceRule index entry :: sourceRules (index + 1) entries

private theorem sourceRules_compile (index : Nat) (entries : List ACL.Entry) :
    (sourceRules index entries).map SourceRule.compile = entries.map ACL.Entry.rule := by
  induction entries generalizing index with
  | nil => rfl
  | cons entry entries ih => simp only [sourceRules, List.map_cons, sourceRule_compile, ih]

def makeSnapshot (entries : List ACL.Entry) : Snapshot where
  version := Netlib.Import.Nftables.referenceVersion
  releaseName := "Netlib compiler"
  table := "netlib"
  chain := "forward"
  tableHandle := 1
  chainHandle := 2
  tableIndex := 1
  chainIndex := 2
  priority := 0
  policy := .deny
  rules := sourceRules 3 entries

theorem makeSnapshot_allows (entries : List ACL.Entry) (header : Header) :
    (makeSnapshot entries).compile.allows header = Packet.ACL.allows (entries.map ACL.Entry.rule) header := by
  simp only [Snapshot.compile, makeSnapshot, sourceRules_compile, Packet.ACL.allows,
    Packet.ACL.evaluate_append]
  rfl

theorem makeSnapshot_permits (entries : List ACL.Entry) (header : Header) :
    (makeSnapshot entries).permits header = Packet.ACL.allows (entries.map ACL.Entry.rule) header := by
  rw [← Snapshot.compile_allows, makeSnapshot_allows]

structure Emitted (intents : List ACL.Intent) where
  compiled : ACL.Certified intents
  supported : ∀ intent ∈ intents, capable intent.test = true
  comments : ∀ intent ∈ intents, intent.id.utf8ByteSize ≤ 128

namespace Emitted

def snapshot (emitted : Emitted intents) : Snapshot := makeSnapshot emitted.compiled.entries

def requirementIds (emitted : Emitted intents) : List String := emitted.compiled.requirementIds

theorem permits_eq (emitted : Emitted intents) (header : Header) :
    emitted.snapshot.permits header = emitted.compiled.rules.allows header :=
  makeSnapshot_permits emitted.compiled.entries header

theorem compiled_eq (emitted : Emitted intents) (header : Header) :
    emitted.snapshot.compile.allows header = emitted.compiled.rules.allows header :=
  makeSnapshot_allows emitted.compiled.entries header

theorem correct (emitted : Emitted intents) (header : Header) :
    emitted.snapshot.permits header = true ↔ ACL.Meaning intents header := by
  rw [emitted.permits_eq]
  exact emitted.compiled.correct header

end Emitted

inductive Error (intents : List ACL.Intent) where
  | intent (error : ACL.Error intents)
  | unsupported (id : String)
  | longId (id : String)

def Error.describe : Error intents → String
  | .intent error => error.describe
  | .unsupported id => s!"Intent {id} needs explicit TCP/UDP port matches and ordered port bounds."
  | .longId id => s!"Intent ID {id} exceeds the 128-byte native comment limit."

def compile (intents : List ACL.Intent) (budget : Nat := 100000) :
    Except (Error intents) (Emitted intents) := do
  let compiled ← (ACL.compile intents budget).mapError Error.intent
  match oversized : intents.find? (fun intent => decide (128 < intent.id.utf8ByteSize)) with
  | some intent => .error (.longId intent.id)
  | none =>
    match unsupported : intents.find? (fun intent => !capable intent.test) with
    | some intent => .error (.unsupported intent.id)
    | none => .ok ⟨compiled, by
        intro intent member
        have missing := (List.find?_eq_none.mp unsupported) intent member
        cases accepted : capable intent.test <;> simp_all, by
        intro intent member
        have bounded := (List.find?_eq_none.mp oversized) intent member
        simp only [decide_eq_true_eq] at bounded
        omega⟩

private def addressText (value : Nat) : String :=
  s!"{value / 16777216}.{value / 65536 % 256}.{value / 256 % 256}.{value % 256}"

private def prefixJson (block : Prefix) : Lean.Json :=
  Lean.Json.mkObj [("prefix", Lean.Json.mkObj [
    ("addr", Lean.toJson (addressText block.lower)), ("len", Lean.toJson block.length.val)])]

private def portsJson (ports : PortRange) : Lean.Json :=
  if ports.first = ports.last then Lean.toJson ports.first.val
  else Lean.Json.mkObj [("range", Lean.toJson [ports.first.val, ports.last.val])]

private def matchJson (left right : Lean.Json) : Lean.Json :=
  Lean.Json.mkObj [("match", Lean.Json.mkObj [
    ("op", Lean.toJson "=="), ("left", left), ("right", right)])]

private def payload (protocol field : String) : Lean.Json :=
  Lean.Json.mkObj [("payload", Lean.Json.mkObj [
    ("protocol", Lean.toJson protocol), ("field", Lean.toJson field)])]

private def expressions (rule : SourceRule) : List Lean.Json :=
  (rule.source.toList.map (fun block => matchJson (payload "ip" "saddr") (prefixJson block))) ++
  (rule.destination.toList.map (fun block => matchJson (payload "ip" "daddr") (prefixJson block))) ++
  (rule.protocol.toList.map (fun protocol => matchJson
    (Lean.Json.mkObj [("meta", Lean.Json.mkObj [("key", Lean.toJson "l4proto")])])
    (Lean.toJson protocol.val))) ++
  (rule.sourcePorts.toList.map (fun ports => matchJson
    (payload (if rule.protocol == some Protocol.udp then "udp" else "tcp") "sport") (portsJson ports))) ++
  (rule.destinationPorts.toList.map (fun ports => matchJson
    (payload (if rule.protocol == some Protocol.udp then "udp" else "tcp") "dport") (portsJson ports))) ++
  [Lean.Json.mkObj [(if rule.action = .permit then "accept" else "drop", .null)]]

private def ruleJson (table chain : String) (rule : SourceRule) : Lean.Json :=
  Lean.Json.mkObj [("rule", Lean.Json.mkObj [
    ("family", Lean.toJson "ip"), ("table", Lean.toJson table), ("chain", Lean.toJson chain),
    ("handle", Lean.toJson rule.handle), ("comment", Lean.toJson rule.sourceID),
    ("expr", Lean.toJson (expressions rule))])]

namespace Emitted

/-- Bare snapshot objects use implicit adds. Handles describe the emitted snapshot. -/
def toJson (emitted : Emitted intents) : Lean.Json :=
  let snapshot := emitted.snapshot
  Lean.Json.mkObj [("nftables", Lean.toJson ([
    Lean.Json.mkObj [("metainfo", Lean.Json.mkObj [
      ("version", Lean.toJson snapshot.version), ("release_name", Lean.toJson snapshot.releaseName),
      ("json_schema_version", Lean.toJson (1 : Nat))])],
    Lean.Json.mkObj [("table", Lean.Json.mkObj [
      ("family", Lean.toJson "ip"), ("name", Lean.toJson snapshot.table),
      ("handle", Lean.toJson snapshot.tableHandle)])],
    Lean.Json.mkObj [("chain", Lean.Json.mkObj [
      ("family", Lean.toJson "ip"), ("table", Lean.toJson snapshot.table), ("name", Lean.toJson snapshot.chain),
      ("handle", Lean.toJson snapshot.chainHandle), ("type", Lean.toJson "filter"), ("hook", Lean.toJson "forward"),
      ("prio", Lean.toJson snapshot.priority), ("policy", Lean.toJson "drop")])]] ++
    snapshot.rules.map (ruleJson snapshot.table snapshot.chain))) ]

end Emitted
end Netlib.Compile.Nftables
