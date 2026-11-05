import Netlib.Import.NftablesNAT
import Netlib.Import.ConntrackNetlink

namespace NetlibTest.NftablesNAT

open Netlib Netlib.Packet Netlib.Import.NftablesNAT

private def object (fields : List (String × Lean.Json)) : Lean.Json := Lean.Json.mkObj fields
private def string (value : String) : Lean.Json := .str value
private def number (value : Nat) : Lean.Json := Lean.toJson value
private def array (values : List Lean.Json) : Lean.Json := .arr values.toArray

private def metadata : Lean.Json :=
  object [("metainfo", object [("version", string "1.1.3"),
    ("release_name", string "source-derived fixture"), ("json_schema_version", number 1)])]

private def table : Lean.Json :=
  object [("table", object [("family", string "ip"), ("name", string "nat"), ("handle", number 1)])]

private def chain (name hook : String) (priority : Int) (handle : Nat) : Lean.Json :=
  object [("chain", object [("family", string "ip"), ("table", string "nat"),
    ("name", string name), ("handle", number handle), ("type", string "nat"),
    ("hook", string hook), ("prio", Lean.toJson priority), ("policy", string "accept")])]

private def destinationChain : Lean.Json := chain "destination" "prerouting" (-100) 1
private def sourceChain : Lean.Json := chain "source" "postrouting" 100 2

private def rule (name : String) (handle : Nat) (expressions : List Lean.Json) : Lean.Json :=
  object [("rule", object [("family", string "ip"), ("table", string "nat"),
    ("chain", string name), ("handle", number handle), ("expr", array expressions),
    ("comment", string s!"nat-rule-{handle}")])]

private def snapshot (rules : List Lean.Json) : Lean.Json :=
  object [("nftables", array ([metadata, table, destinationChain, sourceChain] ++ rules))]

private def payload (protocol field : String) (right : Lean.Json) : Lean.Json :=
  object [("match", object [("op", string "=="),
    ("left", object [("payload", object [("protocol", string protocol), ("field", string field)])]),
    ("right", right)])]

private def target (kind address : String) (port : Option Nat := none) : Lean.Json :=
  object [(kind, object ([("addr", string address)] ++
    (port.toList.map fun value => ("port", number value))))]

private def original : Header := ⟨3221225986, 3405803778, 17, 31000, 8080⟩
private def afterDestination : Header := { original with destination := 3325256706, destinationPort := 9000 }
private def wire : Header := { afterDestination with source := 3405803777, sourcePort := 40000 }

private def destinationRule (handle : Nat := 3) (address : String := "198.51.100.2")
    (port : Nat := 9000) : Lean.Json :=
  rule "destination" handle [payload "ip" "daddr" (string "203.0.113.2"),
    payload "udp" "dport" (number 8080), target "dnat" address (some port)]

private def sourceRule (handle : Nat := 4) : Lean.Json :=
  rule "source" handle [payload "ip" "daddr" (string "198.51.100.2"),
    payload "udp" "sport" (number 31000), target "snat" "203.0.113.1" (some 40000)]

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def reject (result : Except String α) (label : String) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"Expected a fixed NAT input error: {label}")
  | .error _ => pure ()

private def positiveTests : IO Unit := do
  let parsed ← unwrap (Snapshot.parse (snapshot [sourceRule, destinationRule]).compress)
  ensure (parsed.version == "1.1.3" && parsed.table == "nat" && parsed.tableHandle == 1 &&
    parsed.destinationChain.hook == "prerouting" && parsed.destinationChain.priority == -100 &&
    parsed.sourceChain.hook == "postrouting" && parsed.sourceChain.priority == 100)
    "The NAT profile lost table, hook, or priority metadata."
  ensure (parsed.destination original == afterDestination && parsed.source afterDestination == wire &&
    parsed.translated original == wire && parsed.source original == original)
    "The source stage did not read the header produced by the destination stage."
  let destination ← match parsed.destinationChain.rules with
    | [selected] => pure selected
    | _ => throw (IO.userError "The destination rule was lost.")
  ensure (destination.objectIndex == 5 && destination.verdictIndex == 2 &&
    destination.expressionIndices == [0, 1, 2] && destination.handle == 3 &&
    destination.sourceID == "nftables[5].rule.handle[3]" && destination.comment == some "nat-rule-3")
    "The interleaved NAT rules lost source provenance."
  let candidate := parsed.candidate 0 original
  ensure (candidate.flow.original == original && candidate.flow.reply == wire.reverse &&
    candidate.flow.remainingTTL == 0 && candidate.sourceNAT && candidate.destinationNAT && candidate.check)
    "The candidate lost its tuple equations, minimal flags, or compatibility."
  let empty ← unwrap (Snapshot.fromJson (snapshot []))
  let untouched := empty.candidate 0 original
  ensure (empty.translated original == original && !untouched.sourceNAT &&
    !untouched.destinationNAT && untouched.check)
    "An unmatched NAT stage changed the packet or selected a NAT operation."
  let identity := destinationRule 3 "203.0.113.2" 8080
  let firstIdentity ← unwrap (Snapshot.fromJson (snapshot [identity, destinationRule 4]))
  ensure (firstIdentity.destination original == original &&
    !(firstIdentity.candidate 0 original).destinationNAT)
    "A matching identity target incorrectly continued to a later rule."
  let addressOnly ← unwrap (Snapshot.fromJson (snapshot [
    rule "destination" 3 [target "dnat" "198.51.100.2"],
    rule "source" 4 [target "snat" "203.0.113.1"]]))
  ensure ((addressOnly.translated original).sourcePort == original.sourcePort &&
    (addressOnly.translated original).destinationPort == original.destinationPort)
    "An absent NAT port did not preserve the incoming port."
  let swapped := object [("nftables", array [metadata, table, sourceChain, destinationChain, destinationRule])]
  let swapped ← unwrap (Snapshot.fromJson swapped)
  ensure (swapped.destinationChain.objectIndex == 3 && swapped.sourceChain.objectIndex == 2 &&
    swapped.destination original == afterDestination)
    "Chain declaration order changed stage identity or provenance."
  let symmetric : Header := ⟨0, 0, 17, 1, 1⟩
  ensure (!(empty.candidate 0 symmetric).check)
    "A same-zone symmetric tuple pair passed the core ambiguity check."
  for packet in [original, { original with sourcePort := 31001 },
      { original with destinationPort := 8081 }, { original with protocol := Protocol.tcp }] do
    ensure (parsed.destination packet == evaluateRules parsed.destinationChain.rules packet &&
      parsed.source packet == evaluateRules parsed.sourceChain.rules packet &&
      (parsed.translated packet).protocol == packet.protocol)
      "Compiled first-match rewriting differs from source semantics."

private def rejectionTests : IO Unit := do
  let valid := (snapshot [destinationRule, sourceRule]).compress
  for (label, old, replacement) in [
      ("wrong version", "\"1.1.3\"", "\"1.1.4\""),
      ("wrong schema", "\"json_schema_version\":1", "\"json_schema_version\":2"),
      ("wrong family", "\"family\":\"ip\"", "\"family\":\"inet\""),
      ("wrong chain type", "\"type\":\"nat\"", "\"type\":\"filter\""),
      ("wrong destination priority", "\"prio\":-100", "\"prio\":-99"),
      ("wrong source priority", "\"prio\":100", "\"prio\":101"),
      ("wrong hook", "\"hook\":\"prerouting\"", "\"hook\":\"input\""),
      ("drop policy", "\"policy\":\"accept\"", "\"policy\":\"drop\""),
      ("foreign rule table", "\"table\":\"nat\"", "\"table\":\"other\""),
      ("oversized target port", "\"port\":9000", "\"port\":65536"),
      ("invalid target address", "\"addr\":\"198.51.100.2\"", "\"addr\":\"198.51.100.256\""),
      ("address prefix target", "\"addr\":\"198.51.100.2\"", "\"addr\":\"198.51.100.0/24\""),
      ("IPv6 target", "\"addr\":\"198.51.100.2\"", "\"addr\":\"2001:db8::1\""),
      ("duplicate decoded target key", "\"addr\":\"198.51.100.2\"",
        "\"addr\":\"198.51.100.2\",\"\\u0061ddr\":\"198.51.100.3\"") ] do
    reject (Snapshot.parse (valid.replace old replacement)) label
  for (label, json) in [
      ("missing chain", object [("nftables", array [metadata, table, destinationChain])]),
      ("extra chain", snapshot [sourceChain]),
      ("duplicate chain kind", object [("nftables", array [metadata, table, destinationChain, destinationChain])]),
      ("duplicate rule handle", snapshot [destinationRule, sourceRule 3]),
      ("zero rule handle", snapshot [destinationRule 0]),
      ("unknown rule chain", snapshot [rule "other" 3 [target "dnat" "198.51.100.2"]]),
      ("wrong target hook", snapshot [rule "destination" 3 [target "snat" "198.51.100.2"]]),
      ("missing target", snapshot [rule "destination" 3 [payload "udp" "dport" (number 8080)]]),
      ("match after target", snapshot [rule "destination" 3 [target "dnat" "198.51.100.2", payload "udp" "dport" (number 8080)]]),
      ("two targets", snapshot [rule "destination" 3 [target "dnat" "198.51.100.2", target "dnat" "198.51.100.3"]]),
      ("accept verdict", snapshot [rule "destination" 3 [object [("accept", .null)]]]),
      ("masquerade", snapshot [rule "source" 3 [object [("masquerade", .null)]]]),
      ("ct selector", snapshot [rule "source" 3 [object [("match", object [("op", string "in"),
        ("left", object [("ct", object [("key", string "state")])]), ("right", number 8)])], target "snat" "203.0.113.1"]]),
      ("target flags", snapshot [rule "source" 3 [object [("snat", object [("addr", string "203.0.113.1"),
        ("flags", array [string "persistent"])])]]]),
      ("target range", snapshot [rule "source" 3 [object [("snat", object [("addr", object [
        ("range", array [string "203.0.113.1", string "203.0.113.2"])])])]]]),
      ("port range", snapshot [rule "source" 3 [object [("snat", object [("addr", string "203.0.113.1"),
        ("port", object [("range", array [number 40000, number 40001])])])]]]),
      ("missing address", snapshot [rule "source" 3 [object [("snat", object [("port", number 40000)])]]]),
      ("null port", snapshot [rule "source" 3 [object [("snat", object [("addr", string "203.0.113.1"), ("port", .null)])]]]) ] do
    reject (Snapshot.fromJson json) label
  match Snapshot.fromJson (snapshot [rule "source" 3 [object [("snat", object [
      ("addr", string "203.0.113.1"), ("port", number 65536)])]]]) with
  | .ok _ => throw (IO.userError "An oversized NAT port was accepted.")
  | .error message =>
    ensure ((message.splitOn "nftables[4].rule.handle[3].expr[0]").length > 1)
      "The NAT error lost its expression provenance."

private def capturedTests : IO Unit := do
  let initial ← unwrap (Snapshot.parse (← IO.FS.readFile "examples/lifecycle/native/nat-initial.json"))
  let changed ← unwrap (Snapshot.parse (← IO.FS.readFile "examples/lifecycle/native/nat-changed.json"))
  ensure (initial.destination original == afterDestination && initial.translated original == wire &&
    (changed.destination original).destinationPort == 9003 &&
    (changed.translated original).sourcePort == 40001)
    "The genuine NAT exports lost fixed endpoints or their update."
  let first := initial.candidate 0 original
  let second := initial.candidate 0 { original with sourcePort := 31001 }
  ensure (first.check && second.check && first.flow.reply == second.flow.reply &&
    !(Protocol.FlowNAT.Snapshot.check ⟨[first.flow, second.flow]⟩))
    "Fixed-target proposals were incorrectly treated as a collision-free allocator."
  let opened ← unwrap (Import.ConntrackNetlink.Snapshot.parse
    (← IO.FS.readFile "examples/lifecycle/native/opened-state.json"))
  let updated ← unwrap (Import.ConntrackNetlink.Snapshot.parse
    (← IO.FS.readFile "examples/lifecycle/native/updated-state.json"))
  for captured in [opened, updated] do
    let row ← match captured.entries.find? (·.entry.flow.original == original) with
      | none => throw (IO.userError "The genuine original flow is missing.")
      | some row => pure row
    ensure (row.entry.flow.reply == first.flow.reply && row.entry.sourceNAT && row.entry.destinationNAT &&
      row.entry.flow.reply != (changed.candidate 0 original).flow.reply)
      "The retained binding did not preserve its original NAT tuple after the rules changed."

example (snapshot : Snapshot) (packet : Header) :
    snapshot.destination packet = evaluateRules snapshot.destinationChain.rules packet :=
  snapshot.destination_correct packet

example (snapshot : Snapshot) (zone : Nat) (packet : Header)
    (supported : packet.protocol = Protocol.tcp ∨ packet.protocol = Protocol.udp)
    (zoneBound : zone < 65536) (distinct : packet ≠ (snapshot.translated packet).reverse) :
    (snapshot.candidate zone packet).Compatible :=
  snapshot.candidate_compatible zone packet supported zoneBound distinct

def run : IO Unit := do
  positiveTests
  rejectionTests
  capturedTests
  IO.println "Fixed nftables NAT import tests passed."

end NetlibTest.NftablesNAT
