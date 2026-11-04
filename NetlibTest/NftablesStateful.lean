import Netlib.Import.NftablesStateful

namespace NetlibTest.NftablesStateful

open Netlib Netlib.Packet Netlib.Import.NftablesStateful
open StatefulACL (CTState)

private def object (fields : List (String × Lean.Json)) : Lean.Json := Lean.Json.mkObj fields
private def string (value : String) : Lean.Json := .str value
private def number (value : Nat) : Lean.Json := Lean.toJson value
private def array (values : List Lean.Json) : Lean.Json := .arr values.toArray

private def metadata : Lean.Json :=
  object [("metainfo", object [("version", string "1.1.3"),
    ("release_name", string "source-derived fixture"), ("json_schema_version", number 1)])]

private def table : Lean.Json :=
  object [("table", object [("family", string "ip"), ("name", string "filter"), ("handle", number 1)])]

private def chain (policy : String := "drop") (hook : String := "forward") (priority : Int := 0) : Lean.Json :=
  object [("chain", object [("family", string "ip"), ("table", string "filter"),
    ("name", string "forward"), ("handle", number 2), ("type", string "filter"),
    ("hook", string hook), ("prio", Lean.toJson priority), ("policy", string policy)])]

private def rule (handle : Nat) (expressions : List Lean.Json) : Lean.Json :=
  object [("rule", object [("family", string "ip"), ("table", string "filter"),
    ("chain", string "forward"), ("handle", number handle), ("expr", array expressions),
    ("comment", string s!"flow-rule-{handle}")])]

private def snapshot (rules : List Lean.Json) (policy : String := "drop")
    (hook : String := "forward") (priority : Int := 0) : Lean.Json :=
  object [("nftables", array ([metadata, table, chain policy hook priority] ++ rules))]

private def comparison (left right : Lean.Json) (operator : String := "==") : Lean.Json :=
  object [("match", object [("op", string operator), ("left", left), ("right", right)])]

private def ct (right : Lean.Json) (operator : String := "in") (key : String := "state")
    (extra : List (String × Lean.Json) := []) : Lean.Json :=
  comparison (object [("ct", object ([("key", string key)] ++ extra))]) right operator

private def payload (protocol field : String) (right : Lean.Json) : Lean.Json :=
  comparison (object [("payload", object [("protocol", string protocol), ("field", string field)])]) right

private def anonymousSet (values : List Lean.Json) : Lean.Json := object [("set", array values)]
private def accept : Lean.Json := object [("accept", .null)]
private def drop : Lean.Json := object [("drop", .null)]

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def reject (result : Except String α) (label : String) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"Expected a stateful nftables input error: {label}")
  | .error _ => pure ()

private def states : List CTState := [.new, .established, .related, .invalid, .untracked]

private def header (protocol : Protocol := Protocol.tcp) (port : Port := 443) : Header :=
  ⟨167772161, 3325256706, protocol, 50000, port⟩

private def positiveTests : IO Unit := do
  let json := snapshot [
    rule 3 [ct (string "invalid"), drop],
    rule 4 [ct (anonymousSet [string "established", string "related"]) "==", accept],
    rule 5 [payload "ip" "saddr" (string "10.0.0.0/24"), ct (string "new"),
      payload "tcp" "dport" (number 443), accept]]
  let source ← unwrap (Snapshot.parse json.compress)
  ensure (source.version == "1.1.3" && source.table == "filter" && source.chain == "forward" &&
    source.hook == "forward" && source.priority == 0 && source.tableIndex == 1 && source.chainIndex == 2 &&
    source.tableHandle == 1 && source.chainHandle == 2)
    "The stateful profile changed table or chain provenance."
  ensure (source.rules.length == 3 && source.compile.length == 4 &&
    source.policySourceID == "nftables[2].chain.policy")
    "The stateful profile lost rule order or the explicit chain policy."
  ensure (source.compile.allows .new header && source.compile.allows .established header &&
    source.compile.allows .related header && !(source.compile.allows .invalid header) &&
    !(source.compile.allows .untracked header))
    "The filter changed its state-selection behavior."
  ensure (!(source.compile.allows .new (header Protocol.udp)) &&
    !(source.compile.allows .new (header Protocol.tcp 80)) &&
    !(source.compile.allows .new { header with source := 167772417 }))
    "The state predicate erased a header or implied protocol guard."
  ensure (source.compile.allows .established (header Protocol.udp 53))
    "An established-only rule acquired an undeclared header restriction."
  let selected ← match source.rules[2]? with
    | none => throw (IO.userError "The new-flow rule is missing.")
    | some selected => pure selected
  ensure (selected.objectIndex == 5 && selected.handle == 5 && selected.verdictIndex == 3 &&
    selected.expressionIndices == [0, 1, 2, 3] && selected.stateExpressionIndex == some 1 &&
    selected.stateSourceID == some "nftables[5].rule.handle[5].expr[1]" &&
    selected.comment == some "flow-rule-5" && selected.protocol == some Protocol.tcp)
    "The rule lost source indices, comment, or implied protocol."
  let allowDefault ← unwrap (Snapshot.fromJson (snapshot [] "accept"))
  let denyDefault ← unwrap (Snapshot.fromJson (snapshot []))
  let ordered ← unwrap (Snapshot.fromJson (snapshot [rule 3 [ct (string "established"), drop], rule 4 [accept]]))
  for state in states do
    ensure (allowDefault.compile.allows state header && !(denyDefault.compile.allows state header))
      "The chain policy failed to apply to every state."
    ensure (ordered.compile.allows state header == (state != .established))
      "The first state match did not take precedence."
    for protocol in [Protocol.tcp, Protocol.udp, Protocol.icmp] do
      for port in [0, 53, 80, 443, 65535] do
        for source in [source, allowDefault, denyDefault, ordered] do
          let packet := header protocol port
          ensure (source.compile.allows state packet == source.permits state packet)
            "The compiled filter differs from its independent source semantics."
          ensure (StatefulACL.Policy.evaluate .permit source.compile state packet == source.evaluate state packet)
            "A caller fallback overrode the explicit chain policy."
  let postrouting ← unwrap (Snapshot.fromJson (snapshot [rule 3 [ct (string "new"), drop]] "accept" "postrouting" 200))
  ensure (postrouting.hook == "postrouting" && postrouting.priority == 200 &&
    !(postrouting.compile.allows .new header) && postrouting.compile.allows .established header)
    "The postrouting filter lost its hook, priority, or state decision."
  reject (Import.Nftables.Snapshot.fromJson (snapshot [] "drop" "postrouting" 200))
    "the stateless profile must remain forward-only"
  reject (Import.Nftables.Snapshot.fromJson json) "the stateless profile must reject ct predicates"

private def stateFormTests : IO Unit := do
  let forms := [
    ct (string "new"), ct (string "new") "==",
    ct (array [string "new", string "established"]),
    ct (anonymousSet [string "new", string "established"]) "==",
    ct (anonymousSet [string "new", string "established"]) "in"]
  for (form, index) in forms.zipIdx do
    let parsed ← unwrap (Snapshot.fromJson (snapshot [rule 3 [form, accept]]))
    for state in states do
      ensure (parsed.compile.allows state header ==
        (state == .new || (2 ≤ index && state == .established)))
        "A native state scalar, list, or anonymous set changed meaning."
  for name in ["new", "established", "related", "invalid", "untracked"] do
    let parsed ← unwrap (Snapshot.fromJson (snapshot [rule 3 [ct (string name), accept]]))
    ensure ((states.filter (fun state => parsed.compile.allows state header)).length == 1)
      "A single state selected multiple classifications."
  for (value, expected) in [(1, CTState.invalid), (2, .established), (4, .related), (8, .new), (64, .untracked)] do
    for operator in ["in", "=="] do
      let parsed ← unwrap (Snapshot.fromJson (snapshot [rule 3 [ct (number value) operator, accept]]))
      for state in states do
        ensure (parsed.compile.allows state header == (state == expected))
          "A native numeric state bit changed classification."
  let mask ← unwrap (Snapshot.fromJson (snapshot [rule 3 [ct (number 10), accept]]))
  let all ← unwrap (Snapshot.fromJson (snapshot [rule 3 [ct (number 79), accept]]))
  for state in states do
    ensure (mask.compile.allows state header == (state == .new || state == .established) &&
      all.compile.allows state header) "A native numeric state mask changed membership."
  let legacy := snapshot [rule 3 [payload "udp" "dport" (number 53), accept]]
  let stateless ← unwrap (Import.Nftables.Snapshot.fromJson legacy)
  let stateful ← unwrap (Snapshot.fromJson legacy)
  for state in states do
    for packet in [header Protocol.udp 53, header Protocol.tcp 53, header Protocol.udp 80] do
      ensure (stateful.compile.allows state packet == stateless.compile.allows packet)
        "The shared header parser changed a stateless rule."
  let before ← unwrap (Snapshot.fromJson (snapshot [rule 3 [ct (string "new"), payload "tcp" "dport" (number 443), accept]]))
  let after ← unwrap (Snapshot.fromJson (snapshot [rule 3 [payload "tcp" "dport" (number 443), ct (string "new"), accept]]))
  for state in states do
    for packet in [header, header Protocol.udp, header Protocol.tcp 80] do
      ensure (before.compile.allows state packet == after.compile.allows state packet)
        "Pure match ordering changed conjunction semantics."

private def rejectionTests : IO Unit := do
  for (label, expression) in [
      ("unknown state", ct (string "authorized")),
      ("unknown numeric state bit", ct (number 16)), ("boolean state", ct (.bool true)),
      ("zero state mask", ct (number 0)), ("mixed unknown mask", ct (number 24)),
      ("large state mask", ct (number 128)), ("multi-bit equality", ct (number 10) "=="),
      ("multi-bit set element", ct (anonymousSet [number 10]) "=="),
      ("null state", ct .null), ("named set", ct (string "@states")),
      ("empty list", ct (array [])), ("empty set", ct (anonymousSet []) "=="),
      ("duplicate list state", ct (array [string "new", string "new"])),
      ("duplicate set state", ct (anonymousSet [string "new", string "new"]) "=="),
      ("mixed list", ct (array [string "new", number 8])),
      ("nested list", ct (array [array [string "new"]])),
      ("bare-list equality", ct (array [string "new", string "established"]) "=="),
      ("inequality", ct (string "new") "!="), ("ordering", ct (string "new") "<"),
      ("implicit operator", ct (string "new") ""),
      ("status key", ct (string "assured") "in" "status"),
      ("direction key", ct (string "original") "==" "direction"),
      ("state direction attribute", ct (string "new") "in" "state" [("dir", string "original")]),
      ("state family attribute", ct (string "new") "in" "state" [("family", string "ip")]),
      ("set extra field", ct (object [("set", array [string "new"]), ("flags", array [])]) "=="),
      ("nonarray set", ct (object [("set", string "new")]) "==") ] do
    reject (Snapshot.fromJson (snapshot [rule 3 [expression, accept]])) label
  for (label, expressions) in [
      ("repeated identical state match", [ct (string "new"), ct (string "new"), accept]),
      ("repeated conflicting state match", [ct (string "new"), ct (string "established"), accept]),
      ("state match after verdict", [accept, ct (string "new")]),
      ("missing verdict", [ct (string "new")]),
      ("multiple verdicts", [ct (string "new"), accept, drop]),
      ("unsupported counter", [ct (string "new"), object [("counter", .null)], accept]),
      ("conflicting implied protocols", [ct (string "new"), payload "tcp" "sport" (number 1),
        payload "udp" "dport" (number 2), accept]),
      ("header list extension", [ct (string "new"), payload "tcp" "dport" (array [number 80, number 443]), accept]) ] do
    reject (Snapshot.fromJson (snapshot [rule 3 expressions])) label
  for hook in ["input", "output", "prerouting", "ingress", "unknown"] do
    reject (Snapshot.fromJson (snapshot [] "drop" hook)) s!"unsupported hook {hook}"
  reject (Snapshot.fromJson (snapshot [rule 3 [accept], rule 3 [drop]])) "duplicate rule handle"
  reject (Snapshot.fromJson (snapshot [rule 0 [accept]])) "zero rule handle"
  for (old, replacement) in [
      ("\"1.1.3\"", "\"1.1.4\""),
      ("\"json_schema_version\":1", "\"json_schema_version\":2"),
      ("\"family\":\"ip\"", "\"family\":\"inet\""),
      ("\"type\":\"filter\"", "\"type\":\"nat\""),
      ("\"prio\":0", "\"prio\":2147483648"),
      ("\"prio\":0", "\"prio\":-2147483649") ] do
    reject (Snapshot.parse ((snapshot []).compress.replace old replacement)) s!"invalid envelope {replacement}"
  let text := (snapshot [rule 3 [ct (string "new"), accept]]).compress
  for duplicate in ["\"key\":\"state\",\"key\":\"status\"", "\"key\":\"state\",\"\\u006bey\":\"status\""] do
    reject (Snapshot.parse (text.replace "\"key\":\"state\"" duplicate)) "duplicate decoded expression key"
  match Snapshot.fromJson (snapshot [rule 3 [ct (string "new"), ct (string "established"), accept]]) with
  | .ok _ => throw (IO.userError "Repeated state predicates were accepted.")
  | .error message =>
    ensure ((message.splitOn "nftables[3].rule.handle[3].expr[1]").length > 1)
      "The rejected state predicate lost expression provenance."

example (source : SourceRule) (state : CTState) (header : Header) :
    source.compile.accepts state header = source.accepts state header := source.compile_accepts state header

example (source : Snapshot) (state : CTState) (header : Header) :
    source.compile.allows state header = source.permits state header := source.compile_allows state header

private def capturedTests : IO Unit := do
  let read (name : String) : IO Snapshot := do
    unwrap (Snapshot.parse (← IO.FS.readFile s!"examples/lifecycle/native/{name}.json"))
  let initial ← read "forward-initial"
  let replyDrop ← read "forward-drop-reply"
  let establishedOnly ← read "forward-established-only"
  let late ← read "late"
  let original : Header := ⟨3221225986, 3325256706, 17, 31000, 9000⟩
  let reply : Header := ⟨3325256706, 3221225986, 17, 9000, 31000⟩
  ensure (initial.hook == "forward" && initial.priority == 0 &&
    initial.compile.allows .new original && !(initial.compile.allows .invalid original) &&
    initial.compile.allows .established reply)
    "The genuine initial filter lost header or state conditions."
  ensure (!(replyDrop.compile.allows .established reply) &&
    replyDrop.compile.allows .established original && !(replyDrop.compile.allows .new original))
    "The genuine reply-drop update changed first-match precedence."
  ensure (establishedOnly.compile.allows .established original &&
    !(establishedOnly.compile.allows .new original))
    "The genuine established-only update admitted a fresh classification."
  ensure (late.hook == "postrouting" && late.priority == 200 &&
    !(late.compile.allows .new { original with destinationPort := 9001 }) &&
    late.compile.allows .new original)
    "The genuine late filter lost its stage or drop condition."
  ensure (initial.rules.map (·.comment) ==
    [some "ESTABLISHED", some "SERVICE", some "LATE_INPUT", some "FORWARD_DROP"])
    "The genuine filter lost rule comments or order."

def run : IO Unit := do
  positiveTests
  stateFormTests
  rejectionTests
  capturedTests
  IO.println "Stateful nftables import tests passed."

end NetlibTest.NftablesStateful
