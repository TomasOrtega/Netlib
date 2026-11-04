import Netlib.Import.Nftables

namespace NetlibTest.Nftables

open Netlib
open Netlib.Packet
open Netlib.Import.Nftables

private def object (fields : List (String × Lean.Json)) : Lean.Json := Lean.Json.mkObj fields
private def string (value : String) : Lean.Json := .str value
private def number (value : Nat) : Lean.Json := Lean.toJson value
private def array (values : List Lean.Json) : Lean.Json := .arr values.toArray

private def metadata (version : String := "1.1.3") (schema : Nat := 1) : Lean.Json :=
  object [("metainfo", object [("version", string version), ("release_name", string "test fixture"),
    ("json_schema_version", number schema)])]

private def table (family : String := "ip") (extra : List (String × Lean.Json) := []) : Lean.Json :=
  object [("table", object ([("family", string family), ("name", string "filter"), ("handle", number 1)] ++ extra))]

private def chain (policy : String := "drop") (hook : String := "forward")
    (extra : List (String × Lean.Json) := []) : Lean.Json :=
  object [("chain", object ([("family", string "ip"), ("table", string "filter"),
    ("name", string "forward"), ("handle", number 2), ("type", string "filter"),
    ("hook", string hook), ("prio", number 0), ("policy", string policy)] ++ extra))]

private def rule (handle : Nat) (expressions : List Lean.Json)
    (extra : List (String × Lean.Json) := []) : Lean.Json :=
  object [("rule", object ([("family", string "ip"), ("table", string "filter"),
    ("chain", string "forward"), ("handle", number handle), ("expr", array expressions)] ++ extra))]

private def snapshot (rules : List Lean.Json) (policy : String := "drop") : Lean.Json :=
  object [("nftables", array ([metadata, table, chain policy] ++ rules))]

private def comparison (left right : Lean.Json) (operator : String := "==") : Lean.Json :=
  object [("match", object [("op", string operator), ("left", left), ("right", right)])]

private def payload (protocol field : String) (right : Lean.Json) : Lean.Json :=
  comparison (object [("payload", object [("protocol", string protocol), ("field", string field)])]) right

private def metadataMatch (key : String) (right : Lean.Json) : Lean.Json :=
  comparison (object [("meta", object [("key", string key)])]) right

private def verdict (name : String) : Lean.Json := object [(name, .null)]
private def accept : Lean.Json := verdict "accept"
private def drop : Lean.Json := verdict "drop"

private def block (address : String) (length : Nat) : Lean.Json :=
  object [("prefix", object [("addr", string address), ("len", number length)])]

private def range (first last : Nat) : Lean.Json := object [("range", array [number first, number last])]

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def rejected (json : Lean.Json) : IO Unit := do
  match Snapshot.fromJson json with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"Unsupported nftables input passed: {json.compress}")

private def header (protocol : Protocol) (port : Port) : Header :=
  ⟨167772161, 167772417, protocol, 12000, port⟩

private def positiveTests : IO Unit := do
  let json := snapshot [rule 3 [payload "ip" "saddr" (block "10.0.0.0" 24),
    payload "ip" "daddr" (string "10.0.1.1"), payload "tcp" "sport" (range 1024 65535),
    payload "tcp" "dport" (number 443), accept] [("comment", string "Allow selected HTTPS")]]
  let parsed ← unwrap (Snapshot.parse json.compress)
  ensure (parsed.version == "1.1.3" && parsed.table == "filter" && parsed.chain == "forward")
    "The snapshot must preserve producer and chain identity."
  ensure (parsed.tableIndex == 1 && parsed.chainIndex == 2 && parsed.tableHandle == 1 && parsed.chainHandle == 2)
    "The snapshot must preserve table and chain locations."
  ensure (parsed.rules.length == 1 && parsed.compile.length == 2) "Compilation must append the explicit default."
  let selected ← match parsed.rules with
    | [selected] => pure selected
    | _ => throw (IO.userError "The source rule list changed.")
  ensure (selected.objectIndex == 3 && selected.handle == 3 && selected.verdictIndex == 4 &&
    selected.expressionIndices == [0, 1, 2, 3, 4]) "Rule provenance must preserve every expression index."
  ensure (selected.sourceID == "nftables[3].rule.handle[3]" &&
    selected.comment == some "Allow selected HTTPS") "The source ID and comment must survive import."
  ensure (selected.protocol == some Protocol.tcp) "TCP payload ports must imply the TCP protocol guard."
  ensure (parsed.compile.allows (header Protocol.tcp 443)) "The selected HTTPS packet must pass."
  ensure (!(parsed.compile.allows (header Protocol.udp 443))) "UDP packets must not pass a TCP port match."
  ensure (!(parsed.compile.allows (header Protocol.tcp 80))) "The drop policy must block unmatched ports."
  ensure (!(parsed.compile.allows { header Protocol.tcp 443 with source := 167772673 }))
    "The source prefix must constrain admitted packets."
  let ordering ← unwrap (Snapshot.fromJson (snapshot [rule 3 [payload "tcp" "dport" (number 443), drop],
    rule 4 [payload "tcp" "dport" (range 440 445), accept]]))
  ensure (!(ordering.compile.allows (header Protocol.tcp 443)) && ordering.compile.allows (header Protocol.tcp 444))
    "The first matching rule must decide each packet."
  let allowDefault ← unwrap (Snapshot.fromJson (snapshot [] "accept"))
  ensure (allowDefault.compile.allows (header Protocol.udp 53)) "An explicit accept policy must permit unmatched packets."
  let denyDefault ← unwrap (Snapshot.fromJson (snapshot []))
  ensure (!(denyDefault.compile.allows (header Protocol.udp 53))) "An explicit drop policy must deny unmatched packets."
  let udp ← unwrap (Snapshot.fromJson (snapshot [rule 3 [metadataMatch "l4proto" (number 17),
    payload "udp" "dport" (number 53), accept]]))
  ensure (udp.compile.allows (header Protocol.udp 53) && !(udp.compile.allows (header Protocol.tcp 53)))
    "UDP selectors must preserve the numeric protocol constraint."
  let icmp ← unwrap (Snapshot.fromJson (snapshot [rule 3 [payload "ip" "protocol" (string "icmp"), accept]]))
  ensure (icmp.compile.allows (header Protocol.icmp 0) && !(icmp.compile.allows (header Protocol.tcp 0)))
    "Named IP protocol matches must retain their protocol number."
  for parsed in [parsed, ordering, allowDefault, denyDefault, udp, icmp] do
    for protocol in [Protocol.tcp, Protocol.udp, Protocol.icmp] do
      for port in [0, 53, 80, 440, 443, 444, 445, 65535] do
        let packet := header protocol port
        ensure (parsed.compile.allows packet == parsed.permits packet)
          "Compiled ACL decisions must agree with the source-chain meaning."

private def rejectionTests : IO Unit := do
  for json in [
    object [("nftables", array [metadata "1.1.4", table, chain])],
    object [("nftables", array [metadata "1.1.3" 2, table, chain])],
    object [("nftables", array [metadata, table "inet", chain])],
    object [("nftables", array [metadata, table, chain, table])],
    object [("nftables", array [metadata, table, chain, chain "accept" "input"])],
    object [("nftables", array [metadata, table, chain "drop" "input"])],
    object [("nftables", array [metadata, table "ip" [("flags", array [string "dormant"])], chain])],
    object [("nftables", array [metadata, table, chain "reject"])],
    snapshot [rule 3 [accept] [("position", number 9)]],
    snapshot [rule 3 [accept], rule 3 [drop]],
    snapshot [rule 0 [accept]],
    snapshot [rule 3 []],
    snapshot [rule 3 [payload "tcp" "dport" (number 443)]],
    snapshot [rule 3 [accept, payload "tcp" "dport" (number 443)]],
    snapshot [rule 3 [accept, object [("counter", object [("packets", number 0), ("bytes", number 0)])]]],
    snapshot [rule 3 [object [("accept", .bool true)]]],
    snapshot [rule 3 [object [("accept", .null), ("drop", .null)]]],
    snapshot [rule 3 [object [("jump", object [("target", string "other")])]]],
    snapshot [rule 3 [object [("dnat", object [("addr", string "10.0.1.1")])]]],
    snapshot [rule 3 [metadataMatch "iifname" (string "eth0"), accept]],
    snapshot [rule 3 [comparison (object [("ct", object [("key", string "state")])]) (string "established"), accept]],
    snapshot [rule 3 [comparison (object [("payload", object [("protocol", string "tcp"), ("field", string "dport")])])
      (number 443) "!=", accept]],
    snapshot [rule 3 [payload "tcp" "dport" (number 65536), accept]],
    snapshot [rule 3 [payload "tcp" "dport" (string "https"), accept]],
    snapshot [rule 3 [payload "tcp" "dport" (range 100 10), accept]],
    snapshot [rule 3 [payload "tcp" "dport" (object [("set", array [number 80, number 443])]), accept]],
    snapshot [rule 3 [metadataMatch "l4proto" (string "udp"), payload "tcp" "dport" (number 443), accept]],
    snapshot [rule 3 [payload "ip" "saddr" (block "10.0.0.0" 33), accept]],
    snapshot [rule 3 [payload "ip" "saddr" (string "2001:db8::1"), accept]],
    snapshot [rule 3 [payload "ip" "saddr" (string "10.0.0.1"), payload "ip" "saddr" (block "10.0.0.0" 24), accept]],
    snapshot [rule 3 [payload "tcp" "flags" (number 2), accept]],
    snapshot [rule 3 [comparison (object [("payload", object [("base", string "th"),
      ("offset", number 16), ("len", number 16)])]) (number 443), accept]]
  ] do rejected json
  let json := snapshot [rule 3 [payload "tcp" "dport" (number 65536), accept]]
  match Snapshot.fromJson json with
  | .ok _ => throw (IO.userError "The invalid port must fail.")
  | .error message =>
    ensure ((message.splitOn "nftables[3].rule.handle[3].expr[0]").length > 1)
      "Expression errors must preserve their source location."
  let valid := (snapshot [rule 3 [accept]]).compress
  for key in ["nftables", "\\u006eftables"] do
    let text := "{\"" ++ key ++ "\":[]," ++ (valid.drop 1).toString
    match Snapshot.parse text with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "Duplicate decoded keys must fail before snapshot import.")

example (snapshot : Snapshot) (packet : Header) :
    snapshot.compile.allows packet = snapshot.permits packet := snapshot.compile_allows packet

def run : IO Unit := do
  positiveTests
  rejectionTests
  IO.println "Nftables import tests passed."

end NetlibTest.Nftables
